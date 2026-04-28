//! Verus-verified `split_command_list` — finds the pkt-line flush
//! ending a receive-pack command list.
//!
//! `serve_receive_pack` (src/lib.rs:151) calls a function with the
//! same shape over the inbound body bytes: walk pkt-line frames
//! parsing each 4-byte ASCII hex header as a length, advance by that
//! length, until reaching a `b"0000"` flush. The byte right after the
//! flush is where the pack data begins.
//!
//! The verified contract here is intentionally weaker than "the input
//! is a well-formed pkt-line stream": we prove that **whenever the
//! function returns `Some(j)`, bytes `[j-4..j]` of the input are
//! exactly `b"0000"`**. That's the wire-protocol-relevant property —
//! the position the caller hands to the pack parser is guaranteed to
//! sit right after a flush, not in the middle of an arbitrary frame.
//!
//! Verifying full-stream well-formedness (that every frame between
//! offset 0 and `j-4` parsed as a valid pkt-line and consumed its
//! declared length) requires a recursive spec function tracking the
//! "frame-aligned prefix" predicate. Tractable, but ~3× the LoC for
//! marginal additional value over the contract here. Deferred.
//!
//! Verified by:
//!     verus --crate-type=lib --crate-name=split_command_list_proofs \
//!         proofs/split_command_list.verus.rs
//!
//! Last verified: 3 verified, 0 errors.

#![no_main]
#![allow(unused)]

use vstd::prelude::*;

verus! {

// ── Local mirrors (until cargo-verus enables cross-file imports) ────

pub open spec fn is_ascii_hex(b: u8) -> bool {
    (0x30 <= b && b <= 0x39) || (0x61 <= b && b <= 0x66) || (0x41 <= b && b <= 0x46)
}

pub open spec fn hex_value(b: u8) -> nat {
    if 0x30 <= b && b <= 0x39 { (b - 0x30) as nat }
    else if 0x61 <= b && b <= 0x66 { (b - 0x57) as nat }
    else if 0x41 <= b && b <= 0x46 { (b - 0x37) as nat }
    else { 0nat }
}

pub fn parse_hex_nibble(b: u8) -> (out: Option<u8>)
    ensures
        out.is_some() == is_ascii_hex(b),
        out.is_some() ==> out.unwrap() < 16,
        out.is_some() ==> out.unwrap() as nat == hex_value(b),
{
    if b >= 0x30 && b <= 0x39 { Some(b - 0x30) }
    else if b >= 0x61 && b <= 0x66 { Some(b - 0x57) }
    else if b >= 0x41 && b <= 0x46 { Some(b - 0x37) }
    else { None }
}

// ── Verified: split_command_list ─────────────────────────────────────

/// Walk pkt-line frames of `body` until reaching a `b"0000"` flush.
/// On success returns the offset of the byte *immediately after* the
/// flush — the caller hands `&body[..j]` to the command-list parser
/// and `&body[j..]` to the pack parser.
///
/// Postcondition: the four bytes ending at offset `j` are exactly
/// `b"0000"`. **Universal** — every input that reaches a return
/// satisfies this; no escape via mid-frame matching of `b"0000"`
/// (the loop only checks the boundary at frame-aligned offsets).
pub fn split_command_list(body: &[u8]) -> (out: Option<usize>)
    ensures
        out.is_some() ==> {
            let j = out.unwrap() as int;
            &&& 4 <= j
            &&& j <= body@.len()
            &&& body@[j - 4] == 0x30u8
            &&& body@[j - 3] == 0x30u8
            &&& body@[j - 2] == 0x30u8
            &&& body@[j - 1] == 0x30u8
        },
{
    let n = body.len();
    let mut i: usize = 0;
    // Use n - i ≥ 4 instead of i + 4 ≤ n to avoid usize-overflow
    // worries on the addition. Equivalent on bounded i ≤ n.
    while i <= n && n - i >= 4
        invariant
            i <= n,
            n == body.len(),
        decreases n - i,
    {
        // Check for the pkt-line flush b"0000".
        if body[i] == 0x30u8
            && body[i + 1] == 0x30u8
            && body[i + 2] == 0x30u8
            && body[i + 3] == 0x30u8
        {
            return Some(i + 4);
        }

        // Otherwise parse the 4-byte ASCII hex length and advance.
        let h0 = parse_hex_nibble(body[i]);
        let h1 = parse_hex_nibble(body[i + 1]);
        let h2 = parse_hex_nibble(body[i + 2]);
        let h3 = parse_hex_nibble(body[i + 3]);
        if h0.is_none() || h1.is_none() || h2.is_none() || h3.is_none() {
            return None;
        }
        let pkt_len: usize = (h0.unwrap() as usize) * 4096
            + (h1.unwrap() as usize) * 256
            + (h2.unwrap() as usize) * 16
            + (h3.unwrap() as usize);

        // pkt_len < 4 is malformed (header itself takes 4 bytes).
        if pkt_len < 4 {
            return None;
        }
        // Don't walk past the buffer.
        if pkt_len > n - i {
            return None;
        }
        // Advance past this frame.
        i = i + pkt_len;
    }
    None
}

/// Convenience splitter: when `split_command_list` returns `Some(j)`,
/// `commands_and_pack(body, j)` gives back `(commands, pack)` with
/// the contracted shape — `commands` ends at the flush, `pack` is
/// everything after. Pure spec; no executable.
pub open spec fn commands_and_pack(body: Seq<u8>, j: int) -> (Seq<u8>, Seq<u8>) {
    (body.subrange(0, j), body.subrange(j, body.len() as int))
}

/// Concatenation lemma: the spec splitter's output reconstructs the
/// input. Useful for downstream proofs that want to reason about the
/// pre-flush + post-flush bytes as separate streams.
pub proof fn commands_and_pack_concat(body: Seq<u8>, j: int)
    requires
        0 <= j <= body.len(),
    ensures
        commands_and_pack(body, j).0.add(commands_and_pack(body, j).1) == body,
{
    let (l, r) = commands_and_pack(body, j);
    assert(l.add(r) =~= body);
}

} // verus!
