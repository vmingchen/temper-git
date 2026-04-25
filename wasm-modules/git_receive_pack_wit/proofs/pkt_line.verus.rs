//! Verus-verified pkt-line length parsing.
//!
//! Mirror of the byte-decoding logic at the heart of `read_command_list`
//! / `split_command_list` in src/lib.rs. The pkt-line wire format
//! frames every payload with a 4-byte ASCII hex header encoding the
//! frame's total byte length. Parsing those four bytes is a pure
//! byte→integer function — a Verus sweet spot.
//!
//! This file is **not** part of the cargo build. It is verified by
//! running:
//!
//!     /home/bits/verus/source/target-verus/release/verus \
//!         --crate-type=lib proofs/pkt_line.verus.rs
//!
//! Last verified: cargo verus pipeline pending toolchain alignment
//! (ADR-0063); the file passes via direct `verus` invocation.

#![no_main]
#![allow(unused)]

use vstd::prelude::*;

verus! {

// ── Specification: ASCII hex digits ─────────────────────────────────

/// Pure spec describing what ASCII byte values count as hex digits.
/// Verus uses this in `ensures` clauses to characterize the *exact*
/// set of bytes the parser accepts.
pub open spec fn is_ascii_hex(b: u8) -> bool {
    (0x30 <= b && b <= 0x39) ||  // '0'..='9'
    (0x61 <= b && b <= 0x66) ||  // 'a'..='f'
    (0x41 <= b && b <= 0x46)     // 'A'..='F'
}

/// Pure spec mapping an ASCII hex digit to its integer value.
/// Defined only when `is_ascii_hex(b)` holds — the executable parser
/// returns `None` for non-hex bytes; the spec uses 0 as a placeholder
/// that doesn't matter when the precondition is violated.
pub open spec fn hex_value(b: u8) -> nat {
    if 0x30 <= b && b <= 0x39 { (b - 0x30) as nat }
    else if 0x61 <= b && b <= 0x66 { (b - 0x57) as nat }
    else if 0x41 <= b && b <= 0x46 { (b - 0x37) as nat }
    else { 0nat }
}

// ── Verified parsing ─────────────────────────────────────────────────

/// Decode one ASCII hex byte to a nibble (0..16). The result aligns
/// with `hex_value` exactly when the byte is a valid hex digit; the
/// `ensures` clause ties the executable code to the spec.
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

/// Decode the 4-byte ASCII pkt-line header into the encoded total
/// frame length. Returns `None` if any byte is not a valid hex digit.
///
/// The postcondition pins the result to the exact arithmetic the
/// pkt-line spec demands: `h0*4096 + h1*256 + h2*16 + h3`. Verus
/// proves this universally — no input can cause the implementation
/// to disagree with the spec.
pub fn parse_pkt_len(hdr: [u8; 4]) -> (out: Option<u16>)
    ensures
        out.is_some() ==
            (is_ascii_hex(hdr[0]) && is_ascii_hex(hdr[1])
             && is_ascii_hex(hdr[2]) && is_ascii_hex(hdr[3])),
        out.is_some() ==> out.unwrap() as nat ==
            hex_value(hdr[0]) * 4096
            + hex_value(hdr[1]) * 256
            + hex_value(hdr[2]) * 16
            + hex_value(hdr[3]),
{
    let n0 = parse_hex_nibble(hdr[0]);
    let n1 = parse_hex_nibble(hdr[1]);
    let n2 = parse_hex_nibble(hdr[2]);
    let n3 = parse_hex_nibble(hdr[3]);
    if n0.is_none() || n1.is_none() || n2.is_none() || n3.is_none() {
        return None;
    }
    let h0 = n0.unwrap() as u16;
    let h1 = n1.unwrap() as u16;
    let h2 = n2.unwrap() as u16;
    let h3 = n3.unwrap() as u16;
    // Each nibble is in 0..16, so the sum fits in u16 (max 0xFFFF).
    Some(h0 * 4096 + h1 * 256 + h2 * 16 + h3)
}

/// The empty-flush pkt-line is the zero-length header `b"0000"`.
/// `is_flush` returns `true` iff the four bytes are exactly that
/// sequence. Useful as a stronger contract than "parse_pkt_len(...) == Some(0)"
/// because it doesn't admit `b"+0+0"` or other quirky encodings.
pub fn is_flush(hdr: [u8; 4]) -> (b: bool)
    ensures
        b == (hdr[0] == 0x30 && hdr[1] == 0x30 && hdr[2] == 0x30 && hdr[3] == 0x30),
{
    hdr[0] == 0x30 && hdr[1] == 0x30 && hdr[2] == 0x30 && hdr[3] == 0x30
}

// ── Sideband framing budget ──────────────────────────────────────────

/// Total bytes a sideband-1-wrapped pkt-line takes for a chunk of
/// `chunk_len` bytes:  4 (pkt-line ASCII-hex header) + 1 (sideband
/// channel byte) + chunk_len. The caller is responsible for splitting
/// inputs into chunks of ≤ 65515 bytes; this function returns `None`
/// when called with an over-long chunk so the caller can't accidentally
/// emit a frame that won't fit in the u16 length header.
///
/// 65515 is the chunk cap our `serve_receive_pack` uses (see the
/// `for chunk in inner.chunks(65515)` loop). Verifying the budget here
/// pins the invariant that the chunk-loop can never overflow the
/// pkt-line header.
pub fn sideband_pkt_total(chunk_len: u16) -> (out: Option<u16>)
    ensures
        out.is_some() == (chunk_len <= 65515),
        out.is_some() ==> out.unwrap() as nat == chunk_len as nat + 5,
{
    if chunk_len > 65515 {
        None
    } else {
        Some(chunk_len + 5)
    }
}

} // verus!
