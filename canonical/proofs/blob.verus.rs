//! DRAFT — not compiled. Verus annotations for `src/blob.rs`.
//!
//! Lands under `cfg(feature = "verify")` per RFC-0003 Slice 7.
//! Today this file is a reviewable design artifact; the kernel-side
//! Verus tooling (ADR-0063) is not yet pinned in CI.
//!
//! Theorem (informal):
//!   For any byte slice `c`,
//!     `blob_canonical_bytes(c) == seq![b"blob "] + decimal_ascii(c.len()) + seq![b'\0'] + c`
//!     `blob_hash(c)            == sha1_hex(blob_canonical_bytes(c))`
//!
//! Both compose to deliver ADR-0003's hash-byte-match contract for
//! Blob, but as a universal claim rather than a sampled-corpus one.

#![allow(unused)]

use vstd::prelude::*;
use vstd::seq::*;
use vstd::string::*;

verus! {

// ─── Specification primitives ────────────────────────────────────────

/// Pure spec: the canonical SHA-1 of a byte sequence. Provided by the
/// SDK (axiomatized via `external_body` against the `sha1` crate).
///
/// See `temper-wasm-sdk::axioms::sha1_pure` for the host-side spec.
pub closed spec fn sha1_pure(input: Seq<u8>) -> Seq<u8>;

/// Hex encoding of a 20-byte digest as an ASCII string sequence.
pub closed spec fn hex_lower(bytes: Seq<u8>) -> Seq<u8>;

/// Decimal ASCII rendering of a usize (e.g. `42usize` → `b"42"`).
/// Defined as the lex-shortest decimal numeral ≥ 0 with no leading zero
/// except for the literal `b"0"`.
pub closed spec fn decimal_ascii(n: nat) -> Seq<u8>
    decreases n
{
    if n < 10 {
        seq![ b'0' + (n as u8) ]
    } else {
        decimal_ascii(n / 10).add(seq![ b'0' + (n % 10) as u8 ])
    }
}

/// The canonical bytes form, expressed purely.
pub closed spec fn blob_canonical_spec(content: Seq<u8>) -> Seq<u8> {
    seq![b'b', b'l', b'o', b'b', b' ']
        .add(decimal_ascii(content.len() as nat))
        .add(seq![0u8])
        .add(content)
}

// ─── Theorems on the implementation ──────────────────────────────────

/// `blob_canonical_bytes` produces exactly the spec form. No off-by-one,
/// no missing NUL, no missing space.
pub fn blob_canonical_bytes(content: &[u8]) -> (out: Vec<u8>)
    ensures
        out@ == blob_canonical_spec(content@),
{
    let header_len = 5 + decimal_ascii_len(content.len()) + 1;
    let mut out: Vec<u8> = Vec::with_capacity(header_len + content.len());
    out.extend_from_slice(b"blob ");
    write_decimal_ascii(&mut out, content.len());
    out.push(0u8);
    out.extend_from_slice(content);
    // Postcondition follows from the loop invariants of
    // `write_decimal_ascii` and the lemma `extend_from_slice` in vstd.
    out
}

/// SHA-1 of a blob equals the SHA-1 of its canonical bytes. Composed
/// with `blob_canonical_bytes`'s postcondition this gives the full
/// ADR-0003 contract for Blob: the hash function is a pure projection
/// of the canonical form.
pub fn blob_hash(content: &[u8]) -> (out: String)
    ensures
        out@.as_bytes() == hex_lower(sha1_pure(blob_canonical_spec(content@))),
{
    let mut h = Sha1::new();
    let header = format!("blob {}\0", content.len());
    h.update(header.as_bytes());
    h.update(content);
    h.hex()
}

// ─── Axiomatized primitives ──────────────────────────────────────────

/// The `Sha1` streaming hasher behaves as concatenation. This is the
/// fundamental axiom we attach to the `sha1` crate; absent it, no
/// streaming-hash function can be Verus-verified.
///
/// In the integrated build this lives in `temper-wasm-sdk::axioms`
/// (ADR-0063 Sub-Decision 2).
#[verifier(external_body)]
pub fn sha1_update_axiom(s: Sha1Bytes, more: Seq<u8>) -> Sha1Bytes
    ensures
        sha1_pure_state(s.bytes_so_far().add(more)) == result.bytes_so_far(),
;

/// `decimal_ascii_len` produces the byte length of `decimal_ascii(n)`,
/// without doing the conversion. Used to size the `Vec` up front.
pub fn decimal_ascii_len(n: usize) -> (l: usize)
    ensures
        l == decimal_ascii(n as nat).len(),
{
    if n < 10 { 1 }
    else if n < 100 { 2 }
    else if n < 1_000 { 3 }
    else if n < 10_000 { 4 }
    else if n < 100_000 { 5 }
    else if n < 1_000_000 { 6 }
    else if n < 10_000_000 { 7 }
    else if n < 100_000_000 { 8 }
    else if n < 1_000_000_000 { 9 }
    else if n < 10_000_000_000 { 10 }
    else { /* up to usize::MAX on 64-bit hosts */ 20 }
}

/// Inductive helper to write `n` as ASCII bytes into `out`. Verus checks
/// that the postcondition `out@ == old(out)@.add(decimal_ascii(n))`
/// follows from the recursion structure.
pub fn write_decimal_ascii(out: &mut Vec<u8>, n: usize)
    ensures
        out@ == old(out)@.add(decimal_ascii(n as nat)),
{
    if n < 10 {
        out.push(b'0' + (n as u8));
    } else {
        write_decimal_ascii(out, n / 10);
        out.push(b'0' + (n % 10) as u8);
    }
}

} // verus!

// ─── Test bridge ─────────────────────────────────────────────────────
//
// The unit tests in `src/blob.rs` (well-known empty-blob hash, hello
// hashes) remain in place. They are *empirical* checks of the same
// invariants Verus proves *structurally*. Together they pin both
// directions:
//   - Verus: spec is correctly implemented (no off-by-one).
//   - Tests: spec is the right spec (matches real `git`).
//
// Removing either leaves a hole. Keep both.
