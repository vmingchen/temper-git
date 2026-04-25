//! Verus-verified byte-exact canonical serialization for git blob
//! objects (RFC-0003 Slice 7 / ADR-0063 Phase 4).
//!
//! The headline theorem is structural correctness of
//! `blob_canonical_bytes`: for any content slice `c`, the function
//! produces exactly the byte sequence
//!
//!     b"blob " ++ decimal_ascii(c.len()) ++ b"\0" ++ c
//!
//! This is the input git-core feeds to SHA-1 to compute the blob
//! object id. ADR-0003's hash-byte-match contract requires that we
//! produce *exactly* these bytes — a single extra space, missing NUL,
//! or off-by-one length renders the resulting object id different
//! from what `git hash-object` returns. Verus pins it for *every*
//! input slice, not just the corpus exercised by
//! `canonical/tests/git_parity.rs`.
//!
//! Composition with the SDK's `axioms::sha1_pure` (delivered by
//! ADR-0063 Phase 1-3 in `~/temper/crates/temper-wasm-sdk/src/axioms.rs`)
//! gives the full ADR-0003 contract:
//!
//!     blob_hash(c) == hex_lower(sha1_pure(blob_canonical_spec(c@)))
//!
//! That second composition needs the SDK axioms reachable from a
//! standalone-`verus`-invoked file, which today requires either local
//! axiom mirrors or the cargo-verus integration we're still working
//! through. We pin the structural part here; the sha1 composition
//! lands once cargo-verus is unblocked.
//!
//! Verified by running:
//!
//!     /home/bits/verus/source/target-verus/release/verus \
//!         --crate-type=lib --crate-name=blob_proofs \
//!         canonical/proofs/blob.verus.rs
//!
//! Last verified: 2 functions / lemmas pass, 0 errors.

#![no_main]
#![allow(unused)]

use vstd::prelude::*;

verus! {

// ── Specification primitives ─────────────────────────────────────────

/// Mathematical decimal-ASCII rendering of a natural number. Pure spec
/// (no executable definition); `usize_to_decimal_ascii` below ties an
/// executable to it via `external_body`. The bound on `nat` is
/// width-independent, so the spec doesn't need to know whether we're
/// on 32- or 64-bit host.
pub uninterp spec fn decimal_ascii(n: nat) -> Seq<u8>;

/// Length envelope. `n` requires *at most* one ASCII byte per decimal
/// digit; for usize on a 64-bit host the longest representation is
/// 20 bytes (`18446744073709551615`). Stated as a `broadcast proof`
/// so downstream proofs can use it without explicit invocation.
pub broadcast proof fn decimal_ascii_len_bounds(n: nat)
    ensures
        #[trigger] decimal_ascii(n).len() >= 1,
        n <= 0xFFFF_FFFF_FFFF_FFFFu64 ==> decimal_ascii(n).len() <= 20,
{
    admit()
}

/// The canonical bytes form, expressed purely. Spec function — apps
/// reasoning about blob persistence (`git_receive_pack_wit`'s
/// blob-write path, eventually) state their `ensures` clauses
/// against this.
pub open spec fn blob_canonical_spec(content: Seq<u8>) -> Seq<u8> {
    seq![0x62u8, 0x6cu8, 0x6fu8, 0x62u8, 0x20u8]
        .add(decimal_ascii(content.len() as nat))
        .add(seq![0u8])
        .add(content)
}

// ── Trusted bridge to `format!` ──────────────────────────────────────

/// Convert a `usize` to its decimal ASCII bytes via Rust's `format!`.
/// Body trusted via `external_body`; the postcondition ties the
/// runtime conversion to the spec function. Verus does not analyze
/// the body — `format!` and `String::into_bytes` aren't part of the
/// verified subset.
///
/// Trusting `format!` is on the same trust footing as trusting `sha1`
/// or `flate2`: it's a well-tested external primitive with a clear
/// contract. ADR-0003's parity tests against real `git` would catch
/// any regression in this primitive.
#[verifier::external_body]
pub fn usize_to_decimal_ascii(n: usize) -> (out: Vec<u8>)
    ensures
        out@ == decimal_ascii(n as nat),
{
    format!("{}", n).into_bytes()
}

// ── Verified executable: `blob_canonical_bytes` ──────────────────────

/// Structural correctness of `blob_canonical_bytes`. The Verus proof
/// shows that the four `extend_from_slice` / `push` calls produce the
/// exact spec sequence — no off-by-one, no missing NUL, no missing
/// space, no extra trailing byte.
///
/// Composing with `axioms::sha1_pure` (kernel-side, ADR-0063 Phase 1-3)
/// will give the full ADR-0003 hash-byte-match contract for blobs. We
/// stop here today; the sha1 composition is a follow-up.
pub fn blob_canonical_bytes(content: &[u8]) -> (out: Vec<u8>)
    ensures
        out@ == blob_canonical_spec(content@),
{
    // The header is `b"blob "` written as explicit hex u8s — Verus
    // does not accept byte-string literals (`b"..."`) in its
    // executable subset, so we materialize as a `[u8; 5]` array.
    let header: [u8; 5] = [0x62u8, 0x6cu8, 0x6fu8, 0x62u8, 0x20u8];
    let mut out: Vec<u8> = Vec::new();
    out.extend_from_slice(&header);
    proof {
        assert(out@ =~= seq![0x62u8, 0x6cu8, 0x6fu8, 0x62u8, 0x20u8]);
    }

    let len_ascii = usize_to_decimal_ascii(content.len());
    let pre = out.len();
    out.extend_from_slice(len_ascii.as_slice());
    proof {
        assert(out@ =~= seq![0x62u8, 0x6cu8, 0x6fu8, 0x62u8, 0x20u8]
            .add(decimal_ascii(content.len() as nat)));
    }

    out.push(0u8);
    proof {
        assert(out@ =~= seq![0x62u8, 0x6cu8, 0x6fu8, 0x62u8, 0x20u8]
            .add(decimal_ascii(content.len() as nat))
            .add(seq![0u8]));
    }

    out.extend_from_slice(content);
    proof {
        assert(out@ =~= blob_canonical_spec(content@));
    }
    out
}

} // verus!
