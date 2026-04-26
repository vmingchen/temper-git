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

/// Mathematical decimal-ASCII rendering of a natural number. Defined
/// recursively: numbers below 10 render to a single ASCII digit byte;
/// larger numbers prepend the rendering of `n / 10` to the digit byte
/// for `n % 10`. `usize_to_decimal_ascii` below ties Rust's `format!`
/// to this spec via `external_body`. The `nat` domain is
/// width-independent, so the spec doesn't need to know whether we're
/// on 32- or 64-bit host.
pub open spec fn decimal_ascii(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 10 {
        seq![(n + 0x30) as u8]
    } else {
        decimal_ascii(n / 10).add(seq![((n % 10) + 0x30) as u8])
    }
}

/// Lower bound: decimal_ascii produces at least one byte for every
/// natural number (including 0, which renders to `b"0"`). **Derived**
/// by induction on `n`, no `admit`. Stated as a `broadcast proof` so
/// downstream proofs can use it without explicit invocation.
pub broadcast proof fn decimal_ascii_len_lb(n: nat)
    ensures
        #[trigger] decimal_ascii(n).len() >= 1,
    decreases n,
{
    if n < 10 {
        // Base: decimal_ascii(n) == seq![digit] of length 1.
    } else {
        // Inductive: decimal_ascii(n) == decimal_ascii(n/10) ++ [digit];
        // the recursive call has length ≥ 1 by IH; concatenating one
        // more byte preserves that.
        decimal_ascii_len_lb(n / 10);
    }
}

// ── Power-of-10 scaffolding for the upper bound ─────────────────────

/// `pow10(k)` = 10^k. Recursive open spec; standard vstd pattern.
pub open spec fn pow10(k: nat) -> nat
    decreases k,
{
    if k == 0 { 1nat }
    else { 10 * pow10((k - 1) as nat) }
}

/// `n / 10 < pow10(k - 1)` whenever `n < pow10(k)` and `k >= 1`.
/// The inductive step the upper-bound lemma needs.
pub proof fn pow10_div_step(n: nat, k: nat)
    requires
        k >= 1,
        n < pow10(k),
    ensures
        n / 10 < pow10((k - 1) as nat),
{
    // pow10(k) == 10 * pow10(k-1) by the open spec definition.
    // n < 10 * pow10(k-1) ==> n/10 < pow10(k-1) by integer division.
    assert(pow10(k) == 10 * pow10((k - 1) as nat));
}

/// Generic upper bound: if `n < pow10(k)`, then the decimal rendering
/// is at most `k` bytes long (with the convention that `pow10(0) = 1`,
/// so `n == 0` requires `k >= 1`, and `decimal_ascii(0)` has length 1).
/// Proof by structural induction on `n` paired with the
/// `pow10_div_step` lemma.
pub proof fn decimal_ascii_len_le_pow10(n: nat, k: nat)
    requires
        k >= 1,
        n < pow10(k),
    ensures
        decimal_ascii(n).len() <= k,
    decreases n,
{
    if n < 10 {
        // length 1, and k >= 1 by precondition
    } else {
        // k >= 2 here: n >= 10 and n < pow10(k) implies pow10(k) > 10,
        // which implies k >= 2 (since pow10(1) == 10).
        assert(pow10(1nat) == 10) by (compute);
        if k == 1 {
            // n < pow10(1) == 10 contradicts n >= 10.
            assert(false);
        }
        // Inductive step: n/10 < pow10(k-1), and (k-1) >= 1.
        pow10_div_step(n, k);
        decimal_ascii_len_le_pow10(n / 10, (k - 1) as nat);
        // length(n) = length(n/10) + 1 <= (k-1) + 1 == k.
    }
}

/// `pow10(20) > u64::MAX`. Concrete arithmetic, dispatched by Z3 with
/// the spec definition unfolded. Bridges the generic
/// `decimal_ascii_len_le_pow10` lemma to the `u64`-specific upper
/// bound below.
pub proof fn pow10_20_gt_u64_max()
    ensures
        pow10(20nat) > 0xFFFF_FFFF_FFFF_FFFFu64 as nat,
{
    // Force Verus to unfold the recursive definition step by step.
    // Each line establishes pow10(k) = 10^k for the next k.
    assert(pow10(0nat) == 1);
    assert(pow10(1nat) == 10);
    assert(pow10(2nat) == 100);
    assert(pow10(3nat) == 1000);
    assert(pow10(4nat) == 10000);
    assert(pow10(5nat) == 100000);
    assert(pow10(6nat) == 1000000);
    assert(pow10(7nat) == 10000000);
    assert(pow10(8nat) == 100000000);
    assert(pow10(9nat) == 1000000000);
    assert(pow10(10nat) == 10000000000);
    assert(pow10(11nat) == 100000000000);
    assert(pow10(12nat) == 1000000000000);
    assert(pow10(13nat) == 10000000000000);
    assert(pow10(14nat) == 100000000000000);
    assert(pow10(15nat) == 1000000000000000);
    assert(pow10(16nat) == 10000000000000000);
    assert(pow10(17nat) == 100000000000000000);
    assert(pow10(18nat) == 1000000000000000000);
    assert(pow10(19nat) == 10000000000000000000);
    assert(pow10(20nat) == 100000000000000000000);
}

/// Upper bound: for any `n` representable as a `u64`, the rendering
/// fits in 20 bytes (longest decimal representation of u64::MAX is
/// `"18446744073709551615"`, 20 chars). **Derived** by composing
/// `decimal_ascii_len_le_pow10` with `pow10_20_gt_u64_max`.
pub broadcast proof fn decimal_ascii_len_ub_u64(n: nat)
    requires
        n <= 0xFFFF_FFFF_FFFF_FFFFu64,
    ensures
        #[trigger] decimal_ascii(n).len() <= 20,
{
    pow10_20_gt_u64_max();
    decimal_ascii_len_le_pow10(n, 20nat);
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
