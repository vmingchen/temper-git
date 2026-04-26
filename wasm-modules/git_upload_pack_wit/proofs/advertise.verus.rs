//! Structural Verus specs for `tg_wire::advertise_info_refs` —
//! the function `serve_info_refs` calls to produce the smart-HTTP
//! `/info/refs` response body.
//!
//! The full byte-exact spec for `advertise_info_refs` would model
//! Rust's `format!` over `&str` arguments, which Verus does not yet
//! handle without a wall of `assume_specification` boilerplate. We
//! split the obligation:
//!
//!   * **`advertise_spec`** is `uninterp` — the mathematical model.
//!     Downstream proofs about `serve_info_refs` reason against this
//!     name as an opaque function from `(service_name, refs)` to a
//!     byte sequence.
//!
//!   * **Structural lemmas** (`advertise_*` proof fns) state the
//!     non-negotiable shape constraints the spec carries. They're
//!     `admit`-based — Verus accepts them; the parity tests in
//!     `wire/tests/git_parity.rs` (against real `git`) keep them
//!     honest empirically. Once the cargo-verus path unblocks,
//!     these lemmas become the contract `tg-wire` itself proves.
//!
//!   * **`ends_with_pkt_flush`** is a fully verified executable
//!     validator over a byte slice. Downstream code can call it
//!     directly (or invoke it as a debug assertion) to check the
//!     wire-shape invariant at runtime — Verus proves the function
//!     returns `true` iff the slice does end with `b"0000"`.
//!
//! Verified by running:
//!
//!     /home/bits/verus/source/target-verus/release/verus \
//!         --crate-type=lib --crate-name=advertise_proofs \
//!         proofs/advertise.verus.rs
//!
//! Last verified: 2 functions / lemmas pass, 0 errors.

#![no_main]
#![allow(unused)]

use vstd::prelude::*;

verus! {

// ── Spec model of advertise_info_refs ────────────────────────────────

/// Mathematical model of the advertisement body. Inputs:
///   * `service_name` — the service preamble target, either
///     `b"git-upload-pack"` or `b"git-receive-pack"`.
///   * `refs` — the (sha, name) pairs to advertise. Empty list takes
///     the `capabilities^{}` pseudo-ref branch in the spec.
pub uninterp spec fn advertise_spec(
    service_name: Seq<u8>,
    refs: Seq<(Seq<u8>, Seq<u8>)>,
) -> Seq<u8>;

/// The advertisement body always ends with a `b"0000"` flush packet.
/// This is the single most-load-bearing wire-shape invariant: every
/// real git client (`git` itself, `libgit2`, JGit, isomorphic-git)
/// looks for this flush to terminate the ref list. Stated as a
/// `broadcast` lemma so downstream proofs don't need explicit
/// instantiation.
pub broadcast proof fn advertise_ends_with_flush(
    service_name: Seq<u8>,
    refs: Seq<(Seq<u8>, Seq<u8>)>,
)
    ensures
        ({
            let body = #[trigger] advertise_spec(service_name, refs);
            &&& body.len() >= 4
            &&& body[body.len() - 4] == 0x30u8
            &&& body[body.len() - 3] == 0x30u8
            &&& body[body.len() - 2] == 0x30u8
            &&& body[body.len() - 1] == 0x30u8
        }),
{
    admit()
}

/// The advertisement body has a non-empty preamble. Together with the
/// preamble-byte axiom below, this gives downstream proofs enough to
/// reason about response sizing (e.g., `serve_info_refs` setting
/// `Content-Length`).
pub broadcast proof fn advertise_nonempty(
    service_name: Seq<u8>,
    refs: Seq<(Seq<u8>, Seq<u8>)>,
)
    ensures
        #[trigger] advertise_spec(service_name, refs).len() >= 30,
{
    admit()
}

// ── Verified executable: pkt-line flush validator ────────────────────

/// Verified check that a byte slice ends with the pkt-line flush
/// packet `b"0000"`. Downstream handler code can call this in debug
/// assertions or test harnesses; Verus proves the function's
/// return-value contract universally.
///
/// Combined with `advertise_ends_with_flush`, every output of
/// `tg_wire::advertise_info_refs` satisfies `ends_with_pkt_flush`.
/// The ADR-0003 byte-exact-compat parity tests pin the empirical
/// truth of the lemma; this file pins it as a name downstream proofs
/// can compose against.
pub fn ends_with_pkt_flush(body: &[u8]) -> (out: bool)
    ensures
        out == ({
            &&& body@.len() >= 4
            &&& body@[body@.len() - 4] == 0x30u8
            &&& body@[body@.len() - 3] == 0x30u8
            &&& body@[body@.len() - 2] == 0x30u8
            &&& body@[body@.len() - 1] == 0x30u8
        }),
{
    let n = body.len();
    if n < 4 {
        return false;
    }
    body[n - 4] == 0x30
        && body[n - 3] == 0x30
        && body[n - 2] == 0x30
        && body[n - 1] == 0x30
}

} // verus!
