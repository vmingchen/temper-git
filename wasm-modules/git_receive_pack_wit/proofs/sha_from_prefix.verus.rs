//! Verus-verified `sha_from_prefix` — the heart of ADR-0003 for the
//! push side. Every Blob/Tree/Commit/Tag persisted by
//! `serve_receive_pack` flows through this function; the postcondition
//! pins the SHA-1 binding universally.
//!
//! Real implementation in `wasm-modules/git_receive_pack_wit/src/lib.rs:243`
//! (and `wasm-modules/git_receive_pack/src/lib.rs:484` for the legacy
//! module):
//!
//! ```rust
//! fn sha_from_prefix(prefix: &str, body: &[u8]) -> String {
//!     let header = format!("{} {}\0", prefix, body.len());
//!     let mut hasher = tg_canonical::Sha1::new();
//!     hasher.update(header.as_bytes());
//!     hasher.update(body);
//!     hasher.hex()
//! }
//! ```
//!
//! For each object kind, `prefix` is one of: `b"blob"`, `b"tree"`,
//! `b"commit"`, `b"tag"`. The ADR-0003 contract demands the result
//! equal `git hash-object`'s SHA-1 over the canonical bytes, which
//! by definition are `prefix ++ b" " ++ decimal_ascii(body.len()) ++
//! b"\0" ++ body`. The proof here ties the streaming-hasher
//! composition to `sha1_pure` of that exact canonical sequence —
//! universally, for every prefix/body pair, no admit.
//!
//! Verified by running:
//!
//!     /home/bits/verus/source/target-verus/release/verus \
//!         --crate-type=lib --crate-name=sha_from_prefix_proofs \
//!         proofs/sha_from_prefix.verus.rs
//!
//! Last verified: 2 verified items, 0 errors.

#![no_main]
#![allow(unused)]

use vstd::prelude::*;

verus! {

// ── Decimal ASCII (mirror from canonical/proofs/blob.verus.rs) ──────
//
// Standalone-`verus` invocation cannot import across files today
// (cargo-verus path is the unblock). Once cross-file imports work,
// this mirror collapses into a `--import canonical_proofs=...` flag
// at invocation time.

pub open spec fn decimal_ascii(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 10 {
        seq![(n + 0x30) as u8]
    } else {
        decimal_ascii(n / 10).add(seq![((n % 10) + 0x30) as u8])
    }
}

#[verifier::external_body]
pub fn usize_to_decimal_ascii(n: usize) -> (out: Vec<u8>)
    ensures
        out@ == decimal_ascii(n as nat),
{
    format!("{}", n).into_bytes()
}

// ── SHA-1 streaming (mirror from temper-wasm-sdk::axioms) ───────────

pub uninterp spec fn sha1_pure(input: Seq<u8>) -> Seq<u8>;

pub struct Sha1State;

impl Sha1State {
    pub uninterp spec fn bytes_so_far(self) -> Seq<u8>;

    #[verifier::external_body]
    pub fn new() -> (out: Self)
        ensures
            out.bytes_so_far() == Seq::<u8>::empty(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn update(&mut self, data: &[u8])
        ensures
            self.bytes_so_far() == old(self).bytes_so_far().add(data@),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn digest(self) -> (out: [u8; 20])
        ensures
            out@ == sha1_pure(self.bytes_so_far()),
    {
        unimplemented!()
    }
}

// ── Generic git-object canonical bytes ──────────────────────────────

/// The canonical byte sequence git-core feeds to SHA-1 for *any*
/// object kind: `<prefix>` ++ `b" "` ++ decimal_ascii(body.len()) ++
/// `b"\0"` ++ body. Specializes:
///   * `prefix = b"blob"`   ⇒ blob canonical bytes
///   * `prefix = b"tree"`   ⇒ tree canonical bytes
///   * `prefix = b"commit"` ⇒ commit canonical bytes
///   * `prefix = b"tag"`    ⇒ tag canonical bytes
pub open spec fn canonical_with_prefix(prefix: Seq<u8>, body: Seq<u8>) -> Seq<u8> {
    prefix
        .add(seq![0x20u8])              // ASCII space
        .add(decimal_ascii(body.len() as nat))
        .add(seq![0u8])                  // NUL separator
        .add(body)
}

// ── Verified: sha_from_prefix ────────────────────────────────────────

/// **Headline ADR-0003 theorem for receive-pack.**
///
/// Every object the receive-pack handler persists has its SHA-1
/// computed via this function. Verified to match the canonical
/// byte sequence universally — for every prefix and body, every
/// permissible length, every byte content. Real `git hash-object`
/// produces the same byte-for-byte digest because the canonical
/// form is a fixed wire convention.
///
/// Implementation builds the header (`<prefix> <len>\0`) once, then
/// streams it plus the body through the hasher. Verus tracks
/// `bytes_so_far` through both `update` calls and shows the
/// concatenation matches `canonical_with_prefix(prefix@, body@)` at
/// the moment `digest()` is called.
pub fn sha_from_prefix(prefix: &[u8], body: &[u8]) -> (out: [u8; 20])
    ensures
        out@ == sha1_pure(canonical_with_prefix(prefix@, body@)),
{
    // Header: prefix ++ b" " ++ decimal_ascii(body.len()) ++ b"\0".
    let mut header: Vec<u8> = Vec::new();
    header.extend_from_slice(prefix);
    header.push(0x20u8);                 // space
    let len_ascii = usize_to_decimal_ascii(body.len());
    header.extend_from_slice(len_ascii.as_slice());
    header.push(0u8);                    // NUL
    proof {
        assert(header@ =~= prefix@
            .add(seq![0x20u8])
            .add(decimal_ascii(body.len() as nat))
            .add(seq![0u8]));
    }

    let mut h = Sha1State::new();
    proof {
        assert(h.bytes_so_far() == Seq::<u8>::empty());
    }

    h.update(header.as_slice());
    proof {
        assert(h.bytes_so_far() =~= header@);
    }

    h.update(body);
    proof {
        // bytes_so_far == header ++ body
        //              == prefix ++ b" " ++ decimal_ascii(body.len()) ++ b"\0" ++ body
        //              == canonical_with_prefix(prefix@, body@)
        assert(h.bytes_so_far() =~= header@.add(body@));
        assert(canonical_with_prefix(prefix@, body@) =~=
            prefix@
                .add(seq![0x20u8])
                .add(decimal_ascii(body.len() as nat))
                .add(seq![0u8])
                .add(body@));
        assert(h.bytes_so_far() =~= canonical_with_prefix(prefix@, body@));
    }

    h.digest()
}

// ── Specialization lemmas for each object kind ──────────────────────
//
// `sha_from_prefix` is parameterized over `prefix`; downstream
// reasoning specializes to one of four byte-string literals. We
// don't need separate verified functions for blob/tree/commit/tag
// hashing — `sha_from_prefix(b"blob", body)`, `sha_from_prefix(b"tree", body)`,
// etc. are the per-kind hash functions, with their canonical-bytes
// contracts derived directly from `canonical_with_prefix` specialized.
//
// As helpers, we expose the four prefix byte sequences as spec
// constants so handler code can name them without re-spelling the
// hex u8s. Verus open spec definitions; downstream proofs use them
// in `ensures` clauses.

pub open spec fn blob_prefix() -> Seq<u8>   { seq![0x62u8, 0x6cu8, 0x6fu8, 0x62u8] }                                 // "blob"
pub open spec fn tree_prefix() -> Seq<u8>   { seq![0x74u8, 0x72u8, 0x65u8, 0x65u8] }                                 // "tree"
pub open spec fn commit_prefix() -> Seq<u8> { seq![0x63u8, 0x6fu8, 0x6du8, 0x6du8, 0x69u8, 0x74u8] }                 // "commit"
pub open spec fn tag_prefix() -> Seq<u8>    { seq![0x74u8, 0x61u8, 0x67u8] }                                         // "tag"

} // verus!
