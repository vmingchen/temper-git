//! Per-kind canonical hash theorems for tree, commit, tag.
//!
//! Composes the streaming-hash axiom (`Sha1State::digest()`'s
//! postcondition tying it to `sha1_pure(bytes_so_far)`) with the
//! generic prefix-hash form `canonical_with_prefix(prefix, body)`
//! to give per-kind ADR-0003 contracts:
//!
//!   tree_hash(t)   == sha1_pure(tree_canonical_spec(t))
//!   commit_hash(c) == sha1_pure(commit_canonical_spec(c))
//!   tag_hash(g)    == sha1_pure(tag_canonical_spec(g))
//!
//! Each per-kind `canonical_spec` stays `uninterp` here — modeling
//! tree/commit/tag canonical bytes byte-for-byte requires the
//! `format!`-on-`&str` scaffolding that lives in Tier 4 of the
//! verification roadmap. The theorems here pin the **structural
//! contract**: each kind's hash is `sha1_pure` of *its* canonical
//! spec, with the spec function as the named contract surface.
//! Downstream Ring-2 proofs (e.g., receive-pack's hash-binding
//! invariant for trees) reason against these names.
//!
//! The bridging axiom — that the body-buffer the hash function
//! receives equals `*_canonical_body(input)` — is admitted per kind.
//! Once the canonical-body builders enter the verified ring (Tier
//! 4), the admits collapse into derivations.
//!
//! Verified by:
//!     verus --crate-type=lib --crate-name=object_hashes_proofs \
//!         proofs/object_hashes.verus.rs
//!
//! Last verified: 6 verified, 0 errors.

#![no_main]
#![allow(unused)]

use vstd::prelude::*;

verus! {

// ── SHA-1 axioms (mirror from temper-wasm-sdk::axioms) ──────────────

pub uninterp spec fn sha1_pure(input: Seq<u8>) -> Seq<u8>;

// ── canonical_with_prefix (mirror from sha_from_prefix.verus.rs) ────

pub open spec fn decimal_ascii(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 10 {
        seq![(n + 0x30) as u8]
    } else {
        decimal_ascii(n / 10).add(seq![((n % 10) + 0x30) as u8])
    }
}

pub open spec fn canonical_with_prefix(prefix: Seq<u8>, body: Seq<u8>) -> Seq<u8> {
    prefix
        .add(seq![0x20u8])
        .add(decimal_ascii(body.len() as nat))
        .add(seq![0u8])
        .add(body)
}

// ── Per-kind prefixes (concrete byte sequences) ─────────────────────

pub open spec fn tree_prefix() -> Seq<u8> {
    seq![0x74u8, 0x72u8, 0x65u8, 0x65u8]               // "tree"
}

pub open spec fn commit_prefix() -> Seq<u8> {
    seq![0x63u8, 0x6fu8, 0x6du8, 0x6du8, 0x69u8, 0x74u8] // "commit"
}

pub open spec fn tag_prefix() -> Seq<u8> {
    seq![0x74u8, 0x61u8, 0x67u8]                        // "tag"
}

// ── Per-kind input types (opaque ghost data) ────────────────────────

/// Logical tree input — sorted entries, each with mode/name/sha20.
/// The exact field layout is opaque at this layer; downstream proofs
/// either model it concretely (Tier 4) or treat it as an opaque
/// identifier the canonical_body axiom maps to bytes.
pub struct TreeData;

/// Logical commit input — tree sha + parents + author/committer/
/// message. Opaque per the same rationale as `TreeData`.
pub struct CommitData;

/// Logical tag input — object/type/name/tagger/message. Opaque.
pub struct TagData;

// ── Body-byte spec functions (uninterp; bridge by axiom) ────────────

/// The bytes git-core feeds to SHA-1 *after* the `<kind> <len>\0`
/// header for a tree object. `uninterp` here; concrete definition
/// requires modeling sorted-entry concatenation with octal-mode
/// rendering and binary SHA-20 — Tier 4 work.
pub uninterp spec fn tree_canonical_body(t: TreeData) -> Seq<u8>;

/// The bytes git-core feeds to SHA-1 after the `commit <len>\0`
/// header. `uninterp`; concrete form is multi-line headers with
/// variable-count parents.
pub uninterp spec fn commit_canonical_body(c: CommitData) -> Seq<u8>;

/// The bytes git-core feeds to SHA-1 after the `tag <len>\0` header.
/// `uninterp`; concrete form is 5-line header + blank + message.
pub uninterp spec fn tag_canonical_body(g: TagData) -> Seq<u8>;

// ── Per-kind canonical specs (the named ADR-0003 contracts) ─────────

pub open spec fn tree_canonical_spec(t: TreeData) -> Seq<u8> {
    canonical_with_prefix(tree_prefix(), tree_canonical_body(t))
}

pub open spec fn commit_canonical_spec(c: CommitData) -> Seq<u8> {
    canonical_with_prefix(commit_prefix(), commit_canonical_body(c))
}

pub open spec fn tag_canonical_spec(g: TagData) -> Seq<u8> {
    canonical_with_prefix(tag_prefix(), tag_canonical_body(g))
}

// ── sha_from_prefix-style axiom (mirrors the verified function) ─────

/// Mirrors the postcondition of
/// `wasm-modules/git_receive_pack_wit/proofs/sha_from_prefix.verus.rs`.
/// Once cargo-verus enables cross-file imports this becomes a `use`
/// of the verified function; until then we declare the axiom.
#[verifier::external_body]
pub fn sha_from_prefix(prefix: &[u8], body: &[u8]) -> (out: [u8; 20])
    ensures
        out@ == sha1_pure(canonical_with_prefix(prefix@, body@)),
{
    unimplemented!()
}

// ── Trusted bridge: byte-buffer ↔ canonical body ────────────────────
//
// The `external_body` axioms below state that the byte buffer the
// hash function receives, when produced by `tg-canonical::tree_canonical_bytes`
// (resp. commit/tag), equals the spec body. Their executable bodies
// would call `tg_canonical::*_canonical_bytes`; today they're
// `unimplemented!()` placeholders Verus skips.
//
// Tier 4 replaces these with concrete spec definitions and verified
// builders, derived from a `format!`-modeling axiom set. Until then
// the axiom names give downstream proofs a stable contract.

#[verifier::external_body]
pub fn tree_canonical_bytes(t: TreeData) -> (out: Vec<u8>)
    ensures
        out@ == tree_canonical_body(t),
{
    unimplemented!()
}

#[verifier::external_body]
pub fn commit_canonical_bytes(c: CommitData) -> (out: Vec<u8>)
    ensures
        out@ == commit_canonical_body(c),
{
    unimplemented!()
}

#[verifier::external_body]
pub fn tag_canonical_bytes(g: TagData) -> (out: Vec<u8>)
    ensures
        out@ == tag_canonical_body(g),
{
    unimplemented!()
}

// ── Per-kind hash theorems (the ADR-0003 contracts) ─────────────────

/// **ADR-0003 hash-byte-match for trees.** Proven by composition of
/// the canonical-bytes builder (axiom-bridged) and the streaming
/// hash function. Universally — for every TreeData input, no admit.
pub fn tree_hash(t: TreeData) -> (out: [u8; 20])
    ensures
        out@ == sha1_pure(tree_canonical_spec(t)),
{
    let body = tree_canonical_bytes(t);
    let prefix: [u8; 4] = [0x74u8, 0x72u8, 0x65u8, 0x65u8];
    let h = sha_from_prefix(&prefix, body.as_slice());
    proof {
        // sha_from_prefix gives sha1_pure(canonical_with_prefix(prefix@, body@))
        // body@ == tree_canonical_body(t) by canonical_bytes axiom
        // tree_canonical_spec(t) == canonical_with_prefix(tree_prefix(), tree_canonical_body(t))
        //                        == canonical_with_prefix(prefix@, body@)
        assert(prefix@ =~= tree_prefix());
        assert(body@ =~= tree_canonical_body(t));
        assert(canonical_with_prefix(prefix@, body@) =~= tree_canonical_spec(t));
    }
    h
}

/// **ADR-0003 hash-byte-match for commits.** Same composition as
/// `tree_hash`, with the `commit` prefix.
pub fn commit_hash(c: CommitData) -> (out: [u8; 20])
    ensures
        out@ == sha1_pure(commit_canonical_spec(c)),
{
    let body = commit_canonical_bytes(c);
    let prefix: [u8; 6] = [0x63u8, 0x6fu8, 0x6du8, 0x6du8, 0x69u8, 0x74u8];
    let h = sha_from_prefix(&prefix, body.as_slice());
    proof {
        assert(prefix@ =~= commit_prefix());
        assert(body@ =~= commit_canonical_body(c));
        assert(canonical_with_prefix(prefix@, body@) =~= commit_canonical_spec(c));
    }
    h
}

/// **ADR-0003 hash-byte-match for tags.** Same composition with
/// the `tag` prefix.
pub fn tag_hash(g: TagData) -> (out: [u8; 20])
    ensures
        out@ == sha1_pure(tag_canonical_spec(g)),
{
    let body = tag_canonical_bytes(g);
    let prefix: [u8; 3] = [0x74u8, 0x61u8, 0x67u8];
    let h = sha_from_prefix(&prefix, body.as_slice());
    proof {
        assert(prefix@ =~= tag_prefix());
        assert(body@ =~= tag_canonical_body(g));
        assert(canonical_with_prefix(prefix@, body@) =~= tag_canonical_spec(g));
    }
    h
}

} // verus!
