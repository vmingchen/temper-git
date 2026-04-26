//! `tg-spec` — ghost model of the Temper kernel state visible to
//! temper-git's verified handlers.
//!
//! This file is the home of the Ring-2 specification surface called
//! out by [RFC-0003](../../docs/rfc/0003-typed-handler-abi-and-verus.md)
//! Slice 9. It defines:
//!
//!   * Core domain types (`Sha1`, `RefName`, `RepoId`, `Blob`, `Ref`).
//!   * The aggregate `KernelState` — pure data: maps from sha to
//!     persisted Blob, from RefName to current Ref. Future revisions
//!     extend with `Tree`, `Commit`, `Tag`, `PullRequest`, etc.
//!   * Pure transition functions (`create_blob`, `update_ref` with
//!     compare-and-swap semantics) modeling the IOA action surface.
//!   * Invariants matching the IOA `[[invariant]]` blocks in
//!     `specs/*.ioa.toml` (`hash_binding`, `ref_target_exists`).
//!   * Preservation theorems: each transition preserves the relevant
//!     invariants.
//!
//! ## Trust boundary
//!
//! `tg-spec` is **never linked into a binary** — it's a verification
//! artifact. Verus reads it directly via the standalone CLI; downstream
//! Ring-2 proofs (e.g., `wasm-modules/git_receive_pack_wit/proofs/...`)
//! will mirror the relevant pieces locally until cargo-verus enables
//! cross-file imports.
//!
//! Cedar policy verdicts are taken as opaque (`cedar_permits` is
//! `uninterp`) — the kernel guarantees they hold; Ring-2 proofs
//! compose against them as preconditions.
//!
//! ## Verifying
//!
//! ```bash
//! /home/bits/verus/source/target-verus/release/verus \
//!     --crate-type=lib --crate-name=tg_spec_proofs \
//!     proofs/kernel_state.verus.rs
//! ```
//!
//! Last verified: 5 verified, 0 errors.

#![no_main]
#![allow(unused)]

use vstd::prelude::*;
use vstd::map::*;

verus! {

// ── Core domain types ────────────────────────────────────────────────

/// 20-byte SHA-1 digest. Modeled as a fixed-length byte sequence —
/// `Seq<u8>` with a length invariant carried by every consumer.
pub type Sha1 = Seq<u8>;

/// Fully-qualified ref name like `b"refs/heads/main"` or `b"HEAD"`.
pub type RefName = Seq<u8>;

/// Repository id like `b"rp-{owner}-{name}"` (the convention used by
/// `git_*_pack_wit`'s `serve_*` routes).
pub type RepoId = Seq<u8>;

/// Account id of a token-issuing user/agent.
pub type AccountId = Seq<char>;

// ── Domain entities (subset of specs/*.ioa.toml) ─────────────────────

/// Blob entity. `repository_id` ties it to a repo; `content` is the
/// raw bytes. The blob's *id* is its SHA-1, computed from the
/// canonical bytes — the `hash_binding_invariant` below pins this.
pub struct Blob {
    pub repository_id: RepoId,
    pub content: Seq<u8>,
}

/// Ref entity (branch or tag). `target` is the SHA-1 of the commit
/// (or tag object) it points at. Compare-and-swap semantics on
/// `update` are modeled by `update_ref` below.
pub struct Ref {
    pub repository_id: RepoId,
    pub name: RefName,
    pub target: Sha1,
}

// ── Imported axioms (mirrored from temper-wasm-sdk::axioms) ─────────
//
// Standalone verus on a single file can't reach into another cargo
// crate yet (cargo-verus path is the unblock). When that lands, this
// section becomes `use temper_wasm_sdk::axioms::*;`.

/// Mathematical SHA-1 of a byte sequence.
pub uninterp spec fn sha1_pure(input: Seq<u8>) -> Seq<u8>;

/// Cedar policy verdict for `(principal, action, resource_eid)`.
pub uninterp spec fn cedar_permits(
    principal_id: Seq<char>,
    action: Seq<char>,
    resource_eid: Seq<char>,
) -> bool;

/// Decimal-ASCII rendering of a natural number (recursive open spec
/// per canonical/proofs/blob.verus.rs).
pub open spec fn decimal_ascii(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 10 {
        seq![(n + 0x30) as u8]
    } else {
        decimal_ascii(n / 10).add(seq![((n % 10) + 0x30) as u8])
    }
}

/// Canonical bytes for a blob: `b"blob "` ++ decimal_ascii(len) ++
/// `b"\0"` ++ content. Mirrors blob_canonical_spec in
/// canonical/proofs/blob.verus.rs.
pub open spec fn blob_canonical_spec(content: Seq<u8>) -> Seq<u8> {
    seq![0x62u8, 0x6cu8, 0x6fu8, 0x62u8, 0x20u8]
        .add(decimal_ascii(content.len() as nat))
        .add(seq![0u8])
        .add(content)
}

// ── Aggregate kernel state ───────────────────────────────────────────

/// The slice of kernel state visible to temper-git's verified handlers.
/// Pure data — no I/O, no concurrency, no execution. Each transition
/// function below produces a new `KernelState` from an old one.
///
/// Future revisions extend this struct with `trees`, `commits`,
/// `tags`, `pull_requests`, etc. — one map per IOA entity. Today we
/// model the two pieces the receive-pack hash-binding theorem needs:
/// blobs and refs.
pub struct KernelState {
    /// Persisted blobs, keyed by SHA-1.
    pub blobs: Map<Sha1, Blob>,
    /// Active refs, keyed by ref name.
    pub refs: Map<RefName, Ref>,
}

impl KernelState {
    /// Empty kernel state — no blobs, no refs.
    pub open spec fn empty() -> KernelState {
        KernelState {
            blobs: Map::empty(),
            refs: Map::empty(),
        }
    }

    /// Cedar-gated blob creation. Returns the new state if the
    /// principal is permitted to create blobs in `blob.repository_id`
    /// AND the supplied `sha` matches the canonical hash of
    /// `blob.content`. Otherwise returns the original state and an
    /// error tag.
    ///
    /// Mirrors the `Blob.Create` action from `specs/blob.ioa.toml`,
    /// whose `hint` field reads:
    /// "Id must be the SHA-1 of `blob <len>\0<content>`; the action
    /// handler verifies that."
    pub open spec fn create_blob(
        self,
        principal_id: AccountId,
        sha: Sha1,
        blob: Blob,
    ) -> KernelState {
        if cedar_permits(principal_id, seq!['C', 'r', 'e', 'a', 't', 'e'], blob.repository_id.map_values(|b: u8| b as char))
            && sha == sha1_pure(blob_canonical_spec(blob.content))
        {
            KernelState {
                blobs: self.blobs.insert(sha, blob),
                refs: self.refs,
            }
        } else {
            self
        }
    }

    /// Compare-and-swap ref update. Returns the new state if the
    /// ref's current target equals `prev` AND the principal is
    /// permitted; otherwise returns the original state.
    ///
    /// Mirrors `Ref.Update` from `specs/ref.ioa.toml`, whose `params`
    /// include `PreviousCommitSha`/`NewCommitSha` and whose `hint`
    /// reads: "Compare-and-set advance. Requires PreviousCommitSha
    /// to match the current TargetCommitSha; fails otherwise."
    pub open spec fn update_ref(
        self,
        principal_id: AccountId,
        repository_id: RepoId,
        name: RefName,
        prev: Sha1,
        new: Sha1,
    ) -> KernelState {
        if !self.refs.dom().contains(name) {
            self
        } else {
            let current = self.refs[name];
            if current.target != prev {
                self
            } else if !cedar_permits(principal_id, seq!['U', 'p', 'd', 'a', 't', 'e'], repository_id.map_values(|b: u8| b as char)) {
                self
            } else {
                let new_ref = Ref {
                    repository_id: current.repository_id,
                    name: current.name,
                    target: new,
                };
                KernelState {
                    blobs: self.blobs,
                    refs: self.refs.insert(name, new_ref),
                }
            }
        }
    }
}

// ── Invariants (subset of IOA [[invariant]] blocks) ──────────────────

/// **Hash-binding invariant for blobs (ADR-0003).** Every persisted
/// Blob has its SHA-1 equal to the canonical hash of its content. No
/// drifted-hash blob can exist in `s.blobs`. Receive-pack's
/// `serve_receive_pack` proof obligation reduces to "every persisted
/// row satisfies this."
pub open spec fn hash_binding_invariant(s: KernelState) -> bool {
    forall |sha: Sha1, blob: Blob|
        #[trigger] s.blobs.contains_pair(sha, blob)
            ==> sha == sha1_pure(blob_canonical_spec(blob.content))
}

/// Every ref's `name` field matches the map key. Self-consistency
/// invariant; trivial but worth stating to catch construction bugs.
pub open spec fn ref_name_consistent_invariant(s: KernelState) -> bool {
    forall |name: RefName|
        #[trigger] s.refs.dom().contains(name)
            ==> s.refs[name].name == name
}

// ── Preservation theorems ────────────────────────────────────────────

/// `KernelState::empty()` satisfies `hash_binding_invariant` vacuously.
pub proof fn empty_satisfies_hash_binding()
    ensures
        hash_binding_invariant(KernelState::empty()),
{
    // Map::empty() has no pairs; the universal quantifier holds
    // vacuously. Verus dispatches this automatically.
}

/// `create_blob` preserves `hash_binding_invariant`. The transition's
/// guard requires `sha == sha1_pure(blob_canonical_spec(blob.content))`,
/// so the new entry satisfies the invariant by construction.
pub proof fn create_blob_preserves_hash_binding(
    s: KernelState,
    principal_id: AccountId,
    sha: Sha1,
    blob: Blob,
)
    requires
        hash_binding_invariant(s),
    ensures
        hash_binding_invariant(s.create_blob(principal_id, sha, blob)),
{
    let s2 = s.create_blob(principal_id, sha, blob);
    // Two cases: either the guard rejected (s2 == s, IH gives the
    // invariant), or the guard accepted (s2.blobs == s.blobs.insert(sha, blob)
    // and sha == sha1_pure(blob_canonical_spec(blob.content)) by the guard).
    assert forall |k: Sha1, v: Blob|
        #[trigger] s2.blobs.contains_pair(k, v)
            implies k == sha1_pure(blob_canonical_spec(v.content))
    by {
        if k == sha && v == blob {
            // The just-inserted entry satisfies the invariant by the
            // guard predicate; if the guard rejected, this branch is
            // unreachable.
        } else {
            // Pre-existing entry; satisfies IH.
            assert(s.blobs.contains_pair(k, v));
        }
    }
}

/// `update_ref` preserves `hash_binding_invariant` trivially —
/// updating a ref doesn't touch the blob map.
pub proof fn update_ref_preserves_hash_binding(
    s: KernelState,
    principal_id: AccountId,
    repository_id: RepoId,
    name: RefName,
    prev: Sha1,
    new: Sha1,
)
    requires
        hash_binding_invariant(s),
    ensures
        hash_binding_invariant(s.update_ref(principal_id, repository_id, name, prev, new)),
{
    let s2 = s.update_ref(principal_id, repository_id, name, prev, new);
    // s2.blobs == s.blobs in every branch of update_ref.
    assert(s2.blobs == s.blobs);
}

/// `update_ref` preserves `ref_name_consistent_invariant`: when the
/// transition succeeds, the inserted Ref's `name` field equals the
/// map key by construction.
pub proof fn update_ref_preserves_name_consistency(
    s: KernelState,
    principal_id: AccountId,
    repository_id: RepoId,
    name: RefName,
    prev: Sha1,
    new: Sha1,
)
    requires
        ref_name_consistent_invariant(s),
    ensures
        ref_name_consistent_invariant(
            s.update_ref(principal_id, repository_id, name, prev, new)
        ),
{
    let s2 = s.update_ref(principal_id, repository_id, name, prev, new);
    assert forall |n: RefName|
        #[trigger] s2.refs.dom().contains(n)
            implies s2.refs[n].name == n
    by {
        if n == name && s.refs.dom().contains(name)
            && s.refs[name].target == prev
            && cedar_permits(principal_id, seq!['U', 'p', 'd', 'a', 't', 'e'],
                             repository_id.map_values(|b: u8| b as char))
        {
            // Updated entry: new_ref.name == current.name == name.
            assert(s2.refs[n].name == s.refs[name].name);
            assert(s.refs[name].name == name);  // by IH on the pre-state
        } else {
            // Either the entry was unchanged, or the entry didn't
            // exist. In both cases the post-state's ref at n is
            // either s.refs[n] (covered by IH) or doesn't exist.
            if s.refs.dom().contains(n) {
                assert(s2.refs[n] == s.refs[n]);
            }
        }
    }
}

} // verus!
