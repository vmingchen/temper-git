//! Ring-2 hash-binding theorem: extends `KernelState` to cover
//! tree/commit/tag persistence and proves the universal ADR-0003
//! contract — every persisted object across *all four* kinds has
//! its SHA-1 equal to the canonical hash of its content.
//!
//! Composes with:
//!   * `kernel_state.verus.rs` — Blob persistence + create_blob
//!     transition + hash_binding_invariant for blobs.
//!   * `canonical/proofs/object_hashes.verus.rs` —
//!     `tree_hash`, `commit_hash`, `tag_hash` postconditions.
//!
//! What this file adds:
//!   * Tree, Commit, Tag entity types in the ghost model.
//!   * `KernelState`'s map fields extended to cover all four kinds
//!     (modeled as a *parallel* extension; the original `KernelState`
//!     in kernel_state.verus.rs stays focused on blobs+refs for
//!     introductory readability).
//!   * `create_tree`, `create_commit`, `create_tag` transitions —
//!     each Cedar-gated and hash-precondition-gated, mirroring
//!     `create_blob`.
//!   * `hash_binding_full_invariant` — the conjunction across all
//!     four object kinds.
//!   * Preservation theorems: each `create_*` transition preserves
//!     `hash_binding_full_invariant`.
//!
//! Together these give Ring-2 receive-pack the ability to prove,
//! universally, "every Blob/Tree/Commit/Tag persisted by
//! `serve_receive_pack` has matching SHA-1." The handler-side
//! glue — calling create_* with hash from sha_from_prefix —
//! lands in Tier 5 (cross-file lemma reuse) once cargo-verus
//! enables direct composition.
//!
//! Verified by:
//!     verus --crate-type=lib --crate-name=object_persistence_proofs \
//!         proofs/object_persistence.verus.rs
//!
//! Last verified: 9 verified, 0 errors.

#![no_main]
#![allow(unused)]

use vstd::prelude::*;
use vstd::map::*;

verus! {

// ── Domain types ────────────────────────────────────────────────────

pub type Sha1 = Seq<u8>;
pub type RepoId = Seq<u8>;
pub type AccountId = Seq<char>;

pub struct Blob {
    pub repository_id: RepoId,
    pub content: Seq<u8>,
}

/// Logical tree input. Opaque per object_hashes.verus.rs: concrete
/// fields modeled in Tier 4.
pub struct TreeData;

/// Logical commit input. Opaque.
pub struct CommitData;

/// Logical tag input. Opaque.
pub struct TagData;

// ── Imported axioms ──────────────────────────────────────────────────

pub uninterp spec fn sha1_pure(input: Seq<u8>) -> Seq<u8>;

pub uninterp spec fn cedar_permits(
    principal_id: AccountId,
    action: Seq<char>,
    resource_eid: Seq<char>,
) -> bool;

pub open spec fn decimal_ascii(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 10 {
        seq![(n + 0x30) as u8]
    } else {
        decimal_ascii(n / 10).add(seq![((n % 10) + 0x30) as u8])
    }
}

pub open spec fn blob_canonical_spec(content: Seq<u8>) -> Seq<u8> {
    seq![0x62u8, 0x6cu8, 0x6fu8, 0x62u8, 0x20u8]
        .add(decimal_ascii(content.len() as nat))
        .add(seq![0u8])
        .add(content)
}

pub open spec fn canonical_with_prefix(prefix: Seq<u8>, body: Seq<u8>) -> Seq<u8> {
    prefix
        .add(seq![0x20u8])
        .add(decimal_ascii(body.len() as nat))
        .add(seq![0u8])
        .add(body)
}

pub uninterp spec fn tree_canonical_body(t: TreeData) -> Seq<u8>;
pub uninterp spec fn commit_canonical_body(c: CommitData) -> Seq<u8>;
pub uninterp spec fn tag_canonical_body(g: TagData) -> Seq<u8>;

pub open spec fn tree_canonical_spec(t: TreeData) -> Seq<u8> {
    canonical_with_prefix(seq![0x74u8, 0x72u8, 0x65u8, 0x65u8], tree_canonical_body(t))
}
pub open spec fn commit_canonical_spec(c: CommitData) -> Seq<u8> {
    canonical_with_prefix(
        seq![0x63u8, 0x6fu8, 0x6du8, 0x6du8, 0x69u8, 0x74u8],
        commit_canonical_body(c),
    )
}
pub open spec fn tag_canonical_spec(g: TagData) -> Seq<u8> {
    canonical_with_prefix(seq![0x74u8, 0x61u8, 0x67u8], tag_canonical_body(g))
}

// ── Aggregate state covering all four object kinds ──────────────────

pub struct ObjectStorage {
    pub blobs: Map<Sha1, Blob>,
    pub trees: Map<Sha1, TreeData>,
    pub commits: Map<Sha1, CommitData>,
    pub tags: Map<Sha1, TagData>,
}

impl ObjectStorage {
    pub open spec fn empty() -> ObjectStorage {
        ObjectStorage {
            blobs: Map::empty(),
            trees: Map::empty(),
            commits: Map::empty(),
            tags: Map::empty(),
        }
    }

    pub open spec fn create_blob(
        self,
        principal_id: AccountId,
        repository_id: RepoId,
        sha: Sha1,
        blob: Blob,
    ) -> ObjectStorage {
        if cedar_permits(
            principal_id,
            seq!['C', 'r', 'e', 'a', 't', 'e'],
            repository_id.map_values(|b: u8| b as char),
        ) && sha == sha1_pure(blob_canonical_spec(blob.content))
        {
            ObjectStorage { blobs: self.blobs.insert(sha, blob), ..self }
        } else {
            self
        }
    }

    pub open spec fn create_tree(
        self,
        principal_id: AccountId,
        repository_id: RepoId,
        sha: Sha1,
        tree: TreeData,
    ) -> ObjectStorage {
        if cedar_permits(
            principal_id,
            seq!['C', 'r', 'e', 'a', 't', 'e'],
            repository_id.map_values(|b: u8| b as char),
        ) && sha == sha1_pure(tree_canonical_spec(tree))
        {
            ObjectStorage { trees: self.trees.insert(sha, tree), ..self }
        } else {
            self
        }
    }

    pub open spec fn create_commit(
        self,
        principal_id: AccountId,
        repository_id: RepoId,
        sha: Sha1,
        commit: CommitData,
    ) -> ObjectStorage {
        if cedar_permits(
            principal_id,
            seq!['C', 'r', 'e', 'a', 't', 'e'],
            repository_id.map_values(|b: u8| b as char),
        ) && sha == sha1_pure(commit_canonical_spec(commit))
        {
            ObjectStorage { commits: self.commits.insert(sha, commit), ..self }
        } else {
            self
        }
    }

    pub open spec fn create_tag(
        self,
        principal_id: AccountId,
        repository_id: RepoId,
        sha: Sha1,
        tag: TagData,
    ) -> ObjectStorage {
        if cedar_permits(
            principal_id,
            seq!['C', 'r', 'e', 'a', 't', 'e'],
            repository_id.map_values(|b: u8| b as char),
        ) && sha == sha1_pure(tag_canonical_spec(tag))
        {
            ObjectStorage { tags: self.tags.insert(sha, tag), ..self }
        } else {
            self
        }
    }
}

// ── Hash-binding invariant across all four kinds ────────────────────

pub open spec fn hash_binding_blobs(s: ObjectStorage) -> bool {
    forall |sha: Sha1, b: Blob|
        #[trigger] s.blobs.contains_pair(sha, b)
            ==> sha == sha1_pure(blob_canonical_spec(b.content))
}

pub open spec fn hash_binding_trees(s: ObjectStorage) -> bool {
    forall |sha: Sha1, t: TreeData|
        #[trigger] s.trees.contains_pair(sha, t)
            ==> sha == sha1_pure(tree_canonical_spec(t))
}

pub open spec fn hash_binding_commits(s: ObjectStorage) -> bool {
    forall |sha: Sha1, c: CommitData|
        #[trigger] s.commits.contains_pair(sha, c)
            ==> sha == sha1_pure(commit_canonical_spec(c))
}

pub open spec fn hash_binding_tags(s: ObjectStorage) -> bool {
    forall |sha: Sha1, g: TagData|
        #[trigger] s.tags.contains_pair(sha, g)
            ==> sha == sha1_pure(tag_canonical_spec(g))
}

/// **Headline ADR-0003 Ring-2 invariant.** Universal claim across all
/// four git object kinds: every persisted row has its SHA-1 equal to
/// the canonical hash of its content. Receive-pack's correctness
/// proof obligation reduces to "every row I created via create_*
/// satisfies this."
pub open spec fn hash_binding_full_invariant(s: ObjectStorage) -> bool {
    hash_binding_blobs(s)
        && hash_binding_trees(s)
        && hash_binding_commits(s)
        && hash_binding_tags(s)
}

// ── Preservation theorems ────────────────────────────────────────────

pub proof fn empty_satisfies_hash_binding_full()
    ensures
        hash_binding_full_invariant(ObjectStorage::empty()),
{
    // All four maps empty; universal quantifiers hold vacuously.
}

pub proof fn create_blob_preserves_hash_binding(
    s: ObjectStorage,
    principal_id: AccountId,
    repository_id: RepoId,
    sha: Sha1,
    blob: Blob,
)
    requires
        hash_binding_full_invariant(s),
    ensures
        hash_binding_full_invariant(s.create_blob(principal_id, repository_id, sha, blob)),
{
    let s2 = s.create_blob(principal_id, repository_id, sha, blob);
    // create_blob only touches blobs; trees/commits/tags identical to s.
    assert(s2.trees == s.trees);
    assert(s2.commits == s.commits);
    assert(s2.tags == s.tags);
    // Blob preservation: case analysis on whether the guard accepted.
    assert forall |k: Sha1, v: Blob|
        #[trigger] s2.blobs.contains_pair(k, v)
            implies k == sha1_pure(blob_canonical_spec(v.content))
    by {
        if k == sha && v == blob {
            // Just-inserted entry; satisfies invariant by guard
            // predicate (only reachable if the guard held).
        } else {
            // Pre-existing entry; satisfies IH.
            assert(s.blobs.contains_pair(k, v));
        }
    }
}

pub proof fn create_tree_preserves_hash_binding(
    s: ObjectStorage,
    principal_id: AccountId,
    repository_id: RepoId,
    sha: Sha1,
    tree: TreeData,
)
    requires
        hash_binding_full_invariant(s),
    ensures
        hash_binding_full_invariant(s.create_tree(principal_id, repository_id, sha, tree)),
{
    let s2 = s.create_tree(principal_id, repository_id, sha, tree);
    assert(s2.blobs == s.blobs);
    assert(s2.commits == s.commits);
    assert(s2.tags == s.tags);
    assert forall |k: Sha1, v: TreeData|
        #[trigger] s2.trees.contains_pair(k, v)
            implies k == sha1_pure(tree_canonical_spec(v))
    by {
        if k == sha && v == tree {
            // Just-inserted; guard required sha == sha1_pure(tree_canonical_spec(tree)).
        } else {
            assert(s.trees.contains_pair(k, v));
        }
    }
}

pub proof fn create_commit_preserves_hash_binding(
    s: ObjectStorage,
    principal_id: AccountId,
    repository_id: RepoId,
    sha: Sha1,
    commit: CommitData,
)
    requires
        hash_binding_full_invariant(s),
    ensures
        hash_binding_full_invariant(
            s.create_commit(principal_id, repository_id, sha, commit)
        ),
{
    let s2 = s.create_commit(principal_id, repository_id, sha, commit);
    assert(s2.blobs == s.blobs);
    assert(s2.trees == s.trees);
    assert(s2.tags == s.tags);
    assert forall |k: Sha1, v: CommitData|
        #[trigger] s2.commits.contains_pair(k, v)
            implies k == sha1_pure(commit_canonical_spec(v))
    by {
        if k == sha && v == commit {
        } else {
            assert(s.commits.contains_pair(k, v));
        }
    }
}

pub proof fn create_tag_preserves_hash_binding(
    s: ObjectStorage,
    principal_id: AccountId,
    repository_id: RepoId,
    sha: Sha1,
    tag: TagData,
)
    requires
        hash_binding_full_invariant(s),
    ensures
        hash_binding_full_invariant(s.create_tag(principal_id, repository_id, sha, tag)),
{
    let s2 = s.create_tag(principal_id, repository_id, sha, tag);
    assert(s2.blobs == s.blobs);
    assert(s2.trees == s.trees);
    assert(s2.commits == s.commits);
    assert forall |k: Sha1, v: TagData|
        #[trigger] s2.tags.contains_pair(k, v)
            implies k == sha1_pure(tag_canonical_spec(v))
    by {
        if k == sha && v == tag {
        } else {
            assert(s.tags.contains_pair(k, v));
        }
    }
}

// ── Cedar-before-write: structural lemma ─────────────────────────────

/// If the post-state of `create_blob` differs from the pre-state on
/// the blob map (i.e., a blob was actually persisted), the guard
/// must have held — meaning Cedar permitted Create on the
/// repository_id. **Derived** from the open-spec body of create_blob.
pub proof fn create_blob_implies_cedar(
    s: ObjectStorage,
    principal_id: AccountId,
    repository_id: RepoId,
    sha: Sha1,
    blob: Blob,
)
    ensures
        s.create_blob(principal_id, repository_id, sha, blob).blobs != s.blobs
            ==> cedar_permits(
                principal_id,
                seq!['C', 'r', 'e', 'a', 't', 'e'],
                repository_id.map_values(|b: u8| b as char),
            ),
{
    // If the blobs map changed, the if-branch of create_blob fired,
    // which requires the cedar_permits conjunct. Verus dispatches
    // this directly from the open spec definition.
}

} // verus!
