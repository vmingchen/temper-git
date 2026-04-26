//! Verus-verified ref-row filtering: prove that the post-filter
//! output of `fetch_refs_for_repo` only carries rows with
//! `status == "Active"`.
//!
//! This is the verifiable core of the `.filter(|r| r.status == "Active")`
//! step in `serve_info_refs` (see `src/lib.rs:88`). The handler today
//! works on `Vec<RefRow>` whose `status` field is `String`; Verus has
//! limited String support, so we model the row using `Vec<u8>` for
//! the status/name bytes and prove the filter postcondition over the
//! byte representation. The logical content is identical: `RefRow.status
//! == "Active"` iff the bytes of that field equal the spec
//! `active_bytes()` constant.
//!
//! HEAD-first ordering — the second half of `fetch_refs_for_repo`'s
//! sort — is verified as a separate function (`partition_head_first`)
//! that splits an input list into HEAD-named rows followed by
//! non-HEAD rows. The full alphabetical sort within the non-HEAD
//! tail is *not* proven here — vstd's lex-cmp surface for
//! `Vec<u8>` doesn't expose what we'd need without significant
//! per-byte boilerplate. The HEAD-first guarantee is the part that
//! actually matters for git-protocol clients (HEAD is the
//! capabilities-carrying first line).
//!
//! Verified by running:
//!
//!     /home/bits/verus/source/target-verus/release/verus \
//!         --crate-type=lib --crate-name=refs_proofs \
//!         proofs/refs.verus.rs
//!
//! Last verified: 4 functions pass, 0 errors.

#![no_main]
#![allow(unused)]

use vstd::prelude::*;

verus! {

// ── Domain types ─────────────────────────────────────────────────────

/// Verus-friendly mirror of `RefRow` from `src/lib.rs`. The handler's
/// `RefRow.{name,target_sha,status}: String` becomes `Vec<u8>` here so
/// the `@` view lands in `Seq<u8>` rather than `Seq<char>` —
/// downstream pkt-line/wire code is byte-oriented anyway.
pub struct VerusRefRow {
    pub name: Vec<u8>,
    pub target_sha: Vec<u8>,
    pub status: Vec<u8>,
}

// ── Spec constants for byte-string literals ──────────────────────────
//
// Verus does not yet accept `b"Active"` byte-string literals in spec
// contexts; we materialize the corresponding sequences explicitly.
// The hex values are ASCII codepoints: 'A'=0x41, 'c'=0x63, etc.

/// The byte sequence `b"Active"`. Used as the predicate target for
/// `is_active`.
pub open spec fn active_bytes() -> Seq<u8> {
    seq![0x41u8, 0x63u8, 0x74u8, 0x69u8, 0x76u8, 0x65u8]
}

/// The byte sequence `b"HEAD"`. Used as the predicate target for
/// `is_head`.
pub open spec fn head_bytes() -> Seq<u8> {
    seq![0x48u8, 0x45u8, 0x41u8, 0x44u8]
}

// ── Verified predicates ──────────────────────────────────────────────

/// True iff the row's `status` field is exactly the bytes `b"Active"`.
/// The postcondition ties the boolean executable to the spec sequence,
/// so downstream proofs can rewrite freely.
pub fn is_active(row: &VerusRefRow) -> (out: bool)
    ensures
        out == (row.status@ == active_bytes()),
{
    if row.status.len() != 6 {
        return false;
    }
    let s = &row.status;
    let r = s[0] == 0x41u8
        && s[1] == 0x63u8
        && s[2] == 0x74u8
        && s[3] == 0x69u8
        && s[4] == 0x76u8
        && s[5] == 0x65u8;
    proof {
        if r {
            assert(s@ =~= active_bytes());
        } else {
            assert(s@ != active_bytes());
        }
    }
    r
}

/// True iff the row's `name` field is exactly the bytes `b"HEAD"`.
pub fn is_head(row: &VerusRefRow) -> (out: bool)
    ensures
        out == (row.name@ == head_bytes()),
{
    if row.name.len() != 4 {
        return false;
    }
    let n = &row.name;
    let r = n[0] == 0x48u8 && n[1] == 0x45u8 && n[2] == 0x41u8 && n[3] == 0x44u8;
    proof {
        if r {
            assert(n@ =~= head_bytes());
        } else {
            assert(n@ != head_bytes());
        }
    }
    r
}

// ── Filter: every output row has status == "Active" ──────────────────

/// Filter to the Active rows. Verus carries the postcondition that
/// every retained row has `status == active_bytes()` — universal
/// quantification over the entire output, not a sample.
///
/// Implementation drains the input by `pop()` (so output order is the
/// reverse of input order; the caller is expected to follow with a
/// sort step). This is intentional: avoiding `clone` keeps the proof
/// inside Verus' supported subset. Production code that wants
/// input-order preservation can reverse the result, or the caller
/// can be restructured to consume in reverse.
pub fn filter_active(rows: Vec<VerusRefRow>) -> (out: Vec<VerusRefRow>)
    ensures
        forall |i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).status@ == active_bytes(),
{
    let mut out: Vec<VerusRefRow> = Vec::new();
    let mut input = rows;
    while input.len() > 0
        invariant
            forall |k: int| 0 <= k < out@.len() ==> (#[trigger] out@[k]).status@ == active_bytes(),
        decreases input.len(),
    {
        let row = input.pop().unwrap();
        if is_active(&row) {
            out.push(row);
        }
    }
    out
}

// ── Partition: HEAD-named rows precede non-HEAD-named rows ───────────

/// Split a row list into (HEAD-named rows, non-HEAD-named rows). The
/// partition's `ensures` clause carries two universal properties:
///
///   * Every row in the first list has `name == b"HEAD"`.
///   * Every row in the second list has `name != b"HEAD"`.
///
/// Concatenating the two outputs (which `fetch_refs_for_repo` does
/// implicitly by virtue of HEAD's compare-less-than position) gives a
/// sequence where any HEAD ref precedes any non-HEAD ref — the wire
/// invariant `tg_wire::advertise_info_refs` relies on for the
/// capabilities-on-first-line convention.
pub fn partition_head_first(
    rows: Vec<VerusRefRow>,
) -> (out: (Vec<VerusRefRow>, Vec<VerusRefRow>))
    ensures
        forall |i: int| 0 <= i < out.0@.len() ==> (#[trigger] out.0@[i]).name@ == head_bytes(),
        forall |i: int| 0 <= i < out.1@.len() ==> (#[trigger] out.1@[i]).name@ != head_bytes(),
{
    let mut heads: Vec<VerusRefRow> = Vec::new();
    let mut others: Vec<VerusRefRow> = Vec::new();
    let mut input = rows;
    while input.len() > 0
        invariant
            forall |k: int| 0 <= k < heads@.len()  ==> (#[trigger] heads@[k]).name@ == head_bytes(),
            forall |k: int| 0 <= k < others@.len() ==> (#[trigger] others@[k]).name@ != head_bytes(),
        decreases input.len(),
    {
        let row = input.pop().unwrap();
        if is_head(&row) {
            heads.push(row);
        } else {
            others.push(row);
        }
    }
    (heads, others)
}

} // verus!
