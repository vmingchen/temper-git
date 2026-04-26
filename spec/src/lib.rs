//! # tg-spec — ghost kernel-state model
//!
//! This crate is a **verification artifact**, not runtime code. It
//! ships the Verus specification of the Temper kernel state visible
//! to temper-git's verified handlers — the surface RFC-0003 Slice 9
//! calls "the ghost `KernelState`."
//!
//! There is no executable code here. The verified content lives in
//! [`proofs/kernel_state.verus.rs`](../proofs/kernel_state.verus.rs)
//! and is exercised by:
//!
//! ```bash
//! ./proofs/verify.sh
//! ```
//!
//! ## Why a crate?
//!
//! The Cargo package gives the verified surface a name (`tg-spec`)
//! and a stable directory layout that downstream verified crates
//! will eventually depend on. Today, standalone-`verus` invocation
//! reads the proof file directly; once `cargo verus verify` is
//! unblocked (see `~/temper/docs/VERUS.md`), downstream crates will
//! `[dependencies] tg-spec = { path = "../spec", features = ["verify"] }`
//! and `use tg_spec::kernel_state::*;` in their proofs.
//!
//! ## Surface
//!
//! - **Domain types:** `Sha1`, `RefName`, `RepoId`, `AccountId`,
//!   `Blob`, `Ref`.
//! - **Aggregate state:** `KernelState` with `blobs: Map<Sha1, Blob>`
//!   and `refs: Map<RefName, Ref>`.
//! - **Pure transitions:** `KernelState::create_blob`,
//!   `KernelState::update_ref` (compare-and-swap).
//! - **Invariants:** `hash_binding_invariant`,
//!   `ref_name_consistent_invariant`.
//! - **Preservation theorems:** each transition is proven to
//!   preserve the relevant invariants.
//!
//! Ring-2 handler proofs (e.g., `serve_receive_pack` showing
//! "every persisted Blob has matching SHA-1") compose against this
//! surface: load `KernelState`, apply the per-action transition,
//! check the invariant holds.
