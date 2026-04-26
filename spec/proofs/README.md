# tg-spec Verus proofs

Ghost kernel-state model — the Ring-2 specification surface from
[RFC-0003](../../docs/rfc/0003-typed-handler-abi-and-verus.md) Slice 9.

This directory carries the verified content of the `tg-spec` crate.
None of it compiles into a binary; the standalone `verus` binary
reads the files directly.

## Files

| File                      | What it pins                                                                        | Verified items |
|---------------------------|-------------------------------------------------------------------------------------|----------------|
| `kernel_state.verus.rs`   | Core domain types, `KernelState`, `create_blob` + `update_ref` transitions, invariants, preservation theorems | 5              |

`kernel_state.verus.rs` proves:

- `empty_satisfies_hash_binding` — `KernelState::empty()` satisfies
  the hash-binding invariant vacuously.
- `create_blob_preserves_hash_binding` — every `create_blob` call
  preserves the invariant (the transition's guard requires the SHA
  to match the canonical hash, so newly-inserted entries satisfy the
  invariant by construction).
- `update_ref_preserves_hash_binding` — `update_ref` doesn't touch
  the blob map, so the blob-side invariant is preserved trivially.
- `update_ref_preserves_name_consistency` — when CAS succeeds, the
  inserted `Ref`'s `name` field matches the map key.

## Running

```bash
./verify.sh
```

Expected output:
```
=== verifying kernel_state.verus.rs ===
verification results:: 5 verified, 0 errors
```

Direct invocation:

```bash
~/verus/source/target-verus/release/verus \
    --crate-type=lib --crate-name=tg_spec_proofs \
    proofs/kernel_state.verus.rs
```

## What this enables

Ring-2 handler theorems become statable. Previously, a proof of
`serve_receive_pack` saying "every persisted Blob has matching SHA-1"
had nowhere to live — there was no name for "the kernel's persisted
blobs." Now there is: `KernelState::blobs`. A receive-pack proof
takes `(s: KernelState)` as ghost argument, applies one or more
`create_blob` transitions per inbound pack object, and concludes
`hash_binding_invariant(s_post)` via composition with the
preservation theorems here.

## What's still required for a fully-composed Ring-2 proof

1. **Cross-file lemma reuse.** Standalone `verus` invocation can't
   import this file from another proof file today; downstream proofs
   mirror locally. Cargo-verus path (see
   `~/temper/docs/VERUS.md`) is the unblock.
2. **Trees, commits, tags.** `KernelState` covers blobs and refs.
   Receive-pack persists trees/commits/tags too; each needs its
   own `Map`, transition function, and per-kind hash-binding
   invariant. Same template as `Blob`/`create_blob`.
3. **Cedar policy state.** `cedar_permits` is `uninterp` here — we
   trust the kernel to enforce it. A future revision could
   axiomatize a richer `CedarPolicySet` if Ring-2 proofs need to
   reason about specific policy fragments.
4. **Concurrent transitions.** CAS correctness here is at the
   transition level; modeling two handlers racing on the same ref
   needs a wider trace-based formulation. Out of scope for the
   initial sketch.

## Adding new transitions

For each new IOA action (e.g., `Tree.Create`, `Commit.Create`,
`Ref.ForceUpdate`):

1. Add the entity type (mirror the `[automaton]` and fields from
   `specs/<entity>.ioa.toml`).
2. Add a `Map<…, Entity>` to `KernelState`.
3. Add a `KernelState::<action>` open spec function modeling the
   transition's guard + state delta.
4. Add an invariant predicate matching the spec's `[[invariant]]`
   block.
5. Add a `*_preserves_*` proof. Verus typically dispatches these
   automatically when the transition's guard already establishes
   the invariant for new entries.
