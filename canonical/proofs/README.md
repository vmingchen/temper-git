# tg-canonical Verus proof obligations

Drafts of the Verus annotations that will land per
[RFC-0003](../../docs/rfc/0003-typed-handler-abi-and-verus.md) Slice 7
(Ring 0a — pure-library verification).

These files are **not compiled** by `cargo`. They sit outside `src/` so
the crate continues to build on the kernel-pinned nightly without a
Verus toolchain. They are reviewed as design artifacts during RFC-0003
Phases 0–2; once the kernel-side ADR-0063 lands and `cargo verus check`
is in CI, these get integrated into `src/` under `cfg(feature = "verify")`.

## Layout

| File              | Source under verification | Status |
|-------------------|---------------------------|--------|
| `blob.verus.rs`   | `src/blob.rs`             | sketch |
| `tree.verus.rs`   | `src/tree.rs`             | TODO   |
| `commit.verus.rs` | `src/commit.rs`           | TODO   |
| `tag.verus.rs`    | `src/tag.rs`              | TODO   |
| `sha1.verus.rs`   | `src/sha1.rs`             | TODO (axiomatized via `external_body`) |

## Activation

Once the kernel ships ADR-0063's `verify` feature on `temper-wasm-sdk`
and Verus is pinned in CI:

1. Move each `*.verus.rs` into `src/` under a sibling module gated by
   `#[cfg(feature = "verify")]`.
2. Add `verify = ["temper-wasm-sdk/verify"]` to `canonical/Cargo.toml`
   features.
3. CI gains a job: `cargo verus check -p tg-canonical --features verify`.

## Why drafts before tooling lands

- Reviewable as plain Rust during ADR review.
- Forces us to confront the spec shape before committing toolchain
  ergonomics.
- Surface area for catching axiom mismatches early (e.g., does our
  understanding of SHA-1 match what `vstd` provides?).

## Trust boundary

Verified pieces are stated as theorems against axiomatized primitives:
- `sha1::digest` — `external_body`. The crypto crate is trusted.
- `Vec::extend_from_slice`, `Vec::with_capacity`, `format!` — handled
  by `vstd`.
- Integer-to-decimal conversion in `format!("{}", n)` — bounded by
  `usize` width; spec uses an inductively-defined `decimal_digits`.

See `blob.verus.rs` for the worked example.
