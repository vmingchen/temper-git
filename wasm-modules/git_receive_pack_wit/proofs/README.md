# git_receive_pack_wit Verus proofs

Formally verified properties of the receive-pack handler's pure
helpers, written in [Verus](https://github.com/verus-lang/verus). Every
file in this directory is the spec + implementation of one logical
unit, machine-checked via Z3 against the spec.

## Files

| File                  | What it pins                                                                 | Verified items |
|-----------------------|------------------------------------------------------------------------------|----------------|
| `pkt_line.verus.rs`   | pkt-line length parsing (ASCII hex header → u16); sideband-1 frame budget    | 4              |

## Running

```bash
~/verus/source/target-verus/release/verus \
    --crate-type=lib --crate-name=pkt_line_proofs \
    proofs/pkt_line.verus.rs
```

Expect: `verification results:: 4 verified, 0 errors`. Any change that
breaks a `requires`/`ensures` clause fails verification — no escape
hatch short of weakening the spec.

The `verify.sh` script in this directory runs all proofs in one shot.

## Why this is *not* part of `cargo build`

The cargo-side Verus integration (`cargo verus verify`) requires
building Verus' `verus_builtin_macros` crate, which uses
unstable proc-macro features (`proc_macro::tracked`,
`proc_macro_quote`, `proc_macro_expand`, `proc_macro_diagnostic`) that
the Rust toolchain in this environment doesn't expose. Verus' own
toolchain wrangles around this with a custom rustc; reproducing that
inside cargo from a downstream crate is non-trivial. The standalone
`verus` binary, in contrast, drives Verus' rustc directly and works on
single-file inputs without rebuilding `verus_builtin_macros`.

This is the rough split documented in
[`docs/rfc/0003-typed-handler-abi-and-verus.md`](../../../docs/rfc/0003-typed-handler-abi-and-verus.md)
(see "Slice 6 — Verus toolchain in CI" and "Slice 9 — `tg-spec` ghost
kernel model"): the cargo-integrated, `axioms`-aware path lives in
[ADR-0063](../../../../temper/docs/adrs/0063-verus-readiness-for-wasm-sdk.md).

## Trust boundary

Verified:
- Every byte of `parse_pkt_len`'s output equals the spec arithmetic
  `h0*4096 + h1*256 + h2*16 + h3`.
- `parse_hex_nibble` accepts exactly the bytes for which `is_ascii_hex`
  holds.
- `is_flush` is true exactly when the four bytes equal `b"0000"`.
- `sideband_pkt_total(c)` accepts iff `c <= 65515` and equals `c + 5`.

Trusted (axiomatic):
- The `vstd` integer arithmetic primitives.
- Verus' Z3 backend (`rust_verify` correctness, version
  `0.2026.01.08.ca57575`).
- The spec functions themselves capture what we *want* the wire format
  to mean — a buggy spec is a buggy proof. Spec correctness is checked
  by parity tests (`wire/tests/git_pack_parity.rs` etc.) against real
  `git`, not Verus.

## Adding new proofs

1. Drop `<topic>.verus.rs` in this directory.
2. Use `#![no_main]`, `use vstd::prelude::*;`, wrap content in `verus! {…}`.
3. Add an entry to the table above.
4. Add an invocation to `verify.sh`.
5. Run `verify.sh` and confirm green.
