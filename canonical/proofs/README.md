# tg-canonical Verus proofs

Formally verified properties of byte-exact git object serialization.
Per [RFC-0003](../../docs/rfc/0003-typed-handler-abi-and-verus.md)
Slice 7 / [ADR-0063](../../../temper/docs/adrs/0063-verus-readiness-for-wasm-sdk.md)
Phase 4, this is **the first Verus proof on `tg-canonical`** — it
validates that the kernel-side axioms surface (`temper-wasm-sdk::axioms`,
shipped by ADR-0063 Phase 1-3) is sufficient for downstream consumers
to compose against.

## Files

| File              | Source under verification | Verified items |
|-------------------|---------------------------|----------------|
| `blob.verus.rs`   | `src/blob.rs`             | 2              |

`blob.verus.rs` carries:

- `blob_canonical_bytes(content)` produces exactly
  `b"blob "` ++ `decimal_ascii(len)` ++ `b"\0"` ++ `content` —
  ADR-0003's hash-byte-match contract for blobs, proven for *every*
  input slice rather than the corpus exercised by
  `canonical/tests/git_parity.rs`.
- `decimal_ascii_len_bounds` lemma: the decimal ASCII rendering of a
  `usize` is always between 1 and 20 bytes (sufficient for any
  64-bit-host blob length).

## Running

```bash
./verify.sh
```

Expected: `verification results:: 2 verified, 0 errors`. The script
loops over every `.verus.rs` in this directory; add new proofs by
dropping a file in.

Direct invocation:

```bash
~/verus/source/target-verus/release/verus \
    --crate-type=lib --crate-name=blob_proofs \
    proofs/blob.verus.rs
```

## Why this is *not* part of `cargo build`

Same reason as the WIT modules' proofs (see
`../../wasm-modules/git_*_pack_wit/proofs/README.md`). `cargo verus
verify` is blocked on `verus_builtin_macros` requiring unstable
proc-macro features the available Rust toolchain doesn't expose.
Standalone `verus` works today.

## Trust boundary

Verified:
- `blob_canonical_bytes` matches `blob_canonical_spec` byte-for-byte.
- `decimal_ascii(n).len() ∈ [1, 20]` for `n <= u64::MAX`.

Trusted:
- `usize_to_decimal_ascii` — `external_body` axiom around `format!`.
  Trusting `format!`'s decimal output is on the same trust footing as
  trusting `sha1` / `flate2`. ADR-0003's parity tests against real
  `git` would catch any regression in this primitive.
- `decimal_ascii` is `uninterp` — Verus knows nothing about its
  implementation; only the length bounds we admit. Stronger axioms
  (e.g., uniqueness, `decimal_ascii(0) == seq![b'0']`) can be added if
  downstream proofs need them.

## What's deferred (and where it's tracked)

- **Composition with `axioms::sha1_pure`** to give the full ADR-0003
  hash-byte-match contract:
  `blob_hash(c) == hex_lower(sha1_pure(blob_canonical_spec(c@)))`.
  This needs the SDK's axioms reachable from a standalone-`verus`
  invocation, which today requires a local mirror of `sha1_pure` in
  the proof file or the cargo-verus toolchain integration. Tracked
  under ADR-0063's "future work" — once cargo-verus is unblocked,
  proofs `use temper_wasm_sdk::axioms::sha1_pure;` directly.
- **Tree, commit, tag canonical bytes.** Same template as blob; one
  follow-up file each.
- **Sortedness invariant on `tree_canonical_bytes`.** Verus can carry
  it; needs the same vstd `Vec` sort lemmas blob uses for byte
  concatenation.
