# git_upload_pack_wit Verus proofs

Formally verified properties of the upload-pack handler's pure
helpers, written in [Verus](https://github.com/verus-lang/verus).
Every file in this directory is the spec + implementation of one
logical unit, machine-checked via Z3 against the spec.

## Files

| File                  | What it pins                                                                          | Verified items |
|-----------------------|---------------------------------------------------------------------------------------|----------------|
| `pkt_line.verus.rs`   | pkt-line length encoding (u16 → ASCII hex header); 4-byte header / payload budget     | 3              |

The receive-pack proofs at
`../../git_receive_pack_wit/proofs/pkt_line.verus.rs` cover the
inverse parse direction. Composing the two postconditions (each
expressed against the same `hex_value` spec function) gives the
encode/decode round-trip property: anything upload-pack emits parses
back to the same u16 by receive-pack and by real `git`. Verus'
SMT backend hits its rlimit on the unrolled base-16 sum across `[u8; 4]`
when the round-trip is stated as a single lemma, so we leave it as
a bridge between two component theorems for now (annotated in the
source). The kernel-side `axioms::pkt_line` module per
[ADR-0063](../../../../temper/docs/adrs/0063-verus-readiness-for-wasm-sdk.md)
will eventually carry it as a single proof with the right rlimit
budget.

## Running

```bash
~/verus/source/target-verus/release/verus \
    --crate-type=lib --crate-name=pkt_line_proofs \
    proofs/pkt_line.verus.rs
```

Expect: `verification results:: 3 verified, 0 errors`. The `verify.sh`
script in this directory runs all proofs in one shot.

## Why this is *not* part of `cargo build`

See `../../git_receive_pack_wit/proofs/README.md` for the toolchain
rationale; the same reasoning applies here.

## Trust boundary

Verified:
- `encode_hex_nibble(n)` for `n < 16` produces a lowercase ASCII hex
  digit whose `hex_value` equals `n`.
- `encode_pkt_len(total)` produces a 4-byte header where each byte
  decodes back to the corresponding base-16 digit of `total`.
- `pkt_line_total_length(payload_len)` accepts iff `payload_len <= 0xFFFB`
  (the largest payload that fits with a 4-byte header in a u16 frame
  length) and returns `payload_len + 4`.

Trusted: same as receive-pack's proofs — vstd, Verus' Z3 backend, the
spec functions themselves (cross-checked by parity tests against real
`git`).

## Adding new proofs

Same pattern as receive-pack's proofs directory. Each new file gets a
table row, a `verify.sh` line, and a green run.
