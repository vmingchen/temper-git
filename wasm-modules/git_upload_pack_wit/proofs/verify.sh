#!/usr/bin/env bash
# Run every Verus proof in this directory. Exits non-zero on any
# verification failure or any unhandled error.

set -euo pipefail

VERUS_BIN="${VERUS_BIN:-$HOME/verus/source/target-verus/release/verus}"

if [[ ! -x "$VERUS_BIN" ]]; then
  echo "verus binary not found or not executable: $VERUS_BIN" >&2
  echo "Set VERUS_BIN, or build Verus from source at \$HOME/verus/." >&2
  exit 2
fi

cd "$(dirname "$0")"

fail=0
for f in *.verus.rs; do
  name="${f%.verus.rs}_proofs"
  echo "=== verifying $f ==="
  if ! "$VERUS_BIN" --crate-type=lib --crate-name="$name" "$f"; then
    fail=1
  fi
done

exit "$fail"
