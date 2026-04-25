# temper-git WIT mirror

This directory mirrors `~/temper/wit/integration.wit` so that the
WIT-based WASM modules (`wasm-modules/git_upload_pack_wit/`,
`wasm-modules/git_receive_pack_wit/`) can build without reaching into
the not-yet-bumped `temper/` submodule. It is **not** an independent
WIT package — the canonical version lives in `~/temper/wit/`.

## When to update

When the kernel bumps the submodule pointer in `temper/` to a commit
that contains the new WIT revision, replace this directory with a
symlink:

```bash
rm -rf wit/
ln -s temper/wit wit
```

(or, equivalently, point the `wit_bindgen::generate!` paths in the
modules at `../../temper/wit`).

Until that submodule bump lands, this mirror is the source of truth for
the modules. Any change to the WIT must be made first in
`~/temper/wit/`, accepted there, and only then copied here.

## Validation

```bash
wasm-tools component wit ./wit/
```

Should round-trip with exit code 0.
