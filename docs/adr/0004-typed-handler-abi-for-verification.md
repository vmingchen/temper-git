# ADR-0004: typed handler ABI to enable formal verification

## Status

Proposed — 2026-04-25. Companion to [RFC-0003](../rfc/0003-typed-handler-abi-and-verus.md), which is the operational plan. Depends on the kernel-side ADRs in `~/temper/docs/adrs/`:
- ADR-0062: WIT-typed WASM integration ABI
- ADR-0063: Verus-readiness for the WASM SDK

## Context

[ADR-0003](0003-byte-exact-git-compat.md) commits temper-git to byte-exact git compatibility, tested against real `git` via parity harnesses (`canonical/tests/git_parity.rs`, `wire/tests/git_parity.rs`, `wire/tests/git_pack_parity.rs`) and round-trip tests (RFC-0002 Gate 3). These tests are necessary but not universal: they show byte-exact agreement on the inputs they sample, not on every possible input.

The two protocol handlers (`wasm-modules/git_upload_pack`, `wasm-modules/git_receive_pack`) currently consume a JSON-blob ABI:

```rust
// wasm-modules/git_upload_pack/src/lib.rs:43-48
let http_value = ctx.http_request.clone()
    .ok_or_else(|| "git_upload_pack requires HttpEndpoint dispatch".to_string())?;
let http: InboundHttp = serde_json::from_value(http_value)
    .map_err(|e| format!("http_request parse error: {e}"))?;
```

The kernel marshals `WasmInvocationContext` into a JSON string in linear memory; the guest deserializes it via `serde_json`. Outbound calls (`/tdata/Refs`, `/tdata/Blobs`, `/tdata/PullRequests`, etc.) follow the same shape: typed Rust values are JSON-encoded into a buffer, posted by `host_http_call`, and the response is JSON-decoded back.

This ABI cannot carry a formal-verification claim. Refinement-type verifiers (Verus, Prusti, Creusot) reason over typed predicates; on `serde_json::Value`, the strongest predicate is "this Value is a JSON encoding of an InboundHttp," and the only way to spell that predicate is by exhibiting the parser. Spec degenerates to implementation.

For temper-git to formally verify the byte-exact-compat contract, the Cedar-gating contract, and the IOA invariants, the handler ABI must be typed end-to-end. The kernel-side ADR-0062 commits Temper to providing such an ABI via the WebAssembly Component Model (WIT). This ADR records temper-git's decision to adopt it, and the verification plan that follows.

## Decision

**temper-git migrates `git_upload_pack` and `git_receive_pack` from the JSON-blob ABI to the WIT-typed `temper:integration/http-handler` world introduced by ADR-0062. The migration is a precondition for the Verus annotations described in RFC-0003.**

Specifically:

### Migration sequencing

1. **Wait on kernel deltas.** RFC-0003 Slice 0 — accept ADR-0062 and ADR-0063 in `~/temper`. Slices 1–3 land kernel-side: WIT world, component-mode dispatcher, SDK feature gate.
2. **Migrate `git_upload_pack`** (RFC-0003 Slice 4). Existing parity + round-trip tests stay green. No wire-protocol bytes change.
3. **Migrate `git_receive_pack`** (RFC-0003 Slice 5). Same gate.
4. **Verus rings 0–2.** RFC-0003 Slices 7–11 add proofs.

### What the new handler looks like

Today's entry:

```rust
temper_module! {
    fn run(ctx: Context) -> Result<Value> {
        let http: InboundHttp = serde_json::from_value(ctx.http_request.unwrap())?;
        match (http.method.as_str(), strip_query(&http.path)) {
            ("GET",  p) if p.ends_with("/info/refs") => serve_info_refs(&ctx, &http),
            ("POST", p) if p.ends_with("/git-upload-pack") => serve_upload_pack(&ctx, &http),
            _ => respond_text(&http, 404, "text/plain", "no upload-pack route matches"),
        }
    }
}
```

After:

```rust
use temper_wasm_sdk::wit::exports::temper::integration::http_handler::Guest;
use temper_wasm_sdk::wit::temper::integration::http::{Request, ResponseHead, ResponseBody};

struct GitUploadPack;

impl Guest for GitUploadPack {
    fn serve(req: Request, head: ResponseHead) -> Result<ResponseBody, String> {
        match (req.method.as_str(), strip_query(&req.path)) {
            ("GET",  p) if p.ends_with("/info/refs") => serve_info_refs(&req, head),
            ("POST", p) if p.ends_with("/git-upload-pack") => serve_upload_pack(&req, head),
            _ => respond_text(head, 404, "text/plain", "no upload-pack route matches"),
        }
    }
}

temper_wasm_sdk::export!(GitUploadPack);
```

`Request` is a typed record (`method: String, path: String, query: String, headers: Vec<Header>, params: Vec<PathParam>, principal: Principal, body_stream: u32`). No JSON parsing. The kernel and handler agree on the schema at build time; an ABI break is a compile error, not a runtime parse error.

### What the OData calls look like

Today the handler does:

```rust
let body = ctx.http_call("GET", "/tdata/Refs", &principal.outbound_headers(), "")?;
let parsed: RefsResponse = serde_json::from_str(&body.body)?;
```

After:

```rust
use temper_wasm_sdk::wit::temper::integration::tdata;

let body_bytes = tdata::list("Refs", "$filter=RepositoryId eq 'rp-foo-bar'")?;
let parsed: RefsResponse = serde_json::from_slice(&body_bytes)?;
```

The transition is incremental. ADR-0062's `tdata` interface keeps OData's body-shape as JSON bytes for now — `result<list<u8>, tdata-error>` — so we don't have to define typed records for every OData entity in one go. RFC-0003 Slice 3 promotes the bodies to typed records once we know which shapes are most-used. The error variant *is* typed today, so `not-found` / `conflict` / `forbidden` / `transport` distinctions land in the type system immediately.

### What stays unchanged

- The wire-protocol bytes the handlers emit. RFC-0002 round-trip tests pass against both the old and new handler shapes.
- ADR-0003's byte-exact-compat contract.
- The handler's logic — only the ABI seam changes.
- All `tg-canonical` and `tg-wire` library calls.
- Cedar policies (`policies/*.cedar`) and IOA specs (`specs/*.ioa.toml`).

### What enables Verus

After this migration, every handler entry point has a typed signature. Verus pre/postconditions attach naturally:

```rust
// Conceptual — full annotations land in RFC-0003 Slice 11.
fn serve(req: Request, head: ResponseHead, ghost s: &mut KernelState)
    -> Result<ResponseBody, String>
    requires req.principal.kind != PrincipalKind::Anonymous
    ensures forall |sha, b| s.blobs.contains_pair(sha, b) && !old(s).blobs.contains_pair(sha, b)
                ==> sha1_hex(blob_canonical_bytes(b.content)) == sha,
    ensures forall |r, new| s.refs.contains_pair(r, new) && !old(s).refs.contains_pair(r, new)
                ==> exists |p| s.cedar.permits(p, "UpdateRef", r),
{ ... }
```

The ghost `KernelState` is supplied by a new `tg-spec/` crate (RFC-0003 Slice 9) modeling the kernel's persistent effects. The contracts above are exactly what the IOA `[[invariant]]` blocks and Cedar policies say in prose; Verus turns them into proofs that hold for all inputs, not just the test corpus.

## Consequences

### Positive

- A path to formally verifying byte-exact compat (ADR-0003) over all inputs, not just a sampled corpus.
- Compile-time safety on the handler ABI: kernel-side schema changes break the handler build, not the running handler.
- Cleaner handler code — no more `.unwrap()` on `ctx.http_request`, no more `serde_json::from_value` boilerplate at every entry point.
- Aligns temper-git with the broader Component Model ecosystem; future cross-language guests for new handlers (e.g., a GraphQL resolver in Go) become possible.

### Negative

- Migration churn for the two existing handlers. Estimated 2–4 days per handler including parity test re-runs.
- Two parallel ABIs in the SDK during migration. Mitigated by the SDK's feature gate (`legacy-json` vs. `component`); we never ship a handler using both.
- Larger WASM artifacts — components carry the WIT type section. Estimated 10–15% size increase. Negligible for our deployment.
- Adds `wasm-tools` and `wit-bindgen` to the build-time toolchain dependency list.

### Risks

- **ADR-0062 stalls or changes.** If the kernel-side ABI design shifts, the temper-git migration shifts with it. Mitigation: stay close to the kernel ADR review, prototype against draft worlds in `wasm-modules/hello-component/` before committing.
- **Performance regression.** Component-model encode/decode of the inbound `request` record could be slower than the JSON-blob path for small requests. Mitigation: ADR-0062 commits to measuring before declaring acceptable; we re-run RFC-0002's perf-relevant tests after the migration.
- **Verus integration friction.** Even with typed inputs, getting Verus to verify a handler that touches I/O is non-trivial. RFC-0003 budgets time for ghost-state modeling and axiom design.

### Compatibility

- The wire-protocol contract of ADR-0003 is preserved. RFC-0002 round-trip tests continue to gate merges. Migrating the ABI should not change a single byte of the smart-HTTP response.
- `git clone`, `git push`, `git ls-remote`, and `gh api` calls against temper-git behave identically before and after the migration. If a parity test diff surfaces, the migration PR fails.

## Non-Goals

- Replacing `tg-canonical` or `tg-wire`. They stay as host-testable Rust libraries. The handlers wrap them; that wrapper is what changes.
- Defining temper-git-specific WIT worlds. We use the kernel's `http-handler` world directly. Per-app entity-typed `tdata` is RFC-0003 Slice 3, future work.
- Migrating any other temper apps. We're the consumer of ADR-0062, not the migration coordinator.
- Verus annotations themselves — those land per RFC-0003 Slices 7–11, after this ABI migration.

## Rollback Policy

The migration is per-handler and reversible up to Verus annotations landing.

If the new ABI fails (e.g., kernel-side bug, performance regression we can't close), we can revert each handler PR independently. The `temper_module!` macro and `legacy-json` SDK feature stay supported indefinitely per ADR-0062.

Once Verus annotations are in (RFC-0003 Slice 7+), reverting becomes more expensive — the proof obligations are tied to the typed signatures. At that point the rollback story is "remove proofs first, then revert ABI," handled by separate PRs.
