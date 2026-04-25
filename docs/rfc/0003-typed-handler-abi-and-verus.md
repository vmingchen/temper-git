# RFC-0003: typed handler ABI and Verus formal verification

- Status: Draft
- Date: 2026-04-25
- Related:
  - [RFC-0001](0001-architecture.md) (v1 architecture, kernel deltas K-1 / K-2)
  - [RFC-0002](0002-push-and-clone.md) (slice cadence for the two git handlers)
  - [ADR-0003](../adr/0003-byte-exact-git-compat.md) (byte-exact compatibility — the headline correctness claim Verus targets)
  - `~/temper/docs/adrs/00NN-wit-wasm-integration-abi.md` (kernel delta this RFC depends on)
  - `~/temper/docs/adrs/00NN-verus-readiness.md` (kernel-side build & toolchain support)

## Goal

Make the two protocol handlers (`git_upload_pack`, `git_receive_pack`) formally verifiable against the byte-exact-compat contract (ADR-0003), the IOA state machines (`specs/*.ioa.toml`), and the authorization invariants (`policies/*.cedar`).

The current ABI between kernel and handler is JSON-blob:

```rust
// wasm-modules/git_upload_pack/src/lib.rs:43-48
let http_value = ctx.http_request.clone()
    .ok_or_else(|| "...".to_string())?;
let http: InboundHttp = serde_json::from_value(http_value)
    .map_err(|e| format!("http_request parse error: {e}"))?;
```

`Value` is a sum type of "string | number | array | object". Verus reasons over typed predicates; on `Value`, the strongest pre/postcondition you can write reduces to "this `Value` is the JSON encoding of an `InboundHttp`," which can only be spelled by exhibiting the parser. The spec becomes the implementation; SMT has nothing to bite.

This RFC plans the migration to a typed handler ABI and the rollout of Verus annotations on top, using temper-git as the exemplar app for the kernel-side change. It coordinates two upstream kernel ADRs that must land first.

## Status quo

What we have today (as of this RFC's date — see RFC-0002 for the wire-protocol slice cadence):

- Both handlers green: `git push` + `git clone` round-trip against a populated repository.
- `tg-canonical` (1.5 KLoC) — byte-exact serialization + SHA-1, parity-tested against real `git`. Pure Rust, zero non-std runtime deps.
- `tg-wire` (3.5 KLoC) — pkt-line, capabilities, command list, pack-v2 parser/emitter, sideband framing. Pure Rust except for `flate2` (zlib).
- WASM modules at 1.6 KLoC total: ~80% effectful (16 host-function call sites, 10 distinct OData endpoint shapes), ~20% pure (parsers, formatters, hash helpers).
- ABI: JSON-blob via `extern "C" fn run(_ctx_ptr: i32, _ctx_len: i32) -> i32`, 16 raw FFI host functions in `temper-wasm-sdk::host`, all using `(ptr, len)` marshaling.
- Wasmtime 29 with the `component-model` feature enabled in `~/temper/Cargo.toml`, but no actual WIT or component-model code in tree.
- No Verus presence in either repo. `temper-verify` uses Z3 directly via the `z3 = 0.19` crate, plus `stateright` and `proptest`. That is SMT + model checking + property testing — not a Rust-source verifier.
- Rust toolchain pinned to `nightly-2026-02-08` in `~/temper/rust-toolchain.toml`.

The verification surface today is exactly what's in `canonical/tests/git_parity.rs`, `wire/tests/git_parity.rs`, `wire/tests/git_pack_parity.rs`, plus the round-trip tests of RFC-0002. These are necessary but not sufficient: they show byte-exact agreement on the inputs they sample, not for *all* inputs.

## What we want at the end

Three concentric rings of verification, each compositional with the next:

**Ring 0 — pure libraries (`tg-canonical`, `tg-wire`).** Verus pre/postconditions on every public function, with `external_body` axioms for `sha1` and `flate2`. Theorems land like:

```
ensures blob_hash(c) == sha1_of(seq![b"blob ", len_ascii(c.len()), b"\0", c])
ensures forall |i, j| i < j => entry_name(emit(entries)[i]) <= entry_name(emit(entries)[j])
ensures parse_pack_v2(emit_pack_v2(objs)) == Ok(objs)
ensures pkt_line_decode(pkt_line_encode(p)) == Some(p)
```

**Ring 1 — typed handler ABI (WIT).** `serde_json::Value` traversal disappears from the handler. Each handler exports `serve(req: http.request) -> response`, where `http.request` is a typed WIT record, not a JSON envelope. OData calls become typed imports (`tdata.list-refs(repo: repo-id) -> result<list<ref-row>, tdata-error>`). Cedar checks become typed (`auth.permits(p: principal, a: action, r: resource) -> bool`). This ring is mostly an ABI redesign — its verification value is *enabling* Ring 2.

**Ring 2 — handler theorems against a ghost kernel state.** With Ring 1 in place, attach Verus contracts to the WIT-typed entry points. Use a ghost `KernelState` to model persistent effects (Blobs, Refs, Cedar policy). Axiomatize the WIT imports. Prove the handler-level invariants ADR-0003 and the spec files demand:

```
// git_receive_pack
ensures forall |sha, b| s.blobs.contains_pair(sha, b)
            ==> sha1_of(canonical_blob(b.content)) == sha
            // every persisted blob has a matching hash (ADR-0003)
ensures forall |r, new_sha| s.refs.contains_pair(r, new_sha) && !old(s).refs.contains_pair(r, new_sha)
            ==> exists |p| s.cedar.permits(p, Action::UpdateRef, r)
            // every ref update went through Cedar
ensures forall |sha| s.commits.contains_key(sha)
            ==> all_referenced_objects(s.commits[sha]).subset_of(s.blobs.dom() ∪ s.trees.dom())
            // commit closure: no commit references a missing object (acyclic-DAG fragment of CLAUDE.md proofs slot)

// git_upload_pack
ensures response.body == advertise_info_refs(filter_by_principal(s.refs, principal))
            // wire-format byte equality
ensures forall |ref| mentioned_in(response, ref) ==> s.cedar.permits(principal, Action::ReadRef, ref)
            // no information leak past Cedar
```

These are exactly the invariants the IOA L0–L3 cascade and Cedar enforce today by structure; Verus turns them into proofs that hold across all inputs, not just the test corpus.

## Scope

In scope:

- A WIT world for HTTP-style WASM integrations, owned by `~/temper` (the kernel).
- A migration of `git_upload_pack` and `git_receive_pack` to the typed ABI.
- Verus annotations across `tg-canonical` (full), `tg-wire` (full), and the two handlers (entry-point theorems).
- A ghost kernel-state model in a new `tg-spec/` crate.
- CI plumbing: `cargo verus check` job that gates merges on proof success.
- Updated parity / round-trip test harness so existing RFC-0002 gates continue to apply.

Out of scope:

- Verifying the kernel itself. Verus annotations on `temper-server`, `temper-runtime`, `temper-platform` are a separate, much larger initiative that's not coupled to this work — we treat the kernel as trusted via `external_body` axioms.
- Verifying `wasmtime`, `flate2`, `sha1`, `serde`, `wit-bindgen`. Trusted by axiom.
- Verus-style proofs of REST/GraphQL handlers. Same template will apply once those handlers exist; this RFC only covers the two git handlers.
- Migration of *other* temper apps off the JSON-blob ABI. We'll keep the JSON-blob ABI working alongside the WIT ABI for the foreseeable future — the kernel ADR specifies a coexistence story.
- Component-model packaging beyond what's needed for typed integrations (no per-handler `wasi:cli/run` worlds, no nested components).

## Architecture

### The four interlocking pieces

```
                                ┌──────────────────────────────┐
                                │   ~/temper                   │
                                │  ┌────────────────────────┐  │
                                │  │ wit/                   │  │
                                │  │   integration.wit      │  │
   handler exports ─────────────┼──┼─→ world: http-handler  │  │
   handler imports ←────────────┼──┼── world: http-handler  │  │
                                │  │ (tdata, cedar, log…)   │  │
                                │  └────────────────────────┘  │
                                │  ┌────────────────────────┐  │
                                │  │ crates/temper-wasm-sdk │  │
                                │  │   guest-side bindings  │  │
                                │  │   ghost shim: KernelState model
                                │  │   verus axioms on imports
                                │  └────────────────────────┘  │
                                │  ┌────────────────────────┐  │
                                │  │ crates/temper-wasm     │  │
                                │  │   wasmtime::component  │  │
                                │  │   linker (host side)   │  │
                                │  └────────────────────────┘  │
                                └──────────────────────────────┘
                                              ▲
                                              │ (submodule)
                                              │
                                ┌──────────────────────────────┐
                                │   temper-git                 │
                                │  canonical/  ←── Verus Ring 0a
                                │  wire/       ←── Verus Ring 0b
                                │  tg-spec/    ←── ghost KernelState (NEW)
                                │  wasm-modules/git_upload_pack ←── Ring 2
                                │  wasm-modules/git_receive_pack ←── Ring 2
                                └──────────────────────────────┘
```

Four pieces, four owners:

1. **WIT world** in `~/temper/wit/` — the contract. Owned by Temper kernel.
2. **Component-model linker** in `~/temper/crates/temper-wasm/` — the runtime. Owned by Temper kernel.
3. **Guest SDK + axioms** in `~/temper/crates/temper-wasm-sdk/` — the bridge. Owned by Temper kernel; consumed by every app.
4. **Verified handlers + ghost model** in `temper-git/` — the proof obligations. Owned by temper-git.

### Why this layering

The kernel cannot ship Verus annotations on its imports without committing every Temper app to Verus. The split puts Verus where it pays — in the apps that opt in — and uses `external_body` axioms to bridge the unverified kernel.

### What changes about the wire to the SDK

Today the SDK's `temper_module!` macro wraps `extern "C" fn run(_ctx_ptr: i32, _ctx_len: i32) -> i32` and parses a JSON `Context` blob out of memory. Tomorrow the SDK provides `wit_bindgen::generate!` from the `http-handler` world, and the handler implements the generated `Guest` trait:

```rust
// before
temper_module! {
    fn run(ctx: Context) -> Result<Value> {
        let http: InboundHttp = serde_json::from_value(ctx.http_request.unwrap())?;
        // ...
    }
}

// after
struct GitUploadPack;
impl Guest for GitUploadPack {
    fn serve(req: HttpRequest) -> Result<HttpResponse, HandlerError> {
        // req is a typed record. No JSON parsing.
        // ...
    }
}
export!(GitUploadPack);
```

The macro stays for backward compatibility (every other temper app still uses it); the `wit_bindgen::generate!` path is opt-in.

### Ghost kernel model

A new crate `tg-spec/` sits alongside `canonical/` and `wire/`. It contains:

- A Verus model of `KernelState` — pure data: `Map<Sha1, Blob>`, `Map<Sha1, Tree>`, `Map<Sha1, Commit>`, `Map<Sha1, Tag>`, `Map<RefName, Sha1>`, `CedarPolicySet`, `Map<RepoId, RepoMeta>`.
- Pure transition functions for each IOA action: `create_blob(s: KernelState, b: Blob) -> KernelState`, `update_ref(s: KernelState, r: RefName, prev: Sha1, new: Sha1) -> Result<KernelState, RefUpdateError>`.
- Verus-level invariants matching the IOA `[[invariant]]` blocks in `specs/*.ioa.toml` (`ArchivedIsFinal`, `DeletedIsFinal`, the acyclic-commit-DAG invariant, "ref-exists-if-named", etc.).
- `external_body` axioms binding the WIT-typed `tdata` and `cedar-check` imports to these pure transitions.

This crate has *no* runtime code. It's spec-only — never linked into the WASM binary. Its purpose is to give Verus a model of the world the handler interacts with.

### Compositionality

Ring 0 lemmas import into Ring 2 proofs without re-verification. Example: `git_receive_pack` proves "every persisted blob has matching SHA-1" by using the Ring 0 theorem `blob_hash(c) == sha1_of(canonical_blob(c))` plus the axiom `create_blob` requires `b.id == blob_hash(b.content)`. The handler proof itself is just a few hundred lines of glue, not a re-derivation of cryptographic facts.

## Sequencing

Twelve slices, dependency-ordered. Each slice is shippable in isolation; later slices depend on earlier ones but earlier ones don't break if later slices stall.

### Slice 0 — kernel ADRs landed

Lands in `~/temper`:

- ADR for the WIT integration ABI: turns on the wasmtime component model in `temper-wasm`, defines the `http-handler` world, ships the SDK macro `wit_bindgen` path, keeps the JSON-blob path for existing apps.
- ADR for Verus readiness: nightly toolchain alignment (Verus 0.x tracks specific nightlies; check compatibility with `nightly-2026-02-08`), `vstd` dependency strategy, build tooling (`cargo verus`), CI plumbing.

Gate: ADRs accepted, no code yet.

### Slice 1 — WIT skeleton in `~/temper/wit/`

The world definition compiles via `wasm-tools component wit`. No host code wiring yet. PoC handler in `~/temper/wasm-modules/` to validate the world.

```wit
// ~/temper/wit/integration.wit (sketch)
package temper:integration@0.1.0;

interface http {
  record header { name: string, value: string }
  record path-param { name: string, value: string }
  record request {
    method: string,
    path: string,
    query: string,
    headers: list<header>,
    params: list<path-param>,
    principal: principal,
    body-stream: u32,    // stream id, opaque to guest; SDK wraps as Read
  }
  record response-head { status: u16, headers: list<header> }
  enum body-result { ok, write-error, closed }
  resource response-body {
    write-chunk: func(b: list<u8>) -> body-result;
    finish: func() -> body-result;
  }
}

interface principal {
  record principal {
    id: string,
    kind: principal-kind,
    scopes: list<string>,
    account-id: string,
    agent-type: string,
    agent-type-verified: bool,
  }
  enum principal-kind { anonymous, system, customer, admin }
}

interface tdata {
  // typed OData replacements — one per OData call shape used by handlers
  variant tdata-error { not-found, conflict(string), forbidden, transport(string) }
  // exact shapes deferred to Slice 3, where temper-git owns the contract for git entities.
  list-refs:    func(repo-id: string) -> result<list<u8>, tdata-error>;  // bytes = JSON for now; replaced with typed in Slice 3
  list-objects: func(set: string, sha: string) -> result<list<u8>, tdata-error>;
  create:       func(set: string, body: list<u8>) -> result<list<u8>, tdata-error>;
  call-action:  func(set: string, id: string, action: string, body: list<u8>) -> result<list<u8>, tdata-error>;
}

interface cedar {
  permits: func(p: principal.principal, action: string, resource: string) -> bool;
}

interface log {
  record level { level: log-level, target: string }
  enum log-level { trace, debug, info, warn, error }
  emit: func(l: level, msg: string);
}

world http-handler {
  import http;
  import principal;
  import tdata;
  import cedar;
  import log;

  export serve: func(req: http.request, head: http.response-head)
                -> result<http.response-body, string>;
}
```

Gate: `wasm-tools component wit ~/temper/wit/` validates clean. PoC component compiles via `wit-bindgen` + `cargo build --target wasm32-wasip2`.

### Slice 2 — kernel-side component linker

Turn on `wasmtime::component::*` in `temper-wasm`. Keep the existing module-mode dispatcher; add a parallel component-mode dispatcher behind a per-`HttpEndpoint` flag (`is_component: bool`). All current apps stay on module-mode.

Implement the host side of the WIT imports:
- `tdata` → forwards to `temper-server::odata::*`
- `cedar` → forwards to existing Cedar evaluator
- `log`, `principal`, etc. → straightforward

Gate: existing `cargo test` in `~/temper` stays green; new test exercises a hello-world component handler end-to-end.

### Slice 3 — temper-git OData contract typing

Today the handler does:
```rust
ctx.http_call("GET", "/tdata/Refs", &headers, "")
   .map(|r| serde_json::from_str::<RefsResponse>(&r.body))
```

Slice 3 promotes the OData shapes the handlers care about to typed WIT records owned by temper-git (since temper-git defines the entity model). This requires extending the WIT world with a temper-git-specific interface or moving `tdata` to a per-app interface. Decision deferred until Slice 2 lands — both shapes are workable.

Output: `temper-git/wit/tdata-git.wit` with typed records for `Ref`, `Blob`, `Tree`, `Commit`, `Tag`, `PullRequest`, `GitToken`. WIT imports become typed.

### Slice 4 — migrate `git_upload_pack` to the WIT ABI

Rewrite `wasm-modules/git_upload_pack/src/lib.rs` against the generated `Guest` trait. Handler compiles to `wasm32-wasip2`. RFC-0002's existing parity + round-trip tests must stay green; the WASM binary changes form, but the wire bytes don't.

Gate: `git_parity` and `git_pack_parity` tests pass against the new component. Round-trip via real `git clone` byte-identical.

### Slice 5 — migrate `git_receive_pack` to the WIT ABI

Same as Slice 4 for the receive-pack handler.

Gate: `git push` round-trip against the WIT-typed handler is byte-identical and SHA-stable.

### Slice 6 — Verus toolchain in CI

Add `cargo verus` to the temper-git CI matrix. Job runs on a Verus-pinned nightly (per `~/temper`'s Verus-readiness ADR). Initially the job only verifies an empty marker module — we want the plumbing green before we add real proofs.

Gate: CI job runs on every PR. Annotates the PR with proof results.

### Slice 7 — Verus on `tg-canonical` (Ring 0a)

Annotate every public function in `canonical/`. Specs:

- `blob_canonical_bytes`: `ensures result == seq![b"blob ", len_ascii(content.len()), b"\0", content]`
- `blob_hash`: `ensures result == sha1_hex_of(blob_canonical_bytes(content))` (with `sha1_hex_of` axiomatized)
- `tree_canonical_bytes`: `ensures sorted_by_name(parse_tree(result)) && length and entry round-trip`
- `tree_hash`, `commit_hash`, `tag_hash`: structurally similar
- `parse_commit`, `parse_tag`, `parse_tree`: round-trip with the canonical emitters

`Sha1::update`/`Sha1::digest` axiomatized via `external_body`.

Gate: `cargo verus check -p tg-canonical` passes. ADR-0003's hash-byte-match contract upgraded from "tested on a corpus" to "proven for all inputs in the spec subset."

### Slice 8 — Verus on `tg-wire` (Ring 0b)

Annotate `pkt_line`, `capabilities`, `commands`, `pack`, `sideband`, `advertise`. Specs:

- `pkt_line_decode(pkt_line_encode(p)) == Some(p)` for `p.len() <= MAX_PAYLOAD`
- `parse_pack_v2(emit_pack_v2(objs)) == Ok(objs)` for non-delta object lists
- `parse_commands(buf)` total parser correctness against the smart-HTTP grammar
- Sideband framing bounds: every output frame `len <= 65520`, every channel byte ∈ {1,2,3}

`flate2::deflate` / `flate2::inflate` axiomatized via `external_body` with the spec `inflate(deflate(x)) == x`. We *do not* axiomatize that `deflate(x) == deflate(y) iff x == y` — zlib output is not unique, and ADR-0003's byte-exactness against `git` lives in parity tests, not Verus.

Gate: `cargo verus check -p tg-wire` passes.

### Slice 9 — `tg-spec` ghost kernel model

Create the `tg-spec/` crate. Verus-only, never linked into a binary. Defines `KernelState`, transition functions, IOA-spec-derived invariants. Ships axiom shims for the WIT imports.

Gate: `cargo verus check -p tg-spec` passes. The IOA invariants compile as Verus predicates and are machine-checked against the transition functions.

### Slice 10 — Verus on `git_upload_pack` (Ring 2a)

Add Verus annotations to the upload-pack handler. Theorems:

- `serve(req)` `ensures` response body equals `advertise_info_refs(filter_by_principal(s.refs, req.principal))` for `info/refs` requests.
- For the upload-pack POST, ensure the emitted pack contains exactly the closure of `wants` minus `haves` reachable via Ring 0 lemmas (no extra objects leaked).
- No-leak lemma: every ref name appearing in the response satisfies `cedar.permits(req.principal, "read", ref)`.

The ghost `KernelState` is read-only on this path, simplifying the proof.

Gate: `cargo verus check -p git_upload_pack` passes. RFC-0002 round-trip tests stay green.

### Slice 11 — Verus on `git_receive_pack` (Ring 2b)

The hard one. Theorems:

- `ensures` every persisted blob has matching SHA-1 (ADR-0003).
- `ensures` every ref update goes through Cedar.
- `ensures` no commit closure is left dangling (every reachable tree/blob exists in the store at end of transition).
- Compare-and-swap correctness on `Ref.Update`: if two concurrent invocations see the same `PreviousCommitSha`, exactly one of them produces an `ok` and the other produces `ng`.
- IOA-invariant preservation: `ArchivedIsFinal`, `DeletedIsFinal`.

Gate: `cargo verus check -p git_receive_pack` passes. RFC-0002 push tests stay green.

### Slice 12 — proofs/ slot

Per CLAUDE.md: "TLA+ / IOA specs we own + their verification status. The git object graph has real invariants (acyclic commit DAG, tree-hash integrity, ref-exists-if-named); these belong in TLA+." Currently empty.

With Verus carrying the per-function obligations, `proofs/` becomes the home for *whole-system* invariants that need a Stateright/TLA+ model: cross-handler concurrency (two pushes racing on the same ref), liveness (a commit with no parents eventually GC's), Cedar policy hierarchies. These complement Verus, which is per-call.

Gate: at least one TLA+ model + Stateright check committed for the acyclic-commit-DAG invariant.

## Readiness gates

Per RFC-0002's gate convention:

- **Gate A (ABI parity).** After Slice 5: round-trip + parity tests stay green against WIT-typed handlers. ADR-0003's byte-exact compat contract preserved. *No verification yet — just the migration.*
- **Gate B (libraries proven).** After Slice 8: `cargo verus check -p tg-canonical -p tg-wire` passes in CI. Failing the check blocks merges.
- **Gate C (handlers proven).** After Slice 11: `cargo verus check` passes for both git handlers. The byte-exact-compat claim of ADR-0003 has both an empirical proof (parity tests) and a formal proof (Verus theorems composed on Ring 0).
- **Gate D (system invariants).** After Slice 12: `proofs/` houses at least one whole-system invariant with a passing model check.

## Trust boundary

What is *trusted* (axiomatic) vs. *proven*:

| Layer                       | Trusted                                  | Proven                                  |
|-----------------------------|------------------------------------------|-----------------------------------------|
| `sha1`, `flate2`, `serde`   | yes                                      | —                                       |
| `wasmtime`, `wit-bindgen`   | yes                                      | —                                       |
| Temper kernel (server, runtime, platform) | yes (via `external_body` axioms) | —                                       |
| `tg-canonical`              | —                                        | byte-exact serialization, SHA-1 binding |
| `tg-wire`                   | zlib trusted; framing proven             | pkt-line, pack, commands, sideband      |
| `tg-spec`                   | —                                        | IOA invariants, transition correctness  |
| `git_upload_pack`           | —                                        | response equals spec; no Cedar leak     |
| `git_receive_pack`          | —                                        | hash binding; Cedar; CAS; IOA invariants|
| Outside-world git compat    | parity tests against real `git`          | —                                       |

Verus does not replace the parity tests. zlib output non-uniqueness, real-git version drift, and host-OS quirks all live outside Verus' reach. The parity tests pin the empirical contract; Verus pins the structural contract; together they're stronger than either alone.

## Risks

1. **Verus nightly drift.** Verus tracks specific Rust nightlies. `~/temper` is on `nightly-2026-02-08`; the latest Verus may demand a different one. The Verus-readiness ADR resolves this; if the resolution is "Verus uses a different nightly," we ship two toolchain pins (one for the kernel build, one for the verified-app build).

2. **WIT migration churn for non-temper-git apps.** The WIT ABI is opt-in per `HttpEndpoint`. Existing apps stay on JSON-blob until they migrate. No forced cutover.

3. **Verus expressiveness.** Some specs (e.g., precise zlib output) cannot be proven without verifying zlib itself. We cap our ambition: prove the structural contract; rely on parity tests for byte-exactness against real-world tools.

4. **Proof maintenance burden.** Every function change costs a proof update. Mitigation: keep proof obligations on a small surface (libraries + handler entry points), not the entire codebase. Slice 12's whole-system invariants are model-checked (Stateright/TLA+), not Verus-proven, because they evolve faster.

5. **Compile times.** Verus runs Z3 per function. We isolate verified code into separate crates so iterating on unverified handler glue doesn't pay SMT cost. Estimate: 60–180s for a clean `cargo verus check` on the libraries; 30–90s incremental.

## Non-goals

- Verifying handler liveness ("every push eventually completes"). Verus proves partial correctness and termination on bounded loops; unbounded liveness lives in TLA+/Stateright.
- Verifying network-level adversarial behavior (a malicious git client crafting packs designed to OOM the parser). We prove parser correctness on well-formed inputs and budget-driven termination on all inputs; resource exhaustion is a runtime concern handled by `WasmResourceLimits`.
- Verifying byte-exact output against real `git` *as a Verus theorem*. ADR-0003's empirical contract stays in `git_parity.rs`. Verus proves the structural contract.
- Migrating all temper apps off the JSON-blob ABI. The kernel ADR explicitly preserves coexistence.

## Alternatives considered

1. **Verus on the JSON-blob ABI.** Rejected for the reasons in the Goal section: spec degenerates to "the parser parses the parser."

2. **Refinement types via something other than Verus** (Liquid Haskell-style for Rust, e.g., Flux, Prusti, Creusot). Verus picked because (a) it has the strongest Z3-backed automation, (b) the kernel already depends on Z3, (c) it has good support for `Map`/`Seq` ghost types we need for `KernelState`, (d) the project is active and tracks recent Rust nightlies.

3. **Component model directly without WIT** (raw wasmtime component types in Rust). Rejected because WIT is the schema language the entire WASM ecosystem aligns on; WIT is what gets us cross-language temper apps in the future without re-deriving the ABI.

4. **Verus on a Rust→Coq extraction** (a la CompCert-style verified extraction). Massive overkill; Verus' SMT automation is what makes Ring 0 tractable in days, not months.

5. **Skip Ring 1, do Verus on the existing JSON ABI by writing a Verus-friendly parser.** Hairsplitting: the parser would have to be its own spec (the very problem we're avoiding) and the gains are negligible vs. the WIT migration we want anyway for compile-time ABI safety.

## Next

After this RFC is accepted: kick off Slice 0 by writing the kernel-side ADRs. The temper-git side waits on those, then Slices 3–12 land in order.
