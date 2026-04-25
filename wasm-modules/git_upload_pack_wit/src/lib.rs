//! git_upload_pack_wit — WIT-typed (component-model) upload-pack handler.
//!
//! Functional twin of `wasm-modules/git_upload_pack`, but built against
//! the WIT-typed ABI introduced by `~/temper`'s ADR-0062 instead of the
//! JSON-blob `temper_module!` macro. Demonstrates RFC-0003 Slice 4 in
//! isolation; the kernel-side component dispatcher (ADR-0062 Phase 2)
//! that invokes this binary doesn't exist yet, so end-to-end is not
//! possible. What we *can* show:
//!
//!   * Typed `Request` / `Response` records replacing `serde_json::Value`.
//!   * Auth resolved by the kernel (`req.principal` is already typed);
//!     no `auth.rs`, no GitToken lookup, no SHA-256 of bearer tokens.
//!   * Outbound OData calls go through `tdata.list-rows` / `tdata.get-row`
//!     instead of `host_http_call("GET", "/tdata/Refs", ...)`.
//!
//! What this PoC *defers*:
//!
//!   * Streaming response bodies. The current WIT 0.1 returns an eager
//!     `response { head, body }`; very large packs (>~100 MiB) won't
//!     fit. A 0.2 revision with `stream-serve` lands separately.
//!   * Pack emission for non-trivial fetches. We implement
//!     advertisement (info/refs), and POST `git-upload-pack` returns a
//!     500 with a clear "streaming required" message. Slice B-equivalent
//!     work moves to the typed module after WIT 0.2.
//!
//! See `wasm-modules/git_upload_pack/src/lib.rs` for the full legacy
//! implementation we're tracking.

// wit-bindgen's generated `_export_serve_cabi` is an `unsafe fn` whose
// body itself does not require unsafe ops; Rust 2024 fires on this even
// though it's correct codegen. Suppress repo-wide so we don't litter
// generated code with attribute insertions.
#![allow(unsafe_op_in_unsafe_fn)]

extern crate alloc;

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;

use tg_wire::{advertise_info_refs, AdvertisedRef, Service};

wit_bindgen::generate!({
    world: "http-handler",
    path: "../../wit",
});

use temper::integration::http::{Header, ResponseHead};
use temper::integration::log;
use temper::integration::principal::Principal;
use temper::integration::tdata;

struct GitUploadPackWit;

impl Guest for GitUploadPackWit {
    fn serve(req: Request) -> Result<Response, String> {
        let path = req.path.split('?').next().unwrap_or(req.path.as_str()).to_string();

        match (req.method.as_str(), path.as_str()) {
            ("GET", p) if p.ends_with("/info/refs") => serve_info_refs(&req),
            ("POST", p) if p.ends_with("/git-upload-pack") => serve_upload_pack(&req),
            _ => Ok(text_response(404, "no upload-pack route matches")),
        }
    }
}

export!(GitUploadPackWit);

// ── Routes ──────────────────────────────────────────────────────────

fn serve_info_refs(req: &Request) -> Result<Response, String> {
    let service = match query_param(req, "service").as_deref() {
        Some("git-upload-pack") | None => Service::UploadPack,
        Some("git-receive-pack") => Service::ReceivePack,
        Some(other) => {
            return Ok(text_response(400, &format!("unknown service '{other}'")));
        }
    };

    let owner = param(req, "owner");
    let repo = param(req, "repo");
    let repository_id = format!("rp-{owner}-{repo}");

    let refs_rows = fetch_refs_for_repo(&req.principal, &repository_id)?;
    let owned: Vec<(String, String)> = refs_rows
        .into_iter()
        .filter(|r| r.status == "Active")
        .map(|r| (r.target_sha, r.name))
        .collect();
    let refs: Vec<AdvertisedRef<'_>> = owned
        .iter()
        .map(|(sha, name)| AdvertisedRef {
            sha: sha.as_str(),
            name: name.as_str(),
        })
        .collect();

    let body = advertise_info_refs(service, &refs)
        .map_err(|e| format!("advertise_info_refs: {e}"))?;

    log::emit(
        log::Level::Info,
        "git_upload_pack_wit",
        &format!(
            "info/refs repo={repository_id} refs={} bytes={}",
            refs.len(),
            body.len()
        ),
    );

    Ok(Response {
        head: ResponseHead {
            status: 200,
            headers: vec![
                header("content-type", service.content_type()),
                header("cache-control", "no-cache"),
            ],
        },
        body,
    })
}

fn serve_upload_pack(_req: &Request) -> Result<Response, String> {
    // Pack emission requires streaming response bodies. WIT 0.1's
    // eager `response { head, body }` is unsuitable for non-trivial
    // packs. Wired through, but currently 501 until WIT 0.2 lands a
    // streaming `stream-serve` export. The legacy
    // `wasm-modules/git_upload_pack` continues to handle production
    // fetch/clone traffic.
    Ok(text_response(
        501,
        "git-upload-pack POST requires streaming response (WIT 0.2)",
    ))
}

// ── tdata typed calls ───────────────────────────────────────────────

struct RefRow {
    name: String,
    target_sha: String,
    status: String,
}

fn fetch_refs_for_repo(
    _principal: &Principal,
    repository_id: &str,
) -> Result<Vec<RefRow>, String> {
    // Body bytes are JSON for now (WIT 0.1 ships `result<list<u8>, …>`);
    // RFC-0003 Slice 3 promotes these to typed records. Until then, the
    // parsing layer is the same as the legacy module's.
    let body = tdata::list_rows("Refs", "")
        .map_err(format_tdata_error)?;
    let parsed: serde_json::Value = serde_json::from_slice(&body)
        .map_err(|e| format!("Refs parse: {e}"))?;
    let items = parsed
        .get("value")
        .and_then(|v| v.as_array())
        .cloned()
        .unwrap_or_default();
    let mut rows = Vec::with_capacity(items.len());
    for row in items {
        let fields = row.get("fields").cloned().unwrap_or(serde_json::Value::Null);
        let repo = fields
            .get("RepositoryId")
            .and_then(|v| v.as_str())
            .unwrap_or("");
        if repo != repository_id {
            continue;
        }
        let name = fields
            .get("Name")
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string();
        let target_sha = fields
            .get("TargetCommitSha")
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string();
        let status = fields
            .get("Status")
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string();
        if name.is_empty() || target_sha.is_empty() {
            continue;
        }
        rows.push(RefRow {
            name,
            target_sha,
            status,
        });
    }
    rows.sort_by(|a, b| {
        let a_head = a.name == "HEAD";
        let b_head = b.name == "HEAD";
        match (a_head, b_head) {
            (true, false) => core::cmp::Ordering::Less,
            (false, true) => core::cmp::Ordering::Greater,
            _ => a.name.cmp(&b.name),
        }
    });
    Ok(rows)
}

fn format_tdata_error(e: tdata::TdataError) -> String {
    match e {
        tdata::TdataError::NotFound => "tdata: not found".into(),
        tdata::TdataError::Conflict(s) => format!("tdata conflict: {s}"),
        tdata::TdataError::Forbidden => "tdata: forbidden".into(),
        tdata::TdataError::BadRequest(s) => format!("tdata bad request: {s}"),
        tdata::TdataError::Transport(s) => format!("tdata transport: {s}"),
    }
}

// ── helpers ─────────────────────────────────────────────────────────

fn header(name: &str, value: &str) -> Header {
    Header {
        name: name.into(),
        value: value.into(),
    }
}

fn text_response(status: u16, body: &str) -> Response {
    Response {
        head: ResponseHead {
            status,
            headers: vec![header("content-type", "text/plain")],
        },
        body: body.as_bytes().to_vec(),
    }
}

fn param(req: &Request, key: &str) -> String {
    req.params
        .iter()
        .find(|p| p.name == key)
        .map(|p| p.value.clone())
        .unwrap_or_default()
}

fn query_param(req: &Request, key: &str) -> Option<String> {
    let qs = if !req.query.is_empty() {
        req.query.as_str()
    } else {
        // Fallback: legacy callers may put the query in the path.
        req.path.splitn(2, '?').nth(1)?
    };
    for pair in qs.split('&') {
        let mut it = pair.splitn(2, '=');
        let k = it.next()?;
        let v = it.next().unwrap_or("");
        if k == key {
            return Some(v.to_string());
        }
    }
    None
}
