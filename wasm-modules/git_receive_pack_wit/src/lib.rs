//! git_receive_pack_wit — WIT-typed (component-model) receive-pack handler.
//!
//! Functional twin of `wasm-modules/git_receive_pack`, built against
//! the WIT-typed ABI from ADR-0062. RFC-0003 Slice 5 in isolation; the
//! kernel-side component dispatcher (ADR-0062 Phase 2) doesn't exist
//! yet, so this binary cannot be invoked end-to-end. What this PoC
//! shows:
//!
//!   * `Request` is typed: method/path/headers/params/principal are
//!     records, the body is a `Vec<u8>` instead of a stream id behind
//!     a JSON envelope.
//!   * The kernel resolves auth before dispatch and hands a typed
//!     `Principal` to the guest. No GitToken lookup, no Bearer/Basic
//!     header parsing in this module.
//!   * Object persistence and ref updates flow through typed
//!     `tdata.create-row` / `tdata.call-action` instead of raw
//!     `host_http_call("POST", "/tdata/Blobs", ...)`.
//!
//! What this PoC *defers*:
//!
//!   * Streaming pack parsing. WIT 0.1 ships an eager `body: list<u8>`,
//!     so very large pushes (>~16 MiB) will hit kernel-side body limits.
//!     The legacy `wasm-modules/git_receive_pack` continues to handle
//!     production push traffic via streaming.
//!
//! See `wasm-modules/git_receive_pack/src/lib.rs` for the full legacy
//! implementation.

// See git_upload_pack_wit for the rationale on this allow.
#![allow(unsafe_op_in_unsafe_fn)]

extern crate alloc;

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;

use base64::Engine;
use base64::engine::general_purpose::STANDARD as B64;
use tg_wire::{advertise_info_refs, commands, encode_into, flush, pack, AdvertisedRef, CommandKind, Service};

wit_bindgen::generate!({
    world: "http-handler",
    path: "../../wit",
});

use temper::integration::http::{Header, ResponseHead};
use temper::integration::log;
use temper::integration::tdata;

struct GitReceivePackWit;

impl Guest for GitReceivePackWit {
    fn serve(req: Request) -> Result<Response, String> {
        let path = req.path.split('?').next().unwrap_or(req.path.as_str()).to_string();

        match (req.method.as_str(), path.as_str()) {
            ("GET", p) if p.ends_with("/info/refs") => serve_info_refs(&req),
            ("POST", p) if p.ends_with("/git-receive-pack") => serve_receive_pack(&req),
            _ => Ok(text_response(404, "no receive-pack route matches")),
        }
    }
}

export!(GitReceivePackWit);

// ── Routes ──────────────────────────────────────────────────────────

fn serve_info_refs(req: &Request) -> Result<Response, String> {
    let service = match query_param(req, "service").as_deref() {
        Some("git-receive-pack") => Service::ReceivePack,
        Some("git-upload-pack") | None => Service::UploadPack,
        Some(other) => {
            return Ok(text_response(400, &format!("unknown service '{other}'")));
        }
    };
    let refs: Vec<AdvertisedRef<'_>> = Vec::new();
    let body = advertise_info_refs(service, &refs)
        .map_err(|e| format!("advertise_info_refs: {e}"))?;
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

fn serve_receive_pack(req: &Request) -> Result<Response, String> {
    let owner = param(req, "owner");
    let repo = param(req, "repo");
    let repository_id = format!("rp-{owner}-{repo}");

    if matches!(req.principal.kind, temper::integration::principal::PrincipalKind::Anonymous) {
        return Ok(text_response(401, "receive-pack requires authentication"));
    }

    // Split the eager body into command-list bytes (pkt-line framed,
    // ending at 0000) and the trailing pack bytes. The legacy module
    // streams these via BufReader; here we have the whole buffer.
    let (cmd_bytes, pack_bytes) = split_command_list(&req.body)
        .map_err(|e| format!("split commands: {e}"))?;
    let parsed = commands::parse_commands(cmd_bytes)
        .map_err(|e| format!("parse_commands: {e}"))?;

    let mut unpack_status = "ok".to_string();
    let mut per_obj_errors: Vec<String> = Vec::new();
    let mut object_count = 0u32;

    let cursor = std::io::Cursor::new(pack_bytes);
    let reader = std::io::BufReader::new(cursor);
    let mut parser = pack::StreamingPackParser::begin(reader)
        .map_err(|e| format!("pack header: {e}"))?;
    while let Some(obj) = parser
        .next_object()
        .map_err(|e| format!("pack next: {e}"))?
    {
        let (kind_prefix, entity_set) = match obj.kind {
            pack::ObjectKind::Blob => ("blob", "Blobs"),
            pack::ObjectKind::Tree => ("tree", "Trees"),
            pack::ObjectKind::Commit => ("commit", "Commits"),
            pack::ObjectKind::Tag => ("tag", "Tags"),
        };
        let sha = match obj.kind {
            pack::ObjectKind::Blob => tg_canonical::blob_hash(&obj.data),
            _ => sha_from_prefix(kind_prefix, &obj.data),
        };
        let mut canonical = format!("{} {}\0", kind_prefix, obj.data.len()).into_bytes();
        canonical.extend_from_slice(&obj.data);

        let row = build_object_row(obj.kind, &sha, &repository_id, &obj.data, &canonical);
        let body_json = row.to_string();
        match tdata::create_row(entity_set, body_json.as_bytes()) {
            Ok(_) => {}
            Err(tdata::TdataError::Conflict(_)) => {
                // Object already exists — re-push of an unchanged blob
                // is fine; treat as success per the legacy module.
                object_count += 1;
                continue;
            }
            Err(e) => {
                let msg = format_tdata_error(e);
                unpack_status = format!("error writing {sha}: {msg}");
                per_obj_errors.push(format!("{sha}:{msg}"));
            }
        }
        object_count += 1;
    }

    if let Err(e) = parser.finish() {
        unpack_status = format!("trailer: {e}");
        per_obj_errors.push(format!("trailer:{e}"));
    }

    let mut ref_statuses: Vec<(String, Result<(), String>)> = Vec::new();
    for cmd in &parsed.commands {
        let result = if !per_obj_errors.is_empty() {
            Err(format!("object write failures: {}", per_obj_errors.len()))
        } else {
            apply_ref_command(&repository_id, cmd)
        };
        ref_statuses.push((cmd.refname.clone(), result));
    }

    log::emit(
        log::Level::Info,
        "git_receive_pack_wit",
        &format!(
            "push repo={repository_id} objects={object_count} refs={} principal={}",
            parsed.commands.len(),
            req.principal.id
        ),
    );

    // Build the receive-pack pkt-line response.
    let mut inner = Vec::new();
    let unpack_line = if unpack_status == "ok" {
        "unpack ok\n".to_string()
    } else {
        format!("unpack {unpack_status}\n")
    };
    encode_into(&mut inner, unpack_line.as_bytes())
        .map_err(|e| format!("encode unpack: {e}"))?;
    for (refname, status) in &ref_statuses {
        let line = match status {
            Ok(()) => format!("ok {refname}\n"),
            Err(reason) => format!("ng {refname} {reason}\n"),
        };
        encode_into(&mut inner, line.as_bytes())
            .map_err(|e| format!("encode ref status: {e}"))?;
    }
    flush(&mut inner);

    let sideband = parsed.capabilities.iter().any(|c| c == "side-band-64k");
    let mut body = Vec::new();
    if sideband {
        for chunk in inner.chunks(65515) {
            let mut payload = Vec::with_capacity(1 + chunk.len());
            payload.push(0x01);
            payload.extend_from_slice(chunk);
            encode_into(&mut body, &payload)
                .map_err(|e| format!("encode sideband: {e}"))?;
        }
        flush(&mut body);
    } else {
        body.extend_from_slice(&inner);
    }

    Ok(Response {
        head: ResponseHead {
            status: 200,
            headers: vec![
                header("content-type", "application/x-git-receive-pack-result"),
                header("cache-control", "no-cache"),
            ],
        },
        body,
    })
}

// ── tdata typed calls ───────────────────────────────────────────────

fn apply_ref_command(
    repository_id: &str,
    cmd: &tg_wire::RefCommand,
) -> Result<(), String> {
    match cmd.kind() {
        CommandKind::Create => {
            let row = serde_json::json!({
                "Id": ref_id_for(repository_id, &cmd.refname),
                "RepositoryId": repository_id,
                "Name": cmd.refname,
                "TargetCommitSha": cmd.new_sha,
                "Kind": if cmd.refname.starts_with("refs/tags/") { "tag" } else { "branch" },
                "Status": "Active",
                "UpdatedAt": "1970-01-01T00:00:00Z",
            });
            tdata::create_row("Refs", row.to_string().as_bytes())
                .map(|_| ())
                .map_err(format_tdata_error)?;
            propagate_to_open_prs(repository_id, &cmd.refname, &cmd.new_sha);
            Ok(())
        }
        CommandKind::Update => {
            let ref_id = ref_id_for(repository_id, &cmd.refname);
            let body = serde_json::json!({
                "PreviousCommitSha": cmd.old_sha,
                "NewCommitSha": cmd.new_sha,
            });
            tdata::call_action("Refs", &ref_id, "Update", body.to_string().as_bytes())
                .map(|_| ())
                .map_err(format_tdata_error)?;
            propagate_to_open_prs(repository_id, &cmd.refname, &cmd.new_sha);
            Ok(())
        }
        CommandKind::Delete => Err("ref delete not implemented".into()),
    }
}

fn propagate_to_open_prs(repository_id: &str, refname: &str, new_head: &str) {
    let filter = format!(
        "RepositoryId eq '{repository_id}' and SourceRef eq '{refname}' \
         and (State eq 'Open' or State eq 'UnderReview' \
              or State eq 'ChangesRequested' or State eq 'Approved')"
    );
    let query = format!(
        "$filter={}&$select=Id",
        urlencode(&filter)
    );
    let body = match tdata::list_rows("PullRequests", &query) {
        Ok(b) => b,
        Err(_) => return,
    };
    let parsed: serde_json::Value = match serde_json::from_slice(&body) {
        Ok(v) => v,
        Err(_) => return,
    };
    let Some(items) = parsed.get("value").and_then(|v| v.as_array()) else {
        return;
    };
    for item in items {
        let Some(pr_id) = item.get("Id").and_then(|v| v.as_str()) else {
            continue;
        };
        let body = serde_json::json!({ "NewHeadCommitSha": new_head });
        let _ = tdata::call_action(
            "PullRequests",
            pr_id,
            "UpdateHead",
            body.to_string().as_bytes(),
        );
    }
}

// ── Pack helpers ────────────────────────────────────────────────────

fn split_command_list(body: &[u8]) -> Result<(&[u8], &[u8]), String> {
    // Walk pkt-line framing until we hit a 0000 flush; everything after
    // is pack bytes. Mirrors `read_command_list` from the legacy module
    // but without the BufReader overhead since the body is already in
    // memory.
    let mut i = 0usize;
    loop {
        if i + 4 > body.len() {
            return Err("truncated pkt-line".into());
        }
        let len_str = core::str::from_utf8(&body[i..i + 4])
            .map_err(|_| "pkt length not ASCII")?;
        let pkt_len = usize::from_str_radix(len_str, 16)
            .map_err(|_| "pkt length not hex")?;
        i += 4;
        if pkt_len == 0 {
            return Ok((&body[..i], &body[i..]));
        }
        if pkt_len < 4 {
            return Err(format!("pkt length {pkt_len} below 4-byte header"));
        }
        let payload = pkt_len - 4;
        if i + payload > body.len() {
            return Err("truncated pkt payload".into());
        }
        i += payload;
    }
}

fn build_object_row(
    kind: pack::ObjectKind,
    sha: &str,
    repository_id: &str,
    raw: &[u8],
    canonical: &[u8],
) -> serde_json::Value {
    let canonical_b64 = B64.encode(canonical);
    let created_at = "1970-01-01T00:00:00Z";
    match kind {
        pack::ObjectKind::Blob => serde_json::json!({
            "Id": sha,
            "RepositoryId": repository_id,
            "Size": raw.len(),
            "Content": B64.encode(raw),
            "CanonicalBytes": canonical_b64,
            "Status": "Durable",
            "CreatedAt": created_at,
        }),
        pack::ObjectKind::Tree => serde_json::json!({
            "Id": sha,
            "RepositoryId": repository_id,
            "CanonicalBytes": canonical_b64,
            "Status": "Durable",
            "CreatedAt": created_at,
        }),
        pack::ObjectKind::Commit => {
            let parsed = tg_canonical::parse_commit(raw).ok();
            let (tree, parents, author, committer, message, gpg) = match &parsed {
                Some(c) => (
                    c.tree.clone(),
                    c.parents.join(","),
                    c.author.clone(),
                    c.committer.clone(),
                    c.message.clone(),
                    c.gpg_signature.clone(),
                ),
                None => Default::default(),
            };
            let mut row = serde_json::json!({
                "Id": sha,
                "RepositoryId": repository_id,
                "TreeSha": tree,
                "ParentShas": parents,
                "Author": author,
                "Committer": committer,
                "Message": message,
                "CanonicalBytes": canonical_b64,
                "Status": "Durable",
                "CreatedAt": created_at,
            });
            if let Some(sig) = gpg {
                row["PgpSignature"] = serde_json::Value::String(sig);
            }
            row
        }
        pack::ObjectKind::Tag => {
            let parsed = tg_canonical::parse_tag(raw).ok();
            let (target, ttype, name, tagger, message, gpg) = match &parsed {
                Some(t) => (
                    t.object.clone(),
                    t.target_type.clone(),
                    t.tag.clone(),
                    t.tagger.clone(),
                    t.message.clone(),
                    t.gpg_signature.clone(),
                ),
                None => Default::default(),
            };
            let mut row = serde_json::json!({
                "Id": sha,
                "RepositoryId": repository_id,
                "TargetSha": target,
                "TargetType": ttype,
                "TagName": name,
                "Tagger": tagger,
                "Message": message,
                "CanonicalBytes": canonical_b64,
                "Status": "Durable",
                "CreatedAt": created_at,
            });
            if let Some(sig) = gpg {
                row["PgpSignature"] = serde_json::Value::String(sig);
            }
            row
        }
    }
}

fn sha_from_prefix(prefix: &str, body: &[u8]) -> String {
    let header = format!("{} {}\0", prefix, body.len());
    let mut hasher = tg_canonical::Sha1::new();
    hasher.update(header.as_bytes());
    hasher.update(body);
    hasher.hex()
}

fn ref_id_for(repository_id: &str, refname: &str) -> String {
    format!("rf-{}-{}", repository_id, refname.replace('/', "-"))
}

fn urlencode(s: &str) -> String {
    s.replace(' ', "%20").replace('\'', "%27")
}

// ── helpers ─────────────────────────────────────────────────────────

fn format_tdata_error(e: tdata::TdataError) -> String {
    match e {
        tdata::TdataError::NotFound => "tdata: not found".into(),
        tdata::TdataError::Conflict(s) => format!("tdata conflict: {s}"),
        tdata::TdataError::Forbidden => "tdata: forbidden".into(),
        tdata::TdataError::BadRequest(s) => format!("tdata bad request: {s}"),
        tdata::TdataError::Transport(s) => format!("tdata transport: {s}"),
    }
}

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
