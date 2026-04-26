//! Build-time Verus verification.
//!
//! When the `verify` feature is enabled, this script runs every
//! `*.verus.rs` proof file in `proofs/` through the standalone
//! `verus` binary. A failed verification fails the cargo build.
//!
//! Default builds (no `verify` feature) skip this entirely — cargo
//! short-circuits via the `CARGO_FEATURE_VERIFY` env-var check below.
//!
//! Why not just `cargo verus verify`? See `~/temper/docs/VERUS.md` —
//! the upstream subcommand is blocked on `verus_builtin_macros`
//! requiring unstable proc-macro features the available rustc
//! doesn't expose. This build script bridges that gap by invoking
//! Verus directly on each proof file (which works) instead of
//! letting cargo recompile Verus' internal crates (which doesn't).
//!
//! Configuration:
//!   - `VERUS_BIN` env var picks the verus binary; defaults to
//!     `$HOME/verus/source/target-verus/release/verus`.
//!   - `cargo:rerun-if-changed=proofs` tells cargo to re-run this
//!     script only when proof files change.

use std::path::Path;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=proofs");
    println!("cargo:rerun-if-env-changed=VERUS_BIN");
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_VERIFY");

    if std::env::var_os("CARGO_FEATURE_VERIFY").is_none() {
        return;
    }

    let proofs_dir = Path::new("proofs");
    if !proofs_dir.is_dir() {
        return;
    }

    let verus = std::env::var("VERUS_BIN").unwrap_or_else(|_| {
        let home = std::env::var("HOME").expect("HOME unset");
        format!("{home}/verus/source/target-verus/release/verus")
    });

    if !Path::new(&verus).exists() {
        panic!(
            "verus binary not found at {verus} — set VERUS_BIN or build Verus from source"
        );
    }

    let mut had_failure = false;
    for entry in std::fs::read_dir(proofs_dir).expect("read proofs/") {
        let entry = entry.expect("dir entry");
        let path = entry.path();
        let name = match path.file_name().and_then(|s| s.to_str()) {
            Some(n) if n.ends_with(".verus.rs") => n.to_string(),
            _ => continue,
        };
        let crate_name = format!(
            "{}_{}_proofs",
            std::env::var("CARGO_PKG_NAME")
                .unwrap_or_else(|_| "unknown".into())
                .replace('-', "_"),
            name.trim_end_matches(".verus.rs").replace('-', "_"),
        );
        println!("cargo:warning=verifying {}", path.display());
        let status = Command::new(&verus)
            .args(["--crate-type=lib", "--crate-name", &crate_name])
            .arg(&path)
            .status()
            .unwrap_or_else(|e| panic!("failed to spawn verus: {e}"));
        if !status.success() {
            had_failure = true;
            println!(
                "cargo:warning=verus verification failed for {}",
                path.display()
            );
        }
    }

    if had_failure {
        panic!("verus verification failed (see cargo:warning lines above)");
    }
}
