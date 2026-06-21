//! `rv-coverage` — measure how much **real** Rust the `rv-rustfe` front-end can
//! lower, and surface *why* it can't lower the rest.
//!
//! It walks a directory of `.rs` files (e.g. the local Cargo registry source —
//! a large, diverse corpus of idiomatic Rust), and for each file records:
//!   * **tree-sitter parse** — does the grammar accept the file at all?
//!   * **lower** — does `rv-rustfe` lower it to IR?
//! then prints the success rate plus a histogram of the top lowering-failure
//! reasons (the front-end's own error messages, with source locations stripped),
//! so the *next* features to build are chosen from data, not guesswork.
//!
//! Usage: `rv-coverage <dir> [--limit N]`

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

/// Skip pathologically large (usually generated) files to keep a run quick.
const MAX_FILE_BYTES: u64 = 512 * 1024;

#[derive(Default)]
struct Stats {
    scanned: usize,
    lowered: usize,
    lower_failed: usize,
    parse_failed: usize,
    panicked: usize,
    /// lowering-failure reason (location-stripped) -> count.
    reasons: HashMap<String, usize>,
    /// panic'd file paths (so a remaining crash bug is debuggable).
    panic_files: Vec<String>,
}

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let mut dir: Option<String> = None;
    let mut limit = usize::MAX;
    while let Some(a) = args.next() {
        match a.as_str() {
            "--limit" => limit = args.next().and_then(|n| n.parse().ok()).unwrap_or(limit),
            "-h" | "--help" => {
                eprintln!("usage: rv-coverage <dir> [--limit N]");
                return ExitCode::SUCCESS;
            }
            other => dir = Some(other.to_string()),
        }
    }
    let Some(dir) = dir else {
        eprintln!("usage: rv-coverage <dir> [--limit N]");
        return ExitCode::FAILURE;
    };

    // Silence panic backtraces — we catch and tally them per file instead.
    std::panic::set_hook(Box::new(|_| {}));

    let mut files = Vec::new();
    collect_rs(Path::new(&dir), &mut files);
    files.sort();

    let mut s = Stats::default();
    for path in files.iter().take(limit) {
        let Ok(src) = std::fs::read_to_string(path) else { continue };
        s.scanned += 1;
        classify(&src, path, &mut s);
    }

    report(&dir, &s);
    ExitCode::SUCCESS
}

/// Classify one file into lowered / lower-failed / parse-failed / panicked.
fn classify(src: &str, path: &Path, s: &mut Stats) {
    use ra_ap_syntax::{Edition, SourceFile};
    // 1. Grammar gate: does rust-analyzer's parser accept the file cleanly?
    //    (Same parser the front-end uses, so the gate matches the lowering path.)
    let parses = SourceFile::parse(src, Edition::Edition2021).errors().is_empty();
    if !parses {
        s.parse_failed += 1;
        return;
    }
    // 2. Lower it (in a fresh symbol table). Catch a panic so one bad file does
    //    not abort the whole sweep — and so any remaining crash bug surfaces.
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut syms = rv_core::Symbols::new();
        rv_rustfe::parse_rust(src, &mut syms).map(|_| ())
    }));
    match outcome {
        Ok(Ok(())) => s.lowered += 1,
        Ok(Err(msg)) => {
            s.lower_failed += 1;
            *s.reasons.entry(reason(&msg)).or_default() += 1;
        }
        Err(_) => {
            s.panicked += 1;
            s.panic_files.push(path.display().to_string());
        }
    }
}

/// Strip a leading `line:col: ` location from a front-end error so identical
/// causes bucket together.
fn reason(msg: &str) -> String {
    if let Some((loc, rest)) = msg.split_once(": ") {
        if !loc.is_empty() && loc.contains(':') && loc.chars().all(|c| c.is_ascii_digit() || c == ':')
        {
            return rest.to_string();
        }
    }
    msg.to_string()
}

/// Recursively gather `.rs` files under `dir` (skipping over-large ones).
fn collect_rs(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for entry in entries.flatten() {
        let path = entry.path();
        let Ok(ft) = entry.file_type() else { continue };
        if ft.is_dir() {
            collect_rs(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            let small = std::fs::metadata(&path).map(|m| m.len() <= MAX_FILE_BYTES).unwrap_or(false);
            if small {
                out.push(path);
            }
        }
    }
}

fn report(dir: &str, s: &Stats) {
    let pct = |n: usize| if s.scanned == 0 { 0.0 } else { 100.0 * n as f64 / s.scanned as f64 };
    println!("=== rv-rustfe coverage over {dir} ===");
    println!("files scanned:        {}", s.scanned);
    println!("  lowered to IR:      {:>6}  ({:.1}%)", s.lowered, pct(s.lowered));
    println!("  lower failed:       {:>6}  ({:.1}%)", s.lower_failed, pct(s.lower_failed));
    println!("  tree-sitter failed: {:>6}  ({:.1}%)", s.parse_failed, pct(s.parse_failed));
    println!("  panicked:           {:>6}  ({:.1}%)", s.panicked, pct(s.panicked));
    // Of the files the grammar accepted, how many did we lower?
    let gram_ok = s.lowered + s.lower_failed + s.panicked;
    if gram_ok > 0 {
        println!(
            "\nof {} grammar-accepted files, {:.1}% lowered",
            gram_ok,
            100.0 * s.lowered as f64 / gram_ok as f64
        );
    }

    let mut reasons: Vec<(&String, &usize)> = s.reasons.iter().collect();
    reasons.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    println!("\ntop lowering-failure reasons (file count — the first unsupported construct hit):");
    for (r, n) in reasons.iter().take(30) {
        println!("  {n:>5}  {r}");
    }
    if !s.panic_files.is_empty() {
        println!("\nPANICKED on {} file(s) — investigate:", s.panic_files.len());
        for f in s.panic_files.iter().take(10) {
            println!("  {f}");
        }
    }
}
