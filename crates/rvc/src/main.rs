//! `rvc` — the raven-v3 compiler CLI.
//!
//! Usage: `rvc <file.rv | file.rs | file.rvk ...> [--run] [--entry NAME]`
//!   parse → lower → infer → verify (always), then optionally compile + run.
//!   Multiple `.rs` files are compiled together as one program (modules).
//!   A `.rvk` file is a **Raven kernel-surface** program: it is elaborated and
//!   verified through the dependent-type-theory kernel (`fn … requires/ensures`,
//!   `match`, dependent types), with the standard prelude preloaded.
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut paths: Vec<String> = Vec::new();
    let mut run = false;
    let mut entry = "main".to_string();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--run" => run = true,
            "--entry" => {
                if let Some(e) = it.next() {
                    entry = e.clone();
                }
            }
            "-h" | "--help" => {
                eprintln!("usage: rvc <file.rv | file.rs ...> [--run] [--entry NAME]");
                return ExitCode::SUCCESS;
            }
            other => paths.push(other.to_string()),
        }
    }

    if paths.is_empty() {
        eprintln!("usage: rvc <file.rv | file.rs ...> [--run] [--entry NAME]");
        return ExitCode::FAILURE;
    }
    // Read every input file.
    let mut srcs = Vec::with_capacity(paths.len());
    for path in &paths {
        match std::fs::read_to_string(path) {
            Ok(s) => srcs.push(s),
            Err(e) => {
                eprintln!("cannot read {path}: {e}");
                return ExitCode::FAILURE;
            }
        }
    }

    // A `.rvk` file goes through the dependent-type-theory kernel (verified-Raven).
    if paths.iter().any(|p| p.ends_with(".rvk")) {
        let entry_opt = if run { Some(entry.as_str()) } else { None };
        return run_kernel(&paths, &srcs, entry_opt);
    }

    // `.rs` files go through the real-Rust (tree-sitter) frontend (multiple files
    // compile together as one program); a single `.rv` file goes through the
    // toy/salsa frontend.
    let entry_opt = if run { Some(entry.as_str()) } else { None };
    let any_rust = paths.iter().any(|p| p.ends_with(".rs"));
    let pipeline = if any_rust {
        let refs: Vec<&str> = srcs.iter().map(|s| s.as_str()).collect();
        rv_driver::run_rust_modules_pipeline(&refs, entry_opt)
    } else {
        rv_driver::run_pipeline(&srcs[0], entry_opt)
    };
    let report = match pipeline {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::FAILURE;
        }
    };

    if !report.borrow_errors.is_empty() {
        println!("=== borrow check ===");
        for e in &report.borrow_errors {
            println!("  ✗ {e}");
        }
    }
    println!("=== verification ({} obligations) ===", report.obligations.len());
    for o in &report.obligations {
        let mark = if o.ok() { "✓" } else { "✗" };
        println!("  {mark} {}", o.origin);
    }
    let verified = report.all_verified();
    println!(
        "{}",
        if verified {
            "VERIFIED".to_string()
        } else {
            format!("NOT VERIFIED ({} failed)", report.num_failed())
        }
    );

    if let Some(run_result) = report.run {
        match run_result {
            Ok(v) => println!("=== run ===\n  {entry}() = {v:?}"),
            Err(e) => {
                eprintln!("runtime error: {e}");
                return ExitCode::FAILURE;
            }
        }
    }

    if verified {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// Verify (and optionally run) `.rvk` Raven kernel-surface files through the
/// dependent-type-theory kernel. The standard prelude is preloaded, so programs may use
/// `Bool`/`Nat`/`List`/… freely.
fn run_kernel(paths: &[String], srcs: &[String], entry: Option<&str>) -> ExitCode {
    if paths.len() != 1 {
        eprintln!("error: exactly one .rvk file is supported at a time");
        return ExitCode::FAILURE;
    }
    let report = match rv_driver::run_raven(&srcs[0], true, entry) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::FAILURE;
        }
    };
    println!("=== verification (kernel) ===");
    for n in &report.verified {
        println!("  ✓ {n}");
    }
    for n in &report.open {
        println!("  ✗ {n} (open)");
    }
    let verified = report.all_verified();
    println!("{}", if verified { "VERIFIED" } else { "NOT VERIFIED" });
    if let Some(run_result) = &report.run {
        match run_result {
            Ok(v) => println!("=== run ===\n  {} = {v}", entry.unwrap_or("?")),
            Err(e) => {
                eprintln!("runtime error: {e}");
                return ExitCode::FAILURE;
            }
        }
    }
    if verified {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
