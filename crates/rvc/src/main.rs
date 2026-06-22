//! `rvc` — the raven-v3 compiler CLI.
//!
//! Usage: `rvc <file.rv> [--run] [--verify] [--entry NAME]`
//!   The default path lowers the executable fragment (parse → lower → infer →
//!   verify), then optionally compiles + runs it on the VM.
//!   `--verify` instead checks the file through the dependent-type-theory kernel
//!   (`fn … requires/ensures`, `match`, dependent types, proofs-as-functions),
//!   with the logic prelude preloaded — the verified-Raven path.
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut paths: Vec<String> = Vec::new();
    let mut run = false;
    let mut verify = false;
    let mut entry = "main".to_string();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--run" => run = true,
            "--verify" => verify = true,
            "--entry" => {
                if let Some(e) = it.next() {
                    entry = e.clone();
                }
            }
            "-h" | "--help" => {
                eprintln!("usage: rvc <file.rv> [--run] [--verify] [--entry NAME]");
                return ExitCode::SUCCESS;
            }
            other => paths.push(other.to_string()),
        }
    }

    if paths.is_empty() {
        eprintln!("usage: rvc <file.rv> [--run] [--verify] [--entry NAME]");
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

    // `--verify` checks a `.rv` program through the dependent kernel (logic prelude
    // only — the file brings its own data + proofs): the verified-Raven path.
    if verify {
        if paths.len() != 1 {
            eprintln!("error: --verify takes exactly one file");
            return ExitCode::FAILURE;
        }
        let entry_opt = if run { Some(entry.as_str()) } else { None };
        return verify_rv_file(&srcs[0], entry_opt);
    }

    // The default executable path: a single `.rv` file through the Raven pipeline.
    if paths.len() != 1 {
        eprintln!("error: the executable path takes exactly one `.rv` file (use --verify for proofs)");
        return ExitCode::FAILURE;
    }
    let entry_opt = if run { Some(entry.as_str()) } else { None };
    let pipeline = rv_driver::run_pipeline(&srcs[0], entry_opt);
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
/// Verify a unified `.rv` program (data + proofs) through the dependent kernel.
fn verify_rv_file(src: &str, entry: Option<&str>) -> ExitCode {
    let report = match rv_driver::verify_rv(src, entry) {
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

