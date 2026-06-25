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

    // One unified pipeline over a single `.rv` file: the executable fragment is
    // verified by `rv-solve` (and runs on the VM); the proof fragment is checked by the
    // dependent kernel. `--verify` no longer selects a separate pipeline — it just means
    // "check, don't run" (it suppresses `--run`).
    if paths.len() != 1 {
        eprintln!("error: rvc takes exactly one `.rv` file");
        return ExitCode::FAILURE;
    }
    let entry_opt = if run && !verify { Some(entry.as_str()) } else { None };
    let report = match rv_driver::analyze_unified(&srcs[0], entry_opt) {
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
    if !report.obligations.is_empty() {
        println!("=== verification ({} obligations) ===", report.obligations.len());
        for o in &report.obligations {
            let mark = if o.ok() { "✓" } else { "✗" };
            println!("  {mark} {}", o.origin);
        }
    }
    if !report.proof_verified.is_empty() || !report.proof_open.is_empty() {
        println!("=== verification (kernel) ===");
        for n in &report.proof_verified {
            println!("  ✓ {n}");
        }
        for n in &report.proof_open {
            println!("  ✗ {n} (open)");
        }
    }
    if !report.proofs_erased.is_empty() || !report.runtime_defs.is_empty() {
        println!(
            "=== erasure (QTT) ===  {} proof(s) → 0 bytes, {} runtime def(s) kept",
            report.proofs_erased.len(),
            report.runtime_defs.len()
        );
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
    if let Some(run_result) = report.proof_run {
        match run_result {
            Ok(v) => println!("=== run (kernel) ===\n  {entry} = {v}"),
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

