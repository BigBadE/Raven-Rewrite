//! Incrementality tests: prove salsa genuinely drives & memoizes the pipeline.
use super::*;
use salsa::Setter;
use std::sync::{Arc, Mutex};

const RECIP_OK: &str = include_str!("fixtures/tests_recip_ok.rv");

const RECIP_BAD: &str = include_str!("fixtures/tests_recip_bad.rv");

/// Mutating the `SourceProgram` input to a *different* program changes the
/// memoized result — the correctness-across-an-input-change requirement.
#[test]
fn recompute_after_mutation() {
    let mut db = Database::default();
    let src = SourceProgram::new(&db, RECIP_OK.to_string());

    let before = analyze(&db, src);
    assert!(matches!(&before, AnalysisResult::Analyzed(a) if a.all_verified));

    src.set_text(&mut db).to(RECIP_BAD.to_string());
    let after = analyze(&db, src);
    match &after {
        AnalysisResult::Analyzed(a) => {
            assert!(!a.all_verified, "unguarded division must not verify: {a:?}");
            assert!(a.obligations.iter().any(|o| !o.ok));
        }
        other => panic!("expected analyzed, got {other:?}"),
    }
    assert_ne!(before, after, "result must change when the source changes");
}

/// Memoization: re-running `analyze` with the SAME input executes NO tracked
/// function the second time (everything served from cache). With the input
/// changed, the tracked functions DO execute again.
#[test]
fn unchanged_input_is_not_recomputed() {
    let log = Arc::new(Mutex::new(Vec::<String>::new()));
    let db = Database::with_logger(log.clone());
    let src = SourceProgram::new(&db, RECIP_OK.to_string());

    // First run: the three tracked queries execute.
    let _ = analyze(&db, src);
    let first_executions = log.lock().unwrap().len();
    assert!(first_executions >= 3, "first run should execute the tracked queries, saw {first_executions}");

    // Second run, identical input: nothing should execute.
    log.lock().unwrap().clear();
    let _ = analyze(&db, src);
    let second_executions = log.lock().unwrap().len();
    assert_eq!(second_executions, 0, "re-running with unchanged input must be fully memoized");
}

/// The `compile_source` convenience entry behaves like the old verify path.
#[test]
fn compile_source_entry() {
    assert!(matches!(compile_source(RECIP_OK), AnalysisResult::Analyzed(a) if a.all_verified));
    assert!(matches!(compile_source(RECIP_BAD), AnalysisResult::Analyzed(a) if !a.all_verified));
}

/// `compile_and_run` reuses the memoized elaboration and runs the entry point.
#[test]
fn compile_and_run_executes() {
    let src = include_str!("fixtures/tests_src1.rv");
    let (analysis, run) = compile_and_run(src, Some("main"));
    assert!(matches!(analysis, AnalysisResult::Analyzed(a) if a.all_verified));
    assert_eq!(run, Some(Ok(rv_vm::Value::Int(5))));
}

/// An executable entry is available only after the complete verification result
/// succeeds.  Running a program with an unresolved safety obligation would make
/// `rvc` two different languages: one for checking and one for execution.
#[test]
fn compile_and_run_refuses_unverified_program() {
    let (analysis, run) = compile_and_run(RECIP_BAD, Some("main"));
    assert!(matches!(analysis, AnalysisResult::Analyzed(a) if !a.all_verified));
    assert_eq!(run, None);
}
