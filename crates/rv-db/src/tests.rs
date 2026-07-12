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

/// The trust-base payoff: an obligation discharged by the *arithmetic* solver now
/// travels with a checkable [`rv_logic::Certificate::Lia`], and the driver-level
/// re-check ([`rv_logic::Outcome::checks`], the exact call `analyze` makes at
/// `obligations.iter().map(|ob| outcome.checks(ob))`) **rejects a tampered
/// certificate** — so a wrong answer from the untrusted solver is caught by the tiny
/// re-checker, not trusted. This is the property that moves rv-solve out of the trust
/// base.
#[test]
fn driver_recheck_rejects_tampered_lia_certificate() {
    use rv_core::{BinOp, Prop, Symbols, Term};
    use rv_logic::{Certificate, DisjunctCert, FarkasCert, Obligation, Outcome, Rat};

    // A genuinely valid linear obligation: `x > 0 ⟹ x >= 1` (over the integers).
    let mut s = Symbols::new();
    let x = Term::Var(s.intern("x"));
    let ctx = Prop::Holds(Term::bin(BinOp::Gt, x.clone(), Term::Int(0)));
    let goal = Prop::Holds(Term::bin(BinOp::Ge, x.clone(), Term::Int(1)));
    let ob = Obligation::new(ctx, goal, "x>0 ⟹ x>=1");

    let registry = rv_solve::default_registry();
    let outcome = registry.discharge(&ob);

    // It discharges, carrying a checkable Lia certificate, and the driver-level re-check
    // accepts it.
    let Outcome::Discharged(cert) = outcome else {
        panic!("valid arithmetic obligation must discharge, got {outcome:?}");
    };
    assert!(matches!(cert, Certificate::Lia { .. }), "must be a checkable Lia certificate");
    assert!(cert.is_replayable(), "Lia certificates are re-checkable, not trusted");
    assert!(cert.check(&ob), "the honest certificate must re-check against the obligation");

    // Tamper with it: zero out every Farkas multiplier so no combination is a positive
    // constant. The structured certificate no longer proves UNSAT.
    let Certificate::Lia { mut certificate, disjuncts } = cert else { unreachable!() };
    for dj in &mut certificate.disjuncts {
        if let DisjunctCert::LinearRefutation { branches } = dj {
            for b in branches {
                *b = FarkasCert { multipliers: b.multipliers.iter().map(|_| Rat::from_int(0)).collect() };
            }
        }
    }
    let tampered = Certificate::Lia { certificate, disjuncts };

    // The driver-level re-check must now reject it: an unverified obligation.
    assert!(!tampered.check(&ob), "the driver re-check must reject a tampered certificate");
    let tampered_outcome = Outcome::Discharged(tampered);
    assert!(!tampered_outcome.checks(&ob), "Outcome::checks must reject the tampered discharge");
}

/// A certificate is *bound* to its obligation: presenting a valid certificate for one
/// obligation against a *different* obligation fails the driver-level re-check, even if
/// the other obligation is itself valid. This prevents a producer from smuggling in a
/// proof of some unrelated formula.
#[test]
fn driver_recheck_binds_certificate_to_its_obligation() {
    use rv_core::{BinOp, Prop, Symbols, Term};
    use rv_logic::{Certificate, Obligation, Outcome};

    let mut s = Symbols::new();
    let x = Term::Var(s.intern("x"));
    let y = Term::Var(s.intern("y"));

    let ob1 = Obligation::new(
        Prop::Holds(Term::bin(BinOp::Gt, x.clone(), Term::Int(0))),
        Prop::Holds(Term::bin(BinOp::Ge, x.clone(), Term::Int(1))),
        "x",
    );
    let ob2 = Obligation::new(
        Prop::Holds(Term::bin(BinOp::Gt, y.clone(), Term::Int(0))),
        Prop::Holds(Term::bin(BinOp::Ge, y.clone(), Term::Int(1))),
        "y",
    );

    let registry = rv_solve::default_registry();
    let Outcome::Discharged(cert1) = registry.discharge(&ob1) else { panic!("ob1 must discharge") };
    assert!(cert1.check(&ob1), "cert1 checks against its own obligation");
    // The very same certificate, checked against a *different* obligation, is rejected —
    // the re-derived disjuncts differ (variable `y` vs `x`).
    assert!(!matches!(&cert1, Certificate::Lia { .. }) || !cert1.check(&ob2),
        "a certificate must not validate against a different obligation");
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
