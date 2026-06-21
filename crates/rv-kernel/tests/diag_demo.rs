//! Regression tests for the improved elaboration diagnostics: errors name the failing
//! declaration and pretty-print the mismatched terms (instead of raw `{:?}` de Bruijn).
use rv_kernel::systemf;

#[test]
fn error_names_the_failing_def() {
    let mut s = systemf::safety_session().unwrap();
    let err = s.run("def oops : FTy := FExp.evar(Nat.zero)").unwrap_err();
    assert!(err.contains("def 'oops'"), "error should name the def: {err}");
    assert!(err.contains("FExp") && err.contains("FTy"), "should show the heads: {err}");
}

#[test]
fn error_pretty_prints_terms() {
    let mut s = systemf::safety_session().unwrap();
    // ftnat synthesises `enat 0`, but the goal claims `enat 1` — pretty-printed, not `{:?}`.
    let err = s
        .run(
            "def oops2 : FHasTy FCtx.nil (FExp.enat (Nat.succ Nat.zero)) FTy.tnat := \
               FHasTy.ftnat FCtx.nil Nat.zero",
        )
        .unwrap_err();
    assert!(err.contains("Nat.succ Nat.zero"), "should pretty-print the term: {err}");
    assert!(!err.contains("Const("), "should not leak raw Debug: {err}");
}
