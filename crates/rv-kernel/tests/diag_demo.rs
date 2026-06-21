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

#[test]
fn semantic_errors_carry_the_declaration_position() {
    let mut s = systemf::safety_session().unwrap();
    // The bad `def` is on the third line; the type-mismatch error must be prefixed `3:`.
    let err = s
        .run(
            "def fine1 : FTy := FTy.tnat\n\
             def fine2 : FTy := FTy.tnat\n\
             def bad : FTy := FExp.evar(Nat.zero)",
        )
        .unwrap_err();
    assert!(err.starts_with("3:"), "want a 3:col position prefix, got: {err}");
    assert!(err.contains("def 'bad'"), "should still name the def: {err}");
}

#[test]
fn error_points_a_caret_at_the_offending_subterm() {
    let mut s = systemf::safety_session().unwrap();
    // The offending sub-term is the application `FExp.evar(Nat.zero)`; the error should
    // carry a caret line underlining it (sub-term granularity, not just the declaration).
    let err = s
        .run("def bad : FTy := FExp.evar(Nat.zero)")
        .unwrap_err();
    assert!(err.contains('^'), "should draw a caret under the sub-term: {err}");
    assert!(
        err.contains("FExp.evar(Nat.zero)"),
        "the underlined source line should show the offending sub-term: {err}"
    );
    // The caret's reported position points into the def body (column > 1), not the line start.
    assert!(err.contains("  at 1:18"), "caret should locate the sub-term at 1:18: {err}");
}
