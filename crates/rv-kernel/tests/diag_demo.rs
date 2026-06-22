//! Regression tests for elaboration diagnostics: errors name the failing declaration and
//! pretty-print the mismatched terms (not raw `{:?}` de Bruijn). Tested against a tiny
//! self-contained Rust-like object language (`mod common` + the inline relation below).
mod common;

/// A minimal typed object language to trigger diagnostics on.
const LANG: &str = "\
enum Ty  { TNat }
enum Exp { evar(Nat), enat(Nat) }
enum HasTy(e: Exp, t: Ty) -> Prop {
    TNat(n: Nat) where e == Exp::enat(n), t == Ty::TNat;
}
";

fn lang_session() -> rv_kernel::verify::Session {
    let mut s = common::session();
    s.run(LANG).expect("object language should check");
    s
}

#[test]
fn error_names_the_failing_def() {
    let mut s = lang_session();
    let err = s.run("fn oops() -> Ty { Exp::evar(Nat::Zero) }").unwrap_err();
    assert!(err.contains("fn 'oops'"), "error should name the fn: {err}");
    assert!(err.contains("Exp") && err.contains("Ty"), "should show the heads: {err}");
}

#[test]
fn error_pretty_prints_terms() {
    let mut s = lang_session();
    // TNat synthesises `enat 0`, but the goal claims `enat 1` — pretty-printed, not `{:?}`.
    let err = s
        .run("fn oops2() -> HasTy(Exp::enat(Nat::Succ(Nat::Zero)), Ty::TNat) { HasTy::TNat(Nat::Zero) }")
        .unwrap_err();
    assert!(err.contains("Nat.Succ Nat.Zero"), "should pretty-print the term: {err}");
    assert!(!err.contains("Const("), "should not leak raw Debug: {err}");
}

#[test]
fn semantic_errors_carry_the_declaration_position() {
    let mut s = lang_session();
    // The bad `fn` is on the third line; the type-mismatch error must be prefixed `3:`.
    let err = s
        .run(
            "fn fine1() -> Ty { Ty::TNat }\n\
             fn fine2() -> Ty { Ty::TNat }\n\
             fn bad() -> Ty { Exp::evar(Nat::Zero) }",
        )
        .unwrap_err();
    assert!(err.starts_with("3:"), "want a 3:col position prefix, got: {err}");
    assert!(err.contains("fn 'bad'"), "should still name the fn: {err}");
}

#[test]
fn error_points_a_caret_at_the_offending_subterm() {
    let mut s = lang_session();
    // The offending sub-term is `Exp::evar(Nat::Zero)`; the error should carry a caret line
    // underlining it (sub-term granularity, not just the declaration).
    let err = s.run("fn bad() -> Ty { Exp::evar(Nat::Zero) }").unwrap_err();
    assert!(err.contains('^'), "should draw a caret under the sub-term: {err}");
    assert!(
        err.contains("Exp::evar(Nat::Zero)"),
        "the underlined source line should show the offending sub-term: {err}"
    );
}
