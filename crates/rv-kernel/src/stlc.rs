//! **A verified type checker for a simply-typed λ-calculus** — the type checker of
//! [`crate::typedlang`] grown all the way up to **function types, λ-abstraction, and
//! application**, on top of de Bruijn variables, a `let` binder, and a typing context.
//!
//! This is the real thing: an analysis (a type checker) over a language with binders and
//! a structured (recursive) type grammar, with a machine-checked soundness theorem against
//! an independent typing relation — exactly the shape the kernel-and-core endgame uses for
//! the borrow checker and trait solver. Everything is verified Raven checked by the kernel:
//!
//!  * **Spec** — the typing relation `HasTy : Ctx → Exp → Ty → Prop` (with `tlam`/`tapp`
//!    for functions) and the de Bruijn lookup relation `Lookup : Ctx → Nat → Ty → Prop`.
//!  * **Implementation** — the checker as curried, context-threading Raven functions
//!    `synth : Exp → Ctx → Ty` and `ok : Exp → Ctx → Bool`, with a **recursive** type
//!    decider `tyeq` (arrows compared structurally) and arrow destructors
//!    `isArrow`/`domOf`/`codOf`.
//!  * **Bridge** — `tyeq_sound` (structural induction on the recursive type), the variable
//!    lemma `lookup_sound`, arrow inversion `arrow_inv`, and the soundness theorem
//!    ```text
//!    ok_sound : ∀ e Γ, ok e Γ = true → HasTy Γ e (synth e Γ),
//!    ```
//!    whose `eapp` case is the heart of it: it inverts the synthesized function type to an
//!    arrow, rewrites its domain to the argument's type, and applies `tapp`.

use crate::verify::Session;

/// Logic + booleans + naturals + the (recursive) object types with a decidable equality
/// and arrow destructors + the typing context with lookup/scope and the `Lookup` relation.
pub const PRELUDE: &str = include_str!("raven/stlc_prelude.rvk");

/// The simply-typed λ-calculus (`Exp` with variables, `let`, λ, and application), the
/// typing relation `HasTy`, the checker, and the soundness theorem.
pub const LANG: &str = include_str!("raven/stlc_lang.rvk");

/// The **operational semantics**: a call-by-value, substitution-based small-step
/// evaluator (`isValue`, de Bruijn `shift`/`subst`, `step`, and a fuel-driven `run`).
/// This is what lets the language *run* — concrete typed programs reduce to values, and
/// the kernel computes the result. (Type *safety* relating this to the checker — progress
/// + preservation — is the next layer.)
pub const DYNAMICS: &str = include_str!("raven/stlc_dynamics.rvk");

/// A session with the prelude and the simply-typed λ-calculus + checker + soundness all
/// loaded and kernel-checked.
pub fn session() -> Result<Session, String> {
    let mut s = Session::new();
    s.run(PRELUDE)?;
    s.run(LANG)?;
    Ok(s)
}

/// A session that additionally loads the [`DYNAMICS`] (the evaluator), so programs can be
/// *run*, not just type-checked.
pub fn runnable_session() -> Result<Session, String> {
    let mut s = session()?;
    s.run(DYNAMICS)?;
    Ok(s)
}

/// **Type-safety scaffolding**: the structural predicates, value/term inversions, and the
/// **canonical forms** lemmas that `progress` is built from — all verified Raven.
///
/// Canonical forms (`canon_arrow`/`canon_nat`/`canon_bool`) say a well-typed *value* has
/// the shape its type dictates. They're stated with the value/type side-conditions as
/// hypotheses in the *return type* (so each constructor case specialises them via the
/// motive) — that sidesteps needing dependent inversion on concrete indices.
pub const SAFETY_SCAFFOLD: &str = include_str!("raven/stlc_safety_scaffold.rvk");

/// **Step-characterization lemmas**: how `step` behaves on each non-value term, in terms
/// of stepping its reducible subterm (congruence) or producing a redex result. Each splits
/// on a single operand (values are concretised by canonical forms before these are used),
/// so each is an 8-way (or fewer) case analysis closed by `isSome_omap` or by computation.
pub const STEP_LEMMAS: &str = include_str!("raven/stlc_step_lemmas.rvk");

/// **Progress** — *well-typed closed programs don't get stuck*: a closed (`isNil Γ`)
/// well-typed term is either a value or can take a step. Proved by induction on the typing
/// derivation; each non-value case concretises its value subterms with canonical forms and
/// concludes "it steps" from the step lemmas + the induction hypotheses.
pub const PROGRESS: &str = include_str!("raven/stlc_progress.rvk");

/// A session that additionally loads the type-safety scaffolding ([`SAFETY_SCAFFOLD`]), the
/// step-characterization lemmas ([`STEP_LEMMAS`]), and the [`PROGRESS`] theorem.
pub fn safety_session() -> Result<Session, String> {
    let mut s = runnable_session()?;
    s.run(SAFETY_SCAFFOLD)?;
    s.run(STEP_LEMMAS)?;
    s.run(PROGRESS)?;
    Ok(s)
}

/// **Weakening foundation** for preservation: context insertion (`insertCtx`) and the
/// lookup-weakening lemma (a binding inserted anywhere in the context preserves every
/// existing lookup, at the shifted index). Proved by induction on the `Lookup` derivation;
/// the recursive `shiftIdx`'s laws hold definitionally, so the index arithmetic just
/// computes.
pub const PRESERVATION: &str = include_str!("raven/stlc_preservation.rvk");

/// The preservation theorem proper, plus per-redex standalone lemmas (split from
/// [`PRESERVATION`] so it can be iterated/diagnosed separately).
pub const PRESERVATION_THM: &str = include_str!("raven/stlc_preservation_thm.rvk");

/// A session that additionally loads the [`PRESERVATION`] development (weakening so far).
pub fn preservation_session() -> Result<Session, String> {
    let mut s = safety_session()?;
    s.run(PRESERVATION)?;
    s.run(PRESERVATION_THM)?;
    Ok(s)
}

/// A *lighter* session for iterating on the preservation development: it skips the slow
/// `STEP_LEMMAS` + `PROGRESS` consts (which preservation does not depend on), loading only
/// the evaluator, the safety scaffolding's extractors, and the preservation development.
pub fn preservation_only_session() -> Result<Session, String> {
    let mut s = runnable_session()?;
    s.run(SAFETY_SCAFFOLD)?;
    s.run(PRESERVATION)?;
    s.run(PRESERVATION_THM)?;
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A `Nat` literal as a `succ`/`zero` chain (for building object-language terms in tests).
    fn nat(n: u64) -> String {
        let mut s = String::from("Nat.zero");
        for _ in 0..n {
            s = format!("Nat.succ({s})");
        }
        s
    }

    /// The whole development — recursive types, the checker, and the soundness theorem
    /// (including the `eapp` case) — elaborates and is kernel-checked.
    #[test]
    fn lang_and_soundness_check() {
        let s = session().expect("prelude + simply-typed language + soundness should check");
        for n in [
            "Exp", "Ty", "Lookup", "HasTy", "tyeq", "tyeq_sound", "arrow_inv", "synth", "ok",
            "ok_sound", "synth_complete", "ok_complete", "ok_false_not_welltyped",
        ] {
            assert!(s.k.env().contains(n), "missing '{n}'");
        }
    }

    /// The **type-safety scaffolding** (canonical forms + inversions + helpers) and the
    /// **progress** theorem elaborate and are kernel-checked.
    #[test]
    fn safety_scaffold_check() {
        let s = safety_session().expect("safety scaffolding + progress should check");
        for n in [
            "canon_arrow", "canon_nat", "canon_bool", "natlit_inv", "boollit_inv", "lam_inv",
            "nilLookupFalse", "bool_cases", "orB_false_left", "isSome_omap", "progress",
        ] {
            assert!(s.k.env().contains(n), "missing '{n}'");
        }
    }

    /// The **weakening foundation** (`insertCtx`, `lookup_weaken`) — and the refactored
    /// `shiftIdx` — elaborate and are kernel-checked.
    #[test]
    fn weakening_foundation_check() {
        let s = preservation_session().expect("weakening + substitution + preservation should check");
        for n in [
            "shiftIdx", "insertCtx", "lookup_weaken", "HasTy_weaken", "applySub", "liftSub_respects",
            "subst_lemma", "subst_preserves", "Step", "preservation",
        ] {
            assert!(s.k.env().contains(n), "missing '{n}'");
        }
    }

    /// **Preservation in action.** `(λx:tnat. x) 0` β-reduces (via `Step.s_beta`); applying
    /// `preservation` transports its typing across the step, yielding a kernel-checked proof
    /// that the reduct is still well-typed at the same type.
    #[test]
    fn preservation_applies_to_a_step() {
        let mut s = preservation_session().unwrap();
        s.run("def prog : Exp := Exp.eapp(Exp.elam(Ty.tnat, Exp.evar(Nat.zero)), Exp.enat(Nat.zero))").unwrap();
        s.run(
            "def the_step : Step prog (subst(Exp.evar(Nat.zero))(Nat.zero)(Exp.enat(Nat.zero))) := \
               Step.s_beta Ty.tnat (Exp.evar(Nat.zero)) (Exp.enat(Nat.zero))",
        )
        .unwrap();
        s.run(
            "def preserved : HasTy Ctx.nil (subst(Exp.evar(Nat.zero))(Nat.zero)(Exp.enat(Nat.zero))) (synth(prog)(Ctx.nil)) := \
               preservation prog (subst(Exp.evar(Nat.zero))(Nat.zero)(Exp.enat(Nat.zero))) the_step \
                 Ctx.nil (synth(prog)(Ctx.nil)) (ok_sound(prog)(Ctx.nil)(Eq.refl.{1} Bool Bool.true))",
        )
        .expect("preservation should transport the typing across the β-step");
        assert!(s.k.env().contains("preserved"));
    }

    /// **Progress in action.** Applying `progress` to a concrete closed well-typed term
    /// (`(λx:tnat. x+1) 2`) yields a kernel-checked proof that it is a value or can step —
    /// i.e. it is not stuck. The certificate is just the typing derivation (`ok_sound … refl`).
    #[test]
    fn progress_applies_to_closed_program() {
        let mut s = safety_session().unwrap();
        s.run(
            "def p : Exp := \
               Exp.eapp(Exp.elam(Ty.tnat, Exp.eadd(Exp.evar(Nat.zero), Exp.enat(Nat.succ(Nat.zero)))), \
                        Exp.enat(Nat.succ(Nat.succ(Nat.zero))))",
        )
        .unwrap();
        s.run(
            "def p_not_stuck : Eq.{1} Bool (orB(isValue(p))(canStep(p))) Bool.true := \
               progress Ctx.nil p (synth(p)(Ctx.nil)) \
                 (ok_sound(p)(Ctx.nil)(Eq.refl.{1} Bool Bool.true)) \
                 (Eq.refl.{1} Bool Bool.true)",
        )
        .expect("progress should certify the closed program is not stuck");
        assert!(s.k.env().contains("p_not_stuck"));
    }

    /// The **evaluator** elaborates and is kernel-checked.
    #[test]
    fn dynamics_check() {
        let s = runnable_session().expect("the evaluator should check");
        for n in ["isValue", "shift", "subst", "step", "run", "OExp"] {
            assert!(s.k.env().contains(n), "missing '{n}'");
        }
    }

    /// **Running code.** Typed programs reduce to values, computed by the kernel:
    ///   * `(λx:tnat. x + 1) 2  ⇒  3`           (β + the `eadd` primitive)
    ///   * `if true then 7 else 0  ⇒  7`        (branch selection)
    ///   * `let x = 4 in x + x  ⇒  8`           (a binder, a variable used twice)
    #[test]
    fn programs_run_to_values() {
        let mut s = runnable_session().unwrap();
        // (λx:tnat. x + 1) 2
        s.run(
            "def p1 : Exp := \
               Exp.eapp(Exp.elam(Ty.tnat, Exp.eadd(Exp.evar(Nat.zero), Exp.enat(Nat.succ(Nat.zero)))), \
                        Exp.enat(Nat.succ(Nat.succ(Nat.zero))))",
        )
        .unwrap();
        s.run("def r1 : Exp := run(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))))(p1)").unwrap();
        // if true then 7 else 0
        s.run(
            "def p2 : Exp := Exp.eif(Exp.ebool(Bool.true), \
               Exp.enat(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))))))), \
               Exp.enat(Nat.zero))",
        )
        .unwrap();
        s.run("def r2 : Exp := run(Nat.succ(Nat.succ(Nat.zero)))(p2)").unwrap();
        // let x = 4 in x + x
        s.run(
            "def p3 : Exp := Exp.elet(Exp.enat(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))), \
               Exp.eadd(Exp.evar(Nat.zero), Exp.evar(Nat.zero)))",
        )
        .unwrap();
        s.run("def r3 : Exp := run(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))(p3)").unwrap();
        assert_eq!(s.run_entry("r1").unwrap(), "Exp.enat 3", "(λx. x+1) 2 = 3");
        assert_eq!(s.run_entry("r2").unwrap(), "Exp.enat 7", "if true then 7 else 0 = 7");
        assert_eq!(s.run_entry("r3").unwrap(), "Exp.enat 8", "let x=4 in x+x = 8");
    }

    /// **Conditionals type-check.** `if true then 0 else 1` synthesizes `tnat`; a
    /// non-boolean condition (`if 0 then …`) and mismatched branches (`if true then 0 else
    /// true`) are both rejected.
    #[test]
    fn checker_handles_conditionals() {
        let mut s = session().unwrap();
        s.run(
            "def good : Exp := \
               Exp.eif(Exp.ebool(Bool.true), Exp.enat(Nat.zero), Exp.enat(Nat.succ(Nat.zero)))",
        )
        .unwrap();
        s.run("def good_ty : Ty := synth(good)(Ctx.nil)").unwrap();
        s.run("def good_ok : Bool := ok(good)(Ctx.nil)").unwrap();
        // condition isn't a bool
        s.run("def badcond : Bool := ok(Exp.eif(Exp.enat(Nat.zero), Exp.enat(Nat.zero), Exp.enat(Nat.zero)))(Ctx.nil)").unwrap();
        // branches disagree
        s.run("def badbranch : Bool := ok(Exp.eif(Exp.ebool(Bool.true), Exp.enat(Nat.zero), Exp.ebool(Bool.false)))(Ctx.nil)").unwrap();
        assert_eq!(s.run_entry("good_ty").unwrap(), "Ty.tnat");
        assert_eq!(s.run_entry("good_ok").unwrap(), "Bool.true");
        assert_eq!(s.run_entry("badcond").unwrap(), "Bool.false", "non-boolean condition");
        assert_eq!(s.run_entry("badbranch").unwrap(), "Bool.false", "branch types disagree");
    }

    /// **The checker DECIDES typability** (soundness + completeness). A rejected term is
    /// genuinely untypable: `ok_false_not_welltyped` turns `ok e = false` into a refutation
    /// `HasTy Γ e T → False`, for any context and type.
    #[test]
    fn rejected_term_is_genuinely_untypable() {
        let mut s = session().unwrap();
        // `0 true` — applying a non-function.
        s.run("def bad : Exp := Exp.eapp(Exp.enat(Nat.zero), Exp.ebool(Bool.true))").unwrap();
        s.run(
            "def bad_untypable (T : Ty) : HasTy Ctx.nil bad T -> False := \
               ok_false_not_welltyped Ctx.nil bad T (Eq.refl.{1} Bool Bool.false)",
        )
        .expect("a rejected term must be provably untypable");
        assert!(s.k.env().contains("bad_untypable"));
    }

    /// The checker handles `let` and variables: `let x = 0 in x + 1` synthesizes `tnat`.
    #[test]
    fn checker_accepts_let_with_variable() {
        let mut s = session().unwrap();
        s.run(
            "def prog : Exp := \
               Exp.elet(Exp.enat(Nat.zero), \
                        Exp.eadd(Exp.evar(Nat.zero), Exp.enat(Nat.succ(Nat.zero))))",
        )
        .unwrap();
        s.run("def prog_ty : Ty := synth(prog)(Ctx.nil)").unwrap();
        s.run("def prog_ok : Bool := ok(prog)(Ctx.nil)").unwrap();
        assert_eq!(s.run_entry("prog_ty").unwrap(), "Ty.tnat");
        assert_eq!(s.run_entry("prog_ok").unwrap(), "Bool.true");
    }

    /// **λ-abstraction and application type-check.** `(λx:tnat. x + 1) 0` is well typed and
    /// synthesizes `tnat`; the lambda itself synthesizes the arrow `tnat → tnat`.
    #[test]
    fn checker_accepts_lambda_application() {
        let mut s = session().unwrap();
        // λ(x:tnat). x + 1
        s.run(
            "def idfun : Exp := \
               Exp.elam(Ty.tnat, Exp.eadd(Exp.evar(Nat.zero), Exp.enat(Nat.succ(Nat.zero))))",
        )
        .unwrap();
        s.run("def fun_ty : Ty := synth(idfun)(Ctx.nil)").unwrap();
        s.run("def applied : Exp := Exp.eapp(idfun, Exp.enat(Nat.zero))").unwrap();
        s.run("def applied_ty : Ty := synth(applied)(Ctx.nil)").unwrap();
        s.run("def applied_ok : Bool := ok(applied)(Ctx.nil)").unwrap();
        assert_eq!(s.run_entry("fun_ty").unwrap(), "Ty.tarrow Ty.tnat Ty.tnat");
        assert_eq!(s.run_entry("applied_ty").unwrap(), "Ty.tnat");
        assert_eq!(s.run_entry("applied_ok").unwrap(), "Bool.true");
    }

    /// **Application type errors are caught**: applying a non-function (`0 0`) and a
    /// domain mismatch (`(λx:tnat. x) true`) both make `ok` reduce to `false`.
    #[test]
    fn checker_rejects_application_errors() {
        let mut s = session().unwrap();
        // 0 applied to 0 — the "function" isn't an arrow.
        s.run("def notfun : Bool := ok(Exp.eapp(Exp.enat(Nat.zero), Exp.enat(Nat.zero)))(Ctx.nil)").unwrap();
        // (λx:tnat. x) true — argument type tbool ≠ domain tnat.
        s.run(
            "def mismatch : Bool := \
               ok(Exp.eapp(Exp.elam(Ty.tnat, Exp.evar(Nat.zero)), Exp.ebool(Bool.true)))(Ctx.nil)",
        )
        .unwrap();
        assert_eq!(s.run_entry("notfun").unwrap(), "Bool.false", "applying a non-function");
        assert_eq!(s.run_entry("mismatch").unwrap(), "Bool.false", "argument/domain type mismatch");
    }

    /// **Reflective typing of a higher-order term.** `(λx:tnat. x + 1) 0` is certified by
    /// running the checker: `ok_sound applied nil refl` produces the `HasTy` derivation
    /// (with its `tapp`/`tlam`/`tadd`/`tvar` steps) — a real proof, by computation.
    #[test]
    fn reflective_derivation_for_application() {
        let mut s = session().unwrap();
        s.run(
            "def applied : Exp := \
               Exp.eapp(Exp.elam(Ty.tnat, Exp.eadd(Exp.evar(Nat.zero), Exp.enat(Nat.succ(Nat.zero)))), \
                        Exp.enat(Nat.zero))",
        )
        .unwrap();
        s.run(
            "def derivation : HasTy Ctx.nil applied (synth(applied)(Ctx.nil)) := \
               ok_sound(applied)(Ctx.nil)(Eq.refl.{1} Bool Bool.true)",
        )
        .expect("reflective derivation for an application should check");
        assert!(s.k.env().contains("derivation"));
    }

    /// **`fix`/recursion type-checks and runs (Tier 2).** A genuinely self-referential
    /// function — `fix self : nat→nat. λx:nat. if true then x+1 else self x` — type-checks
    /// (synthesizes `nat → nat`), and applied to `5` it *runs to 6*: the `fix` unrolls, the
    /// λ β-reduces, and the recursive call sits in the dead `else` branch (CBV picks `then`).
    #[test]
    fn fix_typechecks_and_runs() {
        let mut s = runnable_session().unwrap();
        // self is de Bruijn 1 inside the λ (efix binds 0, the λ pushes it to 1); x is 0.
        let rec = format!(
            "Exp.efix(Ty.tarrow(Ty.tnat, Ty.tnat), \
               Exp.elam(Ty.tnat, \
                 Exp.eif(Exp.ebool(Bool.true), \
                         Exp.eadd(Exp.evar({zero}), Exp.enat({one})), \
                         Exp.eapp(Exp.evar({one_idx}), Exp.evar({zero})))))",
            zero = nat(0),
            one = nat(1),
            one_idx = nat(1),
        );
        s.run(&format!("def rec : Exp := {rec}")).unwrap();
        s.run("def rec_ty : Ty := synth(rec)(Ctx.nil)").unwrap();
        s.run("def rec_ok : Bool := ok(rec)(Ctx.nil)").unwrap();
        s.run(&format!("def applied : Exp := Exp.eapp(rec, Exp.enat({}))", nat(5))).unwrap();
        s.run("def applied_ok : Bool := ok(applied)(Ctx.nil)").unwrap();
        s.run(&format!("def result : Exp := run({})(applied)", nat(10))).unwrap();
        assert_eq!(s.run_entry("rec_ty").unwrap(), "Ty.tarrow Ty.tnat Ty.tnat", "fix synthesizes nat→nat");
        assert_eq!(s.run_entry("rec_ok").unwrap(), "Bool.true", "the recursive function is well typed");
        assert_eq!(s.run_entry("applied_ok").unwrap(), "Bool.true");
        assert_eq!(s.run_entry("result").unwrap(), "Exp.enat 6", "(fix …) 5 = 6");
    }

    /// **Type safety extends to `fix`.** Progress: `fix nat. 7` is not stuck (it unrolls).
    /// Preservation: the `s_fix` unrolling step preserves the type — the unrolled body is
    /// still well typed at the same type. Both kernel-checked, with `efix` in the language.
    #[test]
    fn fix_is_type_safe() {
        let mut s = preservation_session().unwrap();
        // A trivial fixpoint whose body ignores the recursive binding: fix self:nat. 7.
        s.run(&format!("def f7 : Exp := Exp.efix(Ty.tnat, Exp.enat({}))", nat(7))).unwrap();
        // Progress: the closed fixpoint is a value or steps.
        s.run(
            "def f7_not_stuck : Eq.{1} Bool (orB(isValue(f7))(canStep(f7))) Bool.true := \
               progress Ctx.nil f7 (synth(f7)(Ctx.nil)) \
                 (ok_sound(f7)(Ctx.nil)(Eq.refl.{1} Bool Bool.true)) (Eq.refl.{1} Bool Bool.true)",
        )
        .expect("progress should certify the fixpoint is not stuck");
        // Preservation: the unrolling step preserves typing.
        s.run(
            "def f7_step : Step f7 (subst(Exp.enat(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))))) (Nat.zero) (f7)) := \
               Step.s_fix Ty.tnat (Exp.enat(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))))))))",
        )
        .unwrap();
        s.run(
            "def f7_preserved : HasTy Ctx.nil (subst(Exp.enat(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))))) (Nat.zero) (f7)) (synth(f7)(Ctx.nil)) := \
               preservation f7 (subst(Exp.enat(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))))) (Nat.zero) (f7)) f7_step \
                 Ctx.nil (synth(f7)(Ctx.nil)) (ok_sound(f7)(Ctx.nil)(Eq.refl.{1} Bool Bool.true))",
        )
        .expect("preservation should transport typing across the fix-unroll step");
        assert!(s.k.env().contains("f7_not_stuck"));
        assert!(s.k.env().contains("f7_preserved"));
    }

    /// **Products (pairs) type-check and run (Tier 2).** `fst (1+2, true)` synthesizes `nat`
    /// and runs to `3`; `snd (1, false)` synthesizes `bool` and runs to `false`. The verified
    /// checker computes the component types; the evaluator projects (pairs are lazy values).
    #[test]
    fn products_typecheck_and_run() {
        let mut s = runnable_session().unwrap();
        // fst ((1+2), true)
        s.run(&format!(
            "def p1 : Exp := Exp.efst(Exp.epair(Exp.eadd(Exp.enat({}), Exp.enat({})), Exp.ebool(Bool.true)))",
            nat(1), nat(2)
        )).unwrap();
        s.run("def p1_ty : Ty := synth(p1)(Ctx.nil)").unwrap();
        s.run("def p1_ok : Bool := ok(p1)(Ctx.nil)").unwrap();
        s.run(&format!("def p1_val : Exp := run({})(p1)", nat(8))).unwrap();
        // snd (1, false)
        s.run(&format!(
            "def p2 : Exp := Exp.esnd(Exp.epair(Exp.enat({}), Exp.ebool(Bool.false)))",
            nat(1)
        )).unwrap();
        s.run("def p2_ty : Ty := synth(p2)(Ctx.nil)").unwrap();
        s.run(&format!("def p2_val : Exp := run({})(p2)", nat(4))).unwrap();
        assert_eq!(s.run_entry("p1_ty").unwrap(), "Ty.tnat", "fst of (nat, bool) is nat");
        assert_eq!(s.run_entry("p1_ok").unwrap(), "Bool.true");
        assert_eq!(s.run_entry("p1_val").unwrap(), "Exp.enat 3", "fst (1+2, true) = 3");
        assert_eq!(s.run_entry("p2_ty").unwrap(), "Ty.tbool", "snd of (nat, bool) is bool");
        assert_eq!(s.run_entry("p2_val").unwrap(), "Exp.ebool Bool.false", "snd (1, false) = false");
    }

    /// **Type safety extends to products.** Progress: `fst (5, 7)` is not stuck (it projects).
    /// Preservation: the `s_fst` projection step preserves the type (the projected component
    /// keeps the first-component type). Both kernel-checked with pairs in the language.
    #[test]
    fn products_type_safe() {
        let mut s = preservation_session().unwrap();
        s.run(&format!(
            "def fp : Exp := Exp.efst(Exp.epair(Exp.enat({}), Exp.enat({})))", nat(5), nat(7)
        )).unwrap();
        s.run(
            "def fp_not_stuck : Eq.{1} Bool (orB(isValue(fp))(canStep(fp))) Bool.true := \
               progress Ctx.nil fp (synth(fp)(Ctx.nil)) \
                 (ok_sound(fp)(Ctx.nil)(Eq.refl.{1} Bool Bool.true)) (Eq.refl.{1} Bool Bool.true)",
        )
        .expect("progress should certify the projection is not stuck");
        s.run(&format!(
            "def fp_step : Step fp (Exp.enat({})) := Step.s_fst (Exp.enat({})) (Exp.enat({}))",
            nat(5), nat(5), nat(7)
        )).unwrap();
        s.run(&format!(
            "def fp_preserved : HasTy Ctx.nil (Exp.enat({})) (synth(fp)(Ctx.nil)) := \
               preservation fp (Exp.enat({})) fp_step Ctx.nil (synth(fp)(Ctx.nil)) \
                 (ok_sound(fp)(Ctx.nil)(Eq.refl.{{1}} Bool Bool.true))",
            nat(5), nat(5)
        ))
        .expect("preservation should transport typing across the fst-projection step");
        assert!(s.k.env().contains("fp_not_stuck"));
        assert!(s.k.env().contains("fp_preserved"));
    }

    /// **Sums (case analysis) type-check and run (Tier 2).** `case (inl 5) of x => x+1 | y => 0`
    /// synthesizes `nat` and runs to `6` (the `inl` branch fires, binding the payload); and
    /// `case (inr false) of x => 0 | y => if y then 1 else 2` runs to `2` (the `inr` branch
    /// fires). The verified checker derives each branch's payload type via `fstSum`/`sndSum`.
    #[test]
    fn sums_typecheck_and_run() {
        let mut s = runnable_session().unwrap();
        // case (inl[:tbool] 5) of x => x + 1 | y => 0
        s.run(&format!(
            "def c1 : Exp := Exp.ecase(Exp.einl(Ty.tbool, Exp.enat({})), \
               Exp.eadd(Exp.evar(Nat.zero), Exp.enat({})), Exp.enat(Nat.zero))",
            nat(5), nat(1)
        )).unwrap();
        s.run("def c1_ty : Ty := synth(c1)(Ctx.nil)").unwrap();
        s.run("def c1_ok : Bool := ok(c1)(Ctx.nil)").unwrap();
        s.run(&format!("def c1_val : Exp := run({})(c1)", nat(8))).unwrap();
        // case (inr[:tnat] false) of x => 0 | y => if y then 1 else 2
        s.run(&format!(
            "def c2 : Exp := Exp.ecase(Exp.einr(Ty.tnat, Exp.ebool(Bool.false)), \
               Exp.enat(Nat.zero), Exp.eif(Exp.evar(Nat.zero), Exp.enat({}), Exp.enat({})))",
            nat(1), nat(2)
        )).unwrap();
        s.run("def c2_ty : Ty := synth(c2)(Ctx.nil)").unwrap();
        s.run(&format!("def c2_val : Exp := run({})(c2)", nat(8))).unwrap();
        assert_eq!(s.run_entry("c1_ty").unwrap(), "Ty.tnat", "case on (nat+bool) sum is nat");
        assert_eq!(s.run_entry("c1_ok").unwrap(), "Bool.true");
        assert_eq!(s.run_entry("c1_val").unwrap(), "Exp.enat 6", "case (inl 5) x=>x+1 = 6");
        assert_eq!(s.run_entry("c2_ty").unwrap(), "Ty.tnat");
        assert_eq!(s.run_entry("c2_val").unwrap(), "Exp.enat 2", "case (inr false) y=>if y..=2");
    }

    /// **Type safety extends to sums.** Progress: `case (inl 5) of x => x | y => 0` is not stuck
    /// (the `inl` branch fires). Preservation: the `s_case_inl` β-step preserves the type — the
    /// reduct (the substituted left branch) keeps the case's result type. Both kernel-checked.
    #[test]
    fn sums_type_safe() {
        let mut s = preservation_session().unwrap();
        // case (inl[:tbool] 5) of x => x | y => 0   — left branch returns the payload.
        s.run(&format!(
            "def cs : Exp := Exp.ecase(Exp.einl(Ty.tbool, Exp.enat({})), \
               Exp.evar(Nat.zero), Exp.enat(Nat.zero))",
            nat(5)
        )).unwrap();
        s.run(
            "def cs_not_stuck : Eq.{1} Bool (orB(isValue(cs))(canStep(cs))) Bool.true := \
               progress Ctx.nil cs (synth(cs)(Ctx.nil)) \
                 (ok_sound(cs)(Ctx.nil)(Eq.refl.{1} Bool Bool.true)) (Eq.refl.{1} Bool Bool.true)",
        )
        .expect("progress should certify the case is not stuck");
        s.run(&format!(
            "def cs_step : Step cs (Exp.enat({})) := \
               Step.s_case_inl Ty.tbool (Exp.enat({})) (Exp.evar Nat.zero) (Exp.enat Nat.zero)",
            nat(5), nat(5)
        )).unwrap();
        s.run(&format!(
            "def cs_preserved : HasTy Ctx.nil (Exp.enat({})) (synth(cs)(Ctx.nil)) := \
               preservation cs (Exp.enat({})) cs_step Ctx.nil (synth(cs)(Ctx.nil)) \
                 (ok_sound(cs)(Ctx.nil)(Eq.refl.{{1}} Bool Bool.true))",
            nat(5), nat(5)
        ))
        .expect("preservation should transport typing across the case-inl step");
        assert!(s.k.env().contains("cs_not_stuck"));
        assert!(s.k.env().contains("cs_preserved"));
    }

    /// **Soundness has teeth, with functions.** An application type error reduces `ok` to
    /// `false`, so no `refl` certificate exists and no derivation can be forged.
    #[test]
    fn ill_typed_application_cannot_be_certified() {
        let mut s = session().unwrap();
        s.run(
            "def bad : Exp := \
               Exp.eapp(Exp.elam(Ty.tnat, Exp.evar(Nat.zero)), Exp.ebool(Bool.true))",
        )
        .unwrap();
        let r = s.run(
            "def forged : HasTy Ctx.nil bad (synth(bad)(Ctx.nil)) := \
               ok_sound(bad)(Ctx.nil)(Eq.refl.{1} Bool Bool.true)",
        );
        assert!(r.is_err(), "an ill-typed application must not be certifiable");
    }
}
