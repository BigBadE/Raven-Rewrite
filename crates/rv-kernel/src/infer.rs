//! Grade and effect **inference** — so the engineer writes none of the annotations.
//!
//! * **Grades.** [`infer_grades`] re-grades a type's `Π` binders: a *type parameter*
//!   (its domain is a sort, e.g. `A : Type`) and a *proof parameter* (its domain is a
//!   proposition, `h : P` with `P : Prop`) are marked grade `0` — the two ubiquitous
//!   kinds of ghost argument. Everything else stays unrestricted. This is optimistic;
//!   [`infer_grades_checked`] *validates* the result with [`crate::erase`] (which
//!   rejects any grade-`0` binder actually used at runtime) and falls back to the
//!   fully-unrestricted grading if the optimism was wrong — so the outcome is always
//!   sound, with zero annotations from the user.
//!
//! * **Effects.** Effect-row inference for a computation is already
//!   [`Comp::effect`](crate::effect::Comp::effect) — it computes the latent row
//!   bottom-up. [`classify`] reads that off as the spec/exec distinction: a pure
//!   computation is admissible as logic (a `spec`), an effectful one is `exec`.

use crate::check::{Checker, LocalCtx};
use crate::effect::Comp;
use crate::erase;
use crate::reduce::Reducer;
use crate::term::{Grade, Term};
use crate::Env;

/// Re-grade the `Π` binders of `ty`: type/proof parameters become grade `0`.
pub fn infer_grades(env: &Env, ty: &Term) -> Term {
    let mut ctx_types: Vec<Term> = Vec::new();
    go(env, &mut ctx_types, ty)
}

fn go(env: &Env, ctx_types: &mut Vec<Term>, ty: &Term) -> Term {
    let red = Reducer::new(env);
    match red.whnf(ty) {
        Term::Pi(_, dom, cod) => {
            let grade = grade_for(env, ctx_types, &dom);
            ctx_types.push((*dom).clone());
            let cod2 = go(env, ctx_types, &cod);
            ctx_types.pop();
            Term::pi_graded(grade, (*dom).clone(), cod2)
        }
        other => other,
    }
}

/// The inferred grade of a binder whose domain type is `dom`.
fn grade_for(env: &Env, ctx_types: &[Term], dom: &Term) -> Grade {
    let red = Reducer::new(env);
    // A type parameter: its domain is itself a sort (`A : Type`/`A : Prop`).
    if matches!(red.whnf(dom), Term::Sort(_)) {
        return Grade::Zero;
    }
    // A proof parameter: its domain is a proposition (`h : P`, `P : Prop`).
    let chk = Checker::new(env);
    let mut ctx = LocalCtx::new();
    for t in ctx_types {
        ctx.push(t.clone());
    }
    if let Ok(sort) = chk.infer_sort(&mut ctx, dom) {
        if matches!(sort.normalize(), crate::Level::Zero) {
            return Grade::Zero;
        }
    }
    Grade::Many
}

/// Infer grades for `value : ty`, then *validate* by erasing. If the optimistic
/// grading makes erasure fail (a "ghost" was actually used at runtime), fall back to
/// the unrestricted (all-`Many`) type, which always erases. The returned type is
/// therefore always sound to erase against.
pub fn infer_grades_checked(env: &Env, value: &Term, ty: &Term) -> Term {
    let graded = infer_grades(env, ty);
    match erase::erase(env, value, &graded) {
        Ok(_) => graded,
        Err(_) => ty.clone(),
    }
}

/// The spec/exec classification of a computation, read off its inferred effect row.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    /// Pure — admissible as logic (a `spec`/`proof`).
    Spec,
    /// Effectful — runtime code.
    Exec,
}

/// Classify a computation by inferring its effect row.
pub fn classify(c: &Comp) -> Mode {
    if c.effect().is_pure() {
        Mode::Spec
    } else {
        Mode::Exec
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::erase::{erase, Erased};
    use crate::kernel::Kernel;
    use crate::term::name;

    fn cn(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }

    /// The engineer writes the *ungraded* polymorphic identity type; inference marks
    /// the type parameter grade 0, and erasure then drops it — yielding `λx. x`.
    #[test]
    fn infers_type_parameter_is_ghost() {
        let env = Env::new();
        // ungraded type: Π (A : Type). Π (x : A). A      (all Many)
        let ty = Term::pi(Term::typ(0), Term::pi(Term::Var(0), Term::Var(1)));
        let graded = infer_grades(&env, &ty);

        // The first binder is now grade 0, the second Many.
        match &graded {
            Term::Pi(g0, _, cod) => {
                assert_eq!(*g0, Grade::Zero, "type parameter should be inferred ghost");
                match &**cod {
                    Term::Pi(g1, _, _) => assert_eq!(*g1, Grade::Many),
                    _ => panic!(),
                }
            }
            _ => panic!(),
        }

        // And erasure against the inferred grades drops the type argument.
        let value = Term::lam(Term::typ(0), Term::lam(Term::Var(0), Term::Var(0)));
        assert_eq!(erase(&env, &value, &graded).unwrap(), Erased::lam(Erased::Var(0)));
    }

    /// A proof parameter (`h : P`, `P : Prop`) is inferred ghost and erased.
    #[test]
    fn infers_proof_parameter_is_ghost() {
        let mut k = Kernel::new();
        k.add_axiom("P", 0, Term::prop()).unwrap();
        k.add_axiom("Nat0", 0, Term::typ(0)).unwrap();
        // ungraded:  Π (n : Nat0). Π (h : P). Nat0
        let ty = Term::pi(cn("Nat0"), Term::pi(cn("P"), cn("Nat0")));
        let graded = infer_grades(k.env(), &ty);
        match &graded {
            Term::Pi(g_n, _, cod) => {
                assert_eq!(*g_n, Grade::Many, "data parameter stays runtime");
                match &**cod {
                    Term::Pi(g_h, _, _) => assert_eq!(*g_h, Grade::Zero, "proof parameter is ghost"),
                    _ => panic!(),
                }
            }
            _ => panic!(),
        }
        // value λ n h. n   erases to  λn. n
        let value = Term::lam(cn("Nat0"), Term::lam(cn("P"), Term::Var(1)));
        assert_eq!(erase(k.env(), &value, &graded).unwrap(), Erased::lam(Erased::Var(0)));
    }

    /// Validation + fallback: if a "type parameter" is actually used at runtime, the
    /// checked inference falls back to the unrestricted grading (which always erases).
    #[test]
    fn checked_inference_falls_back_when_optimism_is_wrong() {
        let env = Env::new();
        // value λ (A : Type). A      type Π (A : Type). Type
        // Inference would mark A ghost, but the body returns A (a runtime use), so
        // erasing against the ghost grading fails — fall back to all-Many.
        let ty = Term::pi(Term::typ(0), Term::typ(1));
        let value = Term::lam(Term::typ(0), Term::Var(0));
        let safe = infer_grades_checked(&env, &value, &ty);
        // Fallback grading: the binder is Many, so erasure succeeds.
        assert!(erase(&env, &value, &safe).is_ok());
        match &safe {
            Term::Pi(g, _, _) => assert_eq!(*g, Grade::Many, "demoted to runtime after validation"),
            _ => panic!(),
        }
    }

    /// Effect inference classifies spec vs exec.
    #[test]
    fn classifies_spec_and_exec() {
        let pure = Comp::ret(cn("u"));
        let effectful = Comp::perform("io", Comp::ret(cn("u")));
        assert_eq!(classify(&pure), Mode::Spec);
        assert_eq!(classify(&effectful), Mode::Exec);
    }
}
