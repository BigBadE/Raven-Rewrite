//! Proof by reflection — the socket every "discharge by computation" procedure
//! plugs into.
//!
//! The reflection approach replaces a big proof *object* with a *computation*: prove
//! a decision procedure sound **once**, then discharge each instance by running the
//! procedure in the kernel's reducer and observing it returns `true`. The universal
//! linchpin is
//!
//! ```text
//! of_decide_eq_true : (p : Prop) (d : Decidable p) → (decide p d = true) → p
//! ```
//!
//! Given any `Decidable p`, a proof of `p` is `of_decide_eq_true p d (refl)` — and
//! `refl : decide p d = true` type-checks *iff the kernel computes `decide p d` to
//! `true`*. So the proof of `p` is literally the evaluation of `decide`. Every
//! reflective tactic (`decide`, `lia`/Farkas, `ring`) is this lemma applied to a
//! different, separately-verified `Decidable` instance.
//!
//! This module installs that foundation through the trusted [`Kernel`] (so all of it
//! is kernel-checked, nothing trusted) and proves it out with a complete reflective
//! decision procedure for `Bool` equality. Swapping `decEqBool` for a verified linear
//! -arithmetic checker is the only delta to get SMT-style discharge — see the module
//! tests and the crate docs for the Farkas shape.

use crate::elab::run_program;
use crate::kernel::Kernel;

/// The surface program defining the reflection foundation: `Bool`, `True`, `False`,
/// `Eq`, `Decidable`, `decide`, `Bool` no-confusion, the `of_decide_eq_true`
/// linchpin, and a fully-proven decidable equality on `Bool`.
pub const REFLECTION_PRELUDE: &str = r#"
    inductive Bool : Type | false : Bool | true : Bool
    inductive True : Prop | intro : True
    inductive False : Prop
    inductive Eq.{u} (A : Sort u) (a : A) : A -> Prop | refl : Eq A a a

    -- Decidable p is informative (in Type): it carries either a proof of p or a
    -- refutation, so we can *eliminate* it to compute a Bool.
    inductive Decidable (p : Prop) : Type
      | isFalse : (p -> False) -> Decidable p
      | isTrue  : p -> Decidable p

    def decide (p : Prop) (d : Decidable p) : Bool :=
      Decidable.rec.{1} p (fun (_ : Decidable p) => Bool)
        (fun (_ : p -> False) => Bool.false)
        (fun (_ : p) => Bool.true)
        d

    -- Two Bool-indexed propositions used for no-confusion.
    def isFalseProp (b : Bool) : Prop := Bool.rec.{1} (fun (_ : Bool) => Prop) True False b
    def isTrueProp  (b : Bool) : Prop := Bool.rec.{1} (fun (_ : Bool) => Prop) False True b

    -- Bool no-confusion: false and true are distinct.
    def ff_ne_tt (h : Eq.{1} Bool Bool.false Bool.true) : False :=
      Eq.rec.{1, 0} Bool Bool.false
        (fun (b : Bool) (_ : Eq.{1} Bool Bool.false b) => isFalseProp b)
        True.intro Bool.true h

    def tt_ne_ff (h : Eq.{1} Bool Bool.true Bool.false) : False :=
      Eq.rec.{1, 0} Bool Bool.true
        (fun (b : Bool) (_ : Eq.{1} Bool Bool.true b) => isTrueProp b)
        True.intro Bool.false h

    -- The reflection linchpin.
    def of_decide_eq_true (p : Prop) (d : Decidable p)
        (h : Eq.{1} Bool (decide p d) Bool.true) : p :=
      Decidable.rec.{0} p
        (fun (d' : Decidable p) => Eq.{1} Bool (decide p d') Bool.true -> p)
        (fun (hnp : p -> False) (he : Eq.{1} Bool Bool.false Bool.true) =>
           False.rec.{0} (fun (_ : False) => p) (ff_ne_tt he))
        (fun (hp : p) (he : Eq.{1} Bool Bool.true Bool.true) => hp)
        d h

    -- A complete, verified reflective decision procedure: decidable Bool equality.
    def decEqBool (a : Bool) (b : Bool) : Decidable (Eq.{1} Bool a b) :=
      Bool.rec.{1} (fun (a' : Bool) => (b : Bool) -> Decidable (Eq.{1} Bool a' b))
        (fun (b : Bool) =>
          Bool.rec.{1} (fun (b' : Bool) => Decidable (Eq.{1} Bool Bool.false b'))
            (Decidable.isTrue (Eq.{1} Bool Bool.false Bool.false) (Eq.refl.{1} Bool Bool.false))
            (Decidable.isFalse (Eq.{1} Bool Bool.false Bool.true) ff_ne_tt)
            b)
        (fun (b : Bool) =>
          Bool.rec.{1} (fun (b' : Bool) => Decidable (Eq.{1} Bool Bool.true b'))
            (Decidable.isFalse (Eq.{1} Bool Bool.true Bool.false) tt_ne_ff)
            (Decidable.isTrue (Eq.{1} Bool Bool.true Bool.true) (Eq.refl.{1} Bool Bool.true))
            b)
        a b
"#;

/// Install the reflection foundation into `k`.
pub fn declare_reflection(k: &mut Kernel) -> Result<(), String> {
    run_program(k, REFLECTION_PRELUDE)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elab::term_of_str;

    fn reflect_kernel() -> Kernel {
        let mut k = Kernel::new();
        declare_reflection(&mut k).expect("reflection prelude should check");
        k
    }

    /// The whole foundation type-checks (every def is kernel-verified on the way in).
    #[test]
    fn foundation_checks() {
        let k = reflect_kernel();
        for n in ["decide", "of_decide_eq_true", "decEqBool", "ff_ne_tt", "tt_ne_ff"] {
            assert!(k.env().contains(n), "missing {n}");
        }
    }

    /// Proof BY COMPUTATION: discharge `true = true` via the reflective procedure.
    /// The proof term is `of_decide_eq_true … refl`; it type-checks only because the
    /// kernel *evaluates* `decide (decEqBool true true)` to `true`.
    #[test]
    fn discharge_decidable_goal_by_computation() {
        let mut k = reflect_kernel();
        let program = r#"
            def true_eq_true : Eq.{1} Bool Bool.true Bool.true :=
              of_decide_eq_true (Eq.{1} Bool Bool.true Bool.true)
                (decEqBool Bool.true Bool.true)
                (Eq.refl.{1} Bool Bool.true)
        "#;
        run_program(&mut k, program).expect("reflective proof should check");
        assert!(k.env().contains("true_eq_true"));
    }

    /// Soundness in action: for a FALSE goal the procedure computes `false`, so the
    /// `refl` certificate cannot exist and the goal is unprovable this way. We check
    /// the computation directly: `decide (decEqBool false true)` reduces to `false`,
    /// not `true`.
    #[test]
    fn false_goal_computes_to_false() {
        let k = reflect_kernel();
        let lhs = term_of_str(
            k.env(),
            "decide (Eq.{1} Bool Bool.false Bool.true) (decEqBool Bool.false Bool.true)",
        )
        .unwrap();
        let ff = term_of_str(k.env(), "Bool.false").unwrap();
        let tt = term_of_str(k.env(), "Bool.true").unwrap();
        assert!(k.def_eq(&lhs, &ff), "should compute to false");
        assert!(!k.def_eq(&lhs, &tt), "must NOT compute to true");
    }

    /// And the positive case really does compute to `true`.
    #[test]
    fn true_goal_computes_to_true() {
        let k = reflect_kernel();
        let lhs = term_of_str(
            k.env(),
            "decide (Eq.{1} Bool Bool.true Bool.true) (decEqBool Bool.true Bool.true)",
        )
        .unwrap();
        let tt = term_of_str(k.env(), "Bool.true").unwrap();
        assert!(k.def_eq(&lhs, &tt));
    }
}
