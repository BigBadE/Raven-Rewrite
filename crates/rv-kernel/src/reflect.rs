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
pub const REFLECTION_PRELUDE: &str = include_str!("raven/reflect_reflection_prelude.rvk");

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
        let program = include_str!("raven/reflect_program1.rvk");
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
