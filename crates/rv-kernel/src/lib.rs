//! `rv-kernel` — a small dependent type theory as the (eventual) single trust base.
//!
//! This crate is the L0 foundation from the kernel-and-core plan: a dependently
//! typed λ-calculus with a cumulative universe hierarchy, inductive types, and a few
//! axioms — and *nothing else*. Arithmetic, sequences, ownership, decision
//! procedures, and the language's own metatheory are intended to be built *on top*
//! as verified libraries, not baked in here. The smaller and more boring this crate
//! is, the smaller the part of the system that must be trusted.
//!
//! It is deliberately built **in parallel** to the existing `rv-core`-based pipeline:
//! nothing here is wired into `rv-driver` yet, so the current compiler is untouched.
//!
//! Layout:
//! * [`level`] — universe levels (`Sort 0 = Prop`, `Type n = Sort (n+1)`).
//! * [`term`]  — the de Bruijn core term language (the whole grammar).
//! * [`env`]   — the global declaration store (axioms, defs, inductives, recursors).
//! * [`reduce`]— β/δ/ζ/ι reduction and definitional equality.
//! * [`check`] — the trusted bidirectional type-checker.
//! * [`inductive`] — declaring inductive families: positivity, constructor checking,
//!   and recursor (eliminator) generation.
//!
//! ## The `Prop` decision
//!
//! We adopt Lean/CIC's **impredicative `Prop`** (`Sort 0`), realized by the `imax`
//! product rule in [`check`]. This was the recommended fork in the design plan: it
//! keeps the higher-order/effect-logic frontier open. Predicativity would have meant
//! dropping `imax` for `max`; the term language and Phases 0–1 are identical either
//! way — the choice only bites at Phase-2 elimination, where it shows up as the
//! large-elimination restriction on `Prop`-valued inductives.

pub mod check;
pub mod coinductive;
pub mod effect;
pub mod elab;
pub mod elab2;
pub mod env;
pub mod erase;
pub mod generate;
pub mod inductive;
pub mod infer;
pub mod kernel;
pub mod level;
pub mod logic;
pub mod mutual;
pub mod nbe;
pub mod reduce;
pub mod surface;
pub mod term;
pub mod unify;
pub mod verify;

pub use check::{Checker, LocalCtx};
pub use env::{Decl, Env};
pub use kernel::Kernel;
pub use level::Level;
pub use term::{name, Name, Term};

#[cfg(test)]
mod tests {
    use super::*;

    /// Phase 0 milestone: the kernel type-checks the polymorphic identity
    /// `λ(A : Type 0)(x : A). x` and assigns it `Π(A : Type 0). A → A`.
    #[test]
    fn polymorphic_identity_checks() {
        let env = Env::new();
        let chk = Checker::new(&env);

        // λ (A : Type 0). λ (x : A). x
        let id = Term::lam(Term::typ(0), Term::lam(Term::Var(0), Term::Var(0)));
        let ty = chk.infer_closed(&id).expect("identity should type-check");

        // Expected: Π (A : Type 0). A → A   ==  Π (Type 0). Π (Var 0). Var 1
        let expected = Term::pi(Term::typ(0), Term::pi(Term::Var(0), Term::Var(1)));
        let r = reduce::Reducer::new(&env);
        assert!(r.is_def_eq(&ty, &expected), "got {ty:?}");
    }

    /// The identity's *type* itself lives in `Type 1` (`Sort 2`).
    #[test]
    fn identity_type_is_in_type1() {
        let env = Env::new();
        let chk = Checker::new(&env);
        let id_ty = Term::pi(Term::typ(0), Term::pi(Term::Var(0), Term::Var(1)));
        let k = chk.infer_closed(&id_ty).expect("identity type should be well-formed");
        // Sort (imax 2 (imax 1 1)) = Sort 2 = Type 1.
        assert!(matches!(k, Term::Sort(_)));
        let r = reduce::Reducer::new(&env);
        assert!(r.is_def_eq(&k, &Term::typ(1)), "got {k:?}");
    }

    /// Universes are stratified: `Type 0 : Type 1`, not `Type 0 : Type 0`.
    #[test]
    fn universe_stratification() {
        let env = Env::new();
        let chk = Checker::new(&env);
        let ty = chk.infer_closed(&Term::typ(0)).unwrap();
        let r = reduce::Reducer::new(&env);
        assert!(r.is_def_eq(&ty, &Term::typ(1)));
        assert!(!r.is_def_eq(&ty, &Term::typ(0)));
    }

    /// Application of a non-function is rejected.
    #[test]
    fn applying_a_sort_is_rejected() {
        let env = Env::new();
        let chk = Checker::new(&env);
        let bad = Term::app(Term::typ(0), Term::typ(0));
        assert!(chk.infer_closed(&bad).is_err());
    }

    /// `Prop` is impredicative: `Π (A : Type 0). A` (a proposition quantifying over
    /// all types) still lands in `Prop`, not a higher universe.
    #[test]
    fn prop_is_impredicative() {
        let env = Env::new();
        let chk = Checker::new(&env);
        // Π (A : Type 0). (A → A is a Prop? no) — use a genuinely Prop codomain:
        // Π (A : Prop). A  : Prop
        let t = Term::pi(Term::prop(), Term::Var(0));
        let k = chk.infer_closed(&t).unwrap();
        let r = reduce::Reducer::new(&env);
        assert!(r.is_def_eq(&k, &Term::prop()), "got {k:?}");
    }
}
