//! `rv-kernel` — a small dependent type theory as the (eventual) single trust base.
//!
//! This crate is the L0 foundation from the kernel-and-core plan: a dependently
//! typed λ-calculus with a cumulative universe hierarchy, inductive types, and a few
//! axioms — and *nothing else*. Arithmetic, sequences, ownership, decision
//! procedures, and the language's own metatheory are intended to be built *on top*
//! as verified libraries, not baked in here. The smaller and more boring this crate
//! is, the smaller the part of the system that must be trusted.
//!
//! It was originally built **in parallel** to the existing `rv-core`-based pipeline;
//! `rv-driver`'s `verify_rv`/`verify_rv_unified` now route the `.rv` proof surface through
//! it (see `rv-driver::verify::Session`), so this crate is the live proof/verification
//! backend, not a standalone experiment.
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
//!
//! ## Trust map: TRUSTED core vs UNTRUSTED elaboration
//!
//! The whole point of a kernel architecture is that soundness rests on a small, auditable
//! slice of this crate — everything else can be as large, buggy, or over-engineered as it
//! needs to be, because its output is *re-checked* by the small slice before it is
//! trusted. Concretely, as of this writing (~16.7k LOC across the crate):
//!
//! **TRUSTED core (~2,900 LOC — term representation, checker, reduction, and the *typing
//! rules* of each axiomatic schema):**
//! * [`term`] (442 LOC) — the de Bruijn term grammar itself. Defines what a term *is*.
//! * [`level`] (243 LOC) — universe levels/cumulativity, load-bearing for `Sort` typing.
//! * [`env`] (437 LOC) — the declaration store. [`env::Env::insert`] is a dumb, unchecked
//!   map write (rejects only redeclaration) — trusted *as a data structure*, not as a
//!   guarantor of well-typedness; that guarantee comes from who is allowed to call it (see
//!   below).
//! * [`check`] (293 LOC) — the trusted bidirectional type-checker (`infer`/`check`). This
//!   is *the* soundness-critical function: if it accepts a term, the term is well-typed by
//!   definition.
//! * [`reduce`] (498 LOC) and [`nbe`] (615 LOC) — β/δ/ζ/ι/ν reduction and definitional
//!   equality (two implementations: a direct reducer and a normalize-by-evaluation
//!   engine used for performance; both must agree, and [`check`] only trusts whichever
//!   one it actually calls).
//! * [`kernel`] (213 LOC + this file, ~130 LOC) — [`Kernel`], the front door. Its
//!   `add_axiom`/`add_definition` are the *only* sanctioned way an axiom's stated type or
//!   a definition's value get into the trusted [`Env`] via the checker; [`reject_meta`]
//!   (private to `kernel.rs`) additionally guarantees no elaboration hole ever reaches
//!   [`check`]. [`recheck_all_definitions`] is the independent re-verification harness
//!   (see below).
//! * [`inductive`] (402 LOC, *typing rules only*) — the shape of a well-formed inductive
//!   family/recursor and its ι-reduction rule is trusted; but see UNTRUSTED below for the
//!   *synthesis* of that shape from a surface spec, which is a separate, larger, re-checked
//!   concern.
//! * The **typing and reduction rules** (not the installer code around them) of the
//!   axiomatically-declared primitive schemas: `Quot`/`Quot.mk`/`Quot.sound`/`Quot.lift`/
//!   `Quot.ind` ([`quotient`]), `Trunc` ([`trunc`]), `S1`/the circle HIT ([`circle`]), and
//!   coinductive destructors/corecursors ([`coinductive`]). These are declared
//!   axiomatically — like `Nat`'s recursor, their soundness rests on a paper argument (see
//!   each module's doc comment for its specific soundness case), not on being re-derived
//!   by [`check`]. This is unavoidable: they are exactly the primitives from which
//!   everything else is derived, so nothing more basic exists to check them against.
//!
//! **UNTRUSTED (everything else, ~13,800 LOC — elaboration, synthesis, tactics; all of it
//! terminates in a call through [`Kernel::add_axiom`]/[`add_definition`]/
//! [`declare_inductive`], which re-verifies the result against [`check`]):**
//! * [`elab2`] (2,453 LOC, by far the largest module) — holes, unification, surface sugar.
//! * [`surface`] (1,479 LOC) and [`elab`] (438 LOC) — the older/simpler surface layers.
//! * [`verify`] (1,387 LOC) — the tactic engine / proof-fragment `Session` driving `.rv`
//!   proof scripts; every tactic result is fed to `Kernel::add_definition`/`Kernel::check`
//!   (see `verify.rs` around the `add_definition`/`.check(` call sites).
//! * [`generate`] (783 LOC) — *synthesizes* recursors/positivity checks from an `IndSpec`;
//!   the synthesized recursor's `ty`/reduction rule it emits still has to satisfy the
//!   TRUSTED shape enforced by [`inductive::declare_raw`], but the search/derivation logic
//!   that builds the candidate is untrusted engineering.
//! * [`unify`] (630 LOC), [`infer`] (183 LOC), [`mutual`] (467 LOC), [`graded`] (706 LOC,
//!   QTT usage-checking — a *linter*, not part of well-typedness), [`erase`] (289 LOC),
//!   [`effect`] (389 LOC), [`logic`] (310 LOC), [`funext`] (442 LOC — derives a proof term
//!   that [`check`] then verifies; see `install_funext`).
//!
//! **Bypasses of the checked front door.** [`quotient`], [`trunc`], [`circle`],
//! [`coinductive`], [`generate`], [`mutual`], and [`inductive::declare_raw`] call
//! [`env::Env::insert`] directly rather than going through `Kernel::add_definition` —
//! by design, since they are installing new *axiomatic* schema constants (no antecedent
//! type to check the schema's own typing rule against) or a recursor whose *shape* is
//! enforced by `declare_raw`'s own checks rather than by delegating to [`check`]. The one
//! module that looks like a bypass but is not is [`funext`]: `install_funext` calls
//! [`check::Checker::check`] on its derived proof term *before* the raw `env.insert` — so
//! the insert is just where the already-checked result lands, not an unchecked write. No
//! module inserts a `Decl::Def` (a value claimed to inhabit a type) without either going
//! through `Kernel::add_definition` or checking it manually first, as `funext` does.
//!
//! ## The independent re-check harness
//!
//! [`recheck_all_definitions`] takes a fully-elaborated [`Env`] — the actual result of
//! running the elaborator/tactics/schema installers over a whole proof corpus — and
//! re-verifies *every* stored [`env::Decl::Def`] from scratch with a brand-new [`check::Checker`],
//! ignoring entirely how the definition was produced. It is the concrete, testable version
//! of the trust-split claim above: run it over the real proof corpus (see
//! `rv-driver`'s `tests/recheck_harness.rs`) and any definition that reached the
//! environment without being genuinely checked — whether through a future bug in
//! `add_definition`'s call sites or a bypass that shouldn't exist — fails loudly instead of
//! silently riding on elaboration's say-so.

pub mod check;
pub mod circle;
pub mod coinductive;
pub mod effect;
pub mod elab;
pub mod elab2;
pub mod env;
pub mod erase;
pub mod funext;
pub mod generate;
pub mod graded;
pub mod inductive;
pub mod infer;
pub mod kernel;
pub mod level;
pub mod logic;
pub mod mutual;
pub mod nbe;
pub mod quotient;
pub mod reduce;
pub mod surface;
pub mod term;
pub mod trunc;
pub mod unify;
pub mod verify;

pub use check::{Checker, LocalCtx};
pub use env::{Decl, Env};
pub use kernel::{recheck_all_definitions, Kernel};
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
