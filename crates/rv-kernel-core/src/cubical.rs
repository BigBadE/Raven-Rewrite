//! **Phase 1** of the cubical build: the interval `I` and `Path`/`PathP` types,
//! *without* Kan operations (`transp`/`hcomp`/`comp`/`glue`/faces — all deferred to a
//! later phase). This module is doc-comments-first: read it before touching
//! [`crate::term::Term::I`]/[`Term::IZero`]/[`Term::IOne`]/[`Term::PLam`]/
//! [`Term::PApp`]/[`Term::PathP`] or [`crate::check::Checker`]'s handling of them.
//!
//! # Which interval: Cartesian, not De Morgan
//!
//! Phase 1 implements the **simplest sound choice**: a *Cartesian* interval — just the
//! two endpoints `i0`/`i1` and interval *variables* — with **no** De Morgan connection
//! structure (`_∧_`, `_∨_`, `~_`). Those lattice operations exist to support Kan
//! composition/`hcomp` (they're what makes the "cube" a cube with faces you can fill);
//! since this phase deliberately excludes Kan entirely, there is nothing for them to
//! do yet, and adding them now would just be unused surface area with its own
//! (nontrivial — De Morgan laws must hold *definitionally*) soundness burden. A later
//! Kan phase can add them without disturbing anything here.
//!
//! # Representation: interval variables reuse the ordinary `Var` binder
//!
//! A naive design gives interval variables their own de Bruijn *namespace* (a second
//! counter, parallel to `Term::Var`), which then needs its own `lift`/`subst` pair
//! threaded through every existing binder, and its own value environment in the NbE
//! evaluator. Phase 1 avoids all of that: [`Term::PLam`] (path abstraction, `⟨i⟩ t`)
//! binds its interval variable using the **same** `Var`/de-Bruijn machinery as
//! [`Term::Lam`] — the bound `i` inside `t` really is `Term::Var(0)`, shifted by
//! `Term::lift`/`Term::instantiate` exactly like any other bound variable. The only
//! difference from an ordinary binder is that [`crate::check::LocalCtx`] records the
//! phantom [`Term::I`] as that binder's "type" (via `ctx.with(Term::I, ...)`) instead
//! of a real sort. This is what makes `I` **not fibrant**: `infer(Term::I)` is
//! rejected outright (see [`crate::check::Checker::infer`]'s `Term::I` arm), so a
//! `Term::I` can never itself be checked as a `Π`/`λ` domain or codomain — nothing can
//! quantify a genuine `Type` over the interval, which is exactly the "no transport
//! yet" restriction Phase 1 needs.
//!
//! The payoff: every existing `lift`/`subst`/`subst_ctx`/`instantiate_levels`/
//! `has_meta` case for `Var` needed **no new logic**, and the NbE evaluator's existing
//! `Var`/`VEnv`/closure infrastructure evaluates and quotes path abstractions the same
//! way it does ordinary lambdas (see [`crate::nbe::Value::PLam`]). The only genuinely
//! new machinery is: (1) [`crate::check::Checker`]'s four new `infer` cases
//! (`I`/`IZero`/`IOne` are trivial; `PLam`/`PApp`/`PathP` mirror `Lam`/`App`/`Pi`); (2)
//! one new β-rule in both [`crate::reduce::Reducer::whnf`] and
//! [`crate::nbe::Nbe::vpapp`] (differentially cross-checked, matching this crate's
//! existing convention for every other computation rule); (3) structural
//! definitional-equality cases in both conversion checkers.
//!
//! # The one computation rule, and its Phase-1 boundary
//!
//! ```text
//!   (⟨i⟩ t) @ i0  ↦  t[i := i0]
//!   (⟨i⟩ t) @ i1  ↦  t[i := i1]
//!   (⟨i⟩ t) @ r   ↦  t[i := r]     (general β, r any interval term)
//! ```
//!
//! `PathP`'s well-formedness check (in `Checker::infer`'s `Term::PathP` arm) requires
//! the two declared endpoints to be *definitionally equal* to the family instantiated
//! at `i0`/`i1` — not syntactically identical — so "the boundary holds by conversion"
//! for anything actually built through `PLam` (directly, or via a `Const` that
//! δ-unfolds to one): `whnf` unfolds through `Let`/`Const`/`Lam`/ι/ν/etc. exactly as it
//! always did, and *then* fires the `PApp` rule once the head reaches a literal
//! `PLam`.
//!
//! **The boundary equation also holds for neutral `p`** — not just a literal `PLam` —
//! via a second, *type-directed* rule in [`crate::check::Checker::path_boundary`]
//! (checked from [`crate::check::Checker::compare`], the authoritative conversion):
//! for any `p` whose *inferred* type is `PathP (λi. A) a0 a1` (a bound variable, an
//! axiom, a stuck application — anything), `p @ i0 ≡ a0` and `p @ i1 ≡ a1`
//! definitionally, because `a0`/`a1` are exactly the endpoints that `p`'s `PathP` type
//! was *already checked against* (`Checker::infer`'s `Term::PathP` arm — see above).
//! This mirrors real cubical type theory (`p i0` reduces for *any* `p : Path A a0 a1`,
//! not only literal path abstractions) and is what lets the derived `funext`/`ap`
//! below type-check at their *stated*, fully general types even when composed with an
//! abstract/neutral path hypothesis (see `ap_boundaries_compute`,
//! `funext_typechecks`). It is exactly analogous to [proof
//! irrelevance](crate::check::Checker::proof_irrelevant) — another type-directed
//! equation the purely structural reducer/NbE conversion can't express, added only at
//! the authoritative [`crate::check::Checker::compare`] layer, not in the lower-level
//! [`crate::reduce::Reducer::is_def_eq`]/[`crate::nbe::Nbe::conv`] (which stay purely
//! structural — the differential tests below only compare those two against each
//! other on the literal-`PLam` β-rule, which both of them do implement identically).
//!
//! This is still strictly conservative: it introduces **no new equation** beyond what
//! a prior, independently-checked typing judgement already forced. See soundness
//! point 3 below.
//!
//! # Soundness argument: Path (without Kan) proves nothing new
//!
//! Phase 1 cannot be used to derive `False` (or equate any two distinct closed
//! values) that the pre-existing kernel couldn't already derive. Sketch:
//!
//! 1. **No transport.** The only way to move a term from one type to another in this
//!    kernel is via conversion (`is_def_eq`) — there is no `J`/`transp`/`subst`
//!    operator over `Path`/`PathP` in Phase 1 (that's the Kan phase). So a `Path A a
//!    b` witness can never be *used* to turn a value at type `A` into a value at some
//!    other type, or to rewrite one side of an unrelated goal — it just sits there as
//!    inert data.
//! 2. **Conservative extension of conversion.** The new definitional-equality cases
//!    added to `reduce::is_def_eq`/`check::compare`/`nbe::alpha_eta_eq` are purely
//!    *structural* (`PLam ≡ PLam` iff bodies `≡`, `PathP ≡ PathP` iff components `≡`,
//!    `IZero ≡ IZero`, …) plus the one β-rule above, plus the type-directed
//!    `path_boundary` rule (see above). None of them can make two pre-existing
//!    (non-Path) terms equal that weren't already: the structural cases are additive
//!    branches in a `match` over the *new* constructors only (a `Sort`/`Pi`/`Lam`/
//!    application/etc. is still only ever compared against another term of the same
//!    head shape, exactly as before this change — every pre-Phase-1 test in the
//!    existing 586-test suite is byte-for-byte unaffected, since no old term can ever
//!    contain a new constructor), and `path_boundary` only ever equates `p @ i0`/`p @
//!    i1` with the endpoint *already recorded in `p`'s own previously-checked type* —
//!    it cannot introduce an equation between two terms that weren't already tied
//!    together by an earlier, independent typing judgement.
//! 3. **Closing a `Path` requires an actual proof.** `Checker::infer`'s `Term::PLam`
//!    arm *computes* the endpoints as `body.instantiate(&IZero)`/`instantiate(&IOne)`
//!    — they are not asserted, they are read off the body you supplied. So
//!    `PLam(body) : Path A a b` only type-checks when `body[i:=i0]` and `body[i:=i1]`
//!    are *literally* (up to the kernel's existing, already-sound conversion) `a` and
//!    `b`. There is no way to write a `PLam` whose type lies about its endpoints (see
//!    the adversarial test `plam_cannot_lie_about_its_endpoints` below) — this is
//!    exactly parallel to how `refl : Eq a a` can't be abused to prove `Eq a b` for
//!    distinct `a`,`b` in the pre-existing `Eq`/inductive-equality machinery.
//! 4. **`I` can't smuggle data.** Since `infer(I)` errors, no `Π`/`λ` can be built
//!    with `I` as a domain or codomain, so an interval variable can never flow into a
//!    position that expects a real `Type`-classified value (e.g. it can't be handed to
//!    a function expecting `Nat`, or used as a motive) — `is_def_eq` would have to
//!    equate `I` with that function's declared domain type, and the structural cases
//!    added above only equate `I` with `I`.
//!
//! Net effect: Phase 1 is exactly what the task calls it — "a conservative
//! presentation of a reflexive/congruent relation with definitional endpoints". The
//! adversarial tests below exercise points 3 and 4 directly, plus the boundary
//! computation itself and the derived `refl`/`funext`/`ap` terms.
//!
//! # What's deferred to later (Kan) phases
//!
//! `transp`/`J`-for-`Path` (transporting along a path), `hcomp`/`comp` (composition —
//! filling an open box), `Glue` types, and face formulas/systems (`[φ ↦ u]`,
//! partial elements) are **all out of scope here**. They are exactly the pieces that
//! turn `Path` from inert data into something that can move proofs between types —
//! i.e. exactly the pieces whose soundness this module's argument depends on
//! *excluding*.

use crate::term::Term;

/// `refl a : Path A a a` — the constant path `⟨i⟩ a` (the body doesn't mention `i`, so
/// it's `a` lifted past the new binder, exactly like [`Term::arrow`]'s non-dependent
/// codomain). A one-line *definitional* fact once `Path` exists, in contrast to the
/// quotient-derived `Eq`/`refl` already in the kernel (see `crate::quotient`), which is
/// an axiomatized computation rule rather than something `Path`'s own reduction gives
/// for free.
pub fn refl(a: &Term) -> Term {
    Term::plam(a.lift(1, 0))
}

/// `funext h : Path (Π x:A. B x) f g`, given `h : Π x:A. Path (B x) (f x) (g x)`.
/// Built as `⟨i⟩ λx. (h x) @ i` — swap the two binders of `h`'s pointwise paths for one
/// path of functions. `dom` is `A`, the shared domain of `f`/`g`/`h`'s telescope.
///
/// This is the *definitional* one-liner Phase 1's `Path` enables directly (no
/// computation rule needs to be axiomatized/derived for it — contrast the
/// quotient-derived `install_funext` schema elsewhere in the kernel, which exists
/// precisely because `Eq` there has no such direct proof).
pub fn funext(dom: &Term, h: &Term) -> Term {
    Term::plam(Term::lam(
        dom.lift(1, 0),
        Term::papp(Term::app(h.lift(2, 0), Term::Var(0)), Term::Var(1)),
    ))
}

/// `ap f p : Path B (f a) (f b)`, given `f : A -> B` and `p : Path A a b`. Built as
/// `⟨i⟩ f (p @ i)` — push `f` under the path.
pub fn ap(f: &Term, p: &Term) -> Term {
    Term::plam(Term::app(f.lift(1, 0), Term::papp(p.lift(1, 0), Term::Var(0))))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Kernel;
    use crate::term::name;

    fn cn(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }

    /// A small environment: `A B : Type 0`, `a b c : A`, `f g : A -> A`.
    fn base_env() -> Kernel {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("B", 0, Term::typ(0)).unwrap();
        k.add_axiom("a", 0, cn("A")).unwrap();
        k.add_axiom("b", 0, cn("A")).unwrap();
        k.add_axiom("c", 0, cn("A")).unwrap();
        k.add_axiom("f", 0, Term::arrow(cn("A"), cn("A"))).unwrap();
        k.add_axiom("g", 0, Term::arrow(cn("A"), cn("A"))).unwrap();
        k
    }

    // ---- Basic Path/PathP typing ----

    #[test]
    fn refl_typechecks() {
        let k = base_env();
        let a = cn("a");
        let p = refl(&a);
        let ty = k.infer(&p).unwrap();
        assert!(k.def_eq(&ty, &Term::path(cn("A"), a.clone(), a)));
    }

    #[test]
    fn refl_check_against_path_type() {
        let k = base_env();
        let a = cn("a");
        k.check(&refl(&a), &Term::path(cn("A"), a.clone(), a)).unwrap();
    }

    #[test]
    fn non_dependent_path_is_pathp_with_constant_family() {
        // `Path A a b` unfolds (structurally) to `PathP (A lifted) a b`; both spellings
        // check the same closed proof.
        let k = base_env();
        let a = cn("a");
        k.check(&refl(&a), &Term::pathp(cn("A").lift(1, 0), a.clone(), a)).unwrap();
    }

    // ---- Boundary computation (definitional) ----

    #[test]
    fn boundary_i0_computes_via_kernel_def_eq() {
        let k = base_env();
        // (refl a) @ i0  ≡  a
        let app0 = Term::papp(refl(&cn("a")), Term::IZero);
        assert!(k.def_eq(&app0, &cn("a")));
    }

    #[test]
    fn boundary_i1_computes_via_kernel_def_eq() {
        let k = base_env();
        let app1 = Term::papp(refl(&cn("a")), Term::IOne);
        assert!(k.def_eq(&app1, &cn("a")));
    }

    /// Differential check (matching this crate's standing convention): the trusted
    /// reducer and NbE agree on the boundary reduction.
    #[test]
    fn boundary_reduction_agrees_between_reducer_and_nbe() {
        let k = base_env();
        let app0 = Term::papp(refl(&cn("a")), Term::IZero);
        let app1 = Term::papp(refl(&cn("a")), Term::IOne);
        let reducer = crate::reduce::Reducer::new(k.env());
        let nbe = crate::nbe::Nbe::new(k.env());
        assert!(reducer.is_def_eq(&app0, &cn("a")));
        assert!(reducer.is_def_eq(&app1, &cn("a")));
        assert!(nbe.conv(&app0, &cn("a")));
        assert!(nbe.conv(&app1, &cn("a")));
    }

    /// A non-constant path: `⟨i⟩ (if-you-squint) …` — here just an interval variable
    /// applied through a Π (built directly): `PLam(Var(0))` has type `PathP (λi. I)
    /// …`? No — `Var(0)` inside a `PLam` body, applied to itself, is ill-typed at
    /// the outer level. Instead exercise a *non-trivial* body: `⟨i⟩ f (p @ i)`-shaped
    /// (i.e. `ap`), and check both boundaries against `f a`/`f b` for a genuine
    /// (non-refl) path `p : Path A a b` assumed as an axiom.
    #[test]
    fn ap_boundaries_compute() {
        let mut k = base_env();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        let term = ap(&cn("f"), &cn("p"));
        let ty = k.infer(&term).unwrap();
        let expected =
            Term::path(cn("A"), Term::app(cn("f"), cn("a")), Term::app(cn("f"), cn("b")));
        assert!(k.def_eq(&ty, &expected));
    }

    // ---- funext ----

    #[test]
    fn funext_typechecks() {
        let mut k = base_env();
        // h : Π x:A. Path A (f x) (g x)
        let h_ty = Term::pi(
            cn("A"),
            Term::path(cn("A"), Term::app(cn("f"), Term::Var(0)), Term::app(cn("g"), Term::Var(0))),
        );
        k.add_axiom("h", 0, h_ty).unwrap();
        let fe = funext(&cn("A"), &cn("h"));
        let ty = k.infer(&fe).unwrap();
        let expected = Term::path(Term::arrow(cn("A"), cn("A")), cn("f"), cn("g"));
        assert!(k.def_eq(&ty, &expected));
        k.check(&fe, &expected).unwrap();
    }

    // ---- Adversarial: no way to derive `False`/lie about endpoints ----

    /// A `PLam` cannot be checked against a `Path` type whose declared endpoints
    /// don't match what the body actually computes to at `i0`/`i1` — the endpoints
    /// are *read off the body*, not asserted, so this must be rejected.
    #[test]
    fn plam_cannot_lie_about_its_endpoints() {
        let k = base_env();
        // refl a : Path A a a, NOT Path A a b (a and b are distinct axioms — no
        // conversion between them).
        let claimed = Term::path(cn("A"), cn("a"), cn("b"));
        let err = k.check(&refl(&cn("a")), &claimed).unwrap_err();
        assert!(err.contains("type mismatch") || err.contains("does not match"), "got: {err}");
    }

    /// Two distinct closed axioms are never definitionally equal — a `Path` between
    /// them cannot be conjured out of nothing (matches the pre-existing kernel's
    /// treatment of any two distinct axioms/constructors, e.g. `Eq`; Phase-1 `Path`
    /// adds no new source of equations between unrelated closed terms).
    #[test]
    fn distinct_closed_values_have_no_path_between_them() {
        let k = base_env();
        assert!(!k.def_eq(&cn("a"), &cn("b")));
        // And indeed: no closed term of type `Path A a b` can be built from `a`/`b`
        // alone (`refl` only ever proves reflexivity).
        assert!(k.check(&refl(&cn("a")), &Term::path(cn("A"), cn("a"), cn("b"))).is_err());
    }

    /// `I` is not `Type`: it cannot be used as a `Π` domain (nor codomain) — nothing
    /// can quantify a real, fibrant type over the interval yet (no Kan/transport).
    #[test]
    fn interval_is_not_a_type() {
        let mut k = Kernel::new();
        let err = k.add_axiom("bad", 0, Term::pi(Term::I, Term::typ(0))).unwrap_err();
        assert!(err.contains('I'), "expected the error to mention `I`, got: {err}");
    }

    /// `I` cannot be checked as an ordinary *value* either (e.g. handed somewhere a
    /// `Type`-classified term is expected) — `infer(I)` is rejected outright.
    #[test]
    fn interval_is_not_checkable_as_a_value() {
        let k = Kernel::new();
        assert!(k.infer(&Term::I).is_err());
    }

    /// A bound interval variable cannot leak into a position that expects ordinary
    /// data: applying a genuine function to a raw path-abstraction's bound interval
    /// variable is ill-typed (its type is `I`, which is never definitionally equal to
    /// any real domain type).
    #[test]
    fn interval_variable_cannot_be_used_as_data() {
        let k = base_env();
        // `⟨i⟩ f i`  — using the bound interval variable where `f : A -> A` expects an
        // `A`. Must be rejected (the interval variable's type is `I`, not `A`).
        let bad = Term::plam(Term::app(cn("f").lift(1, 0), Term::Var(0)));
        assert!(k.infer(&bad).is_err());
    }

    /// `p @ r` requires `r : I` — applying a path to an ordinary data value (not an
    /// interval term) must be rejected.
    #[test]
    fn path_application_rejects_non_interval_argument() {
        let k = base_env();
        let bad = Term::papp(refl(&cn("a")), cn("a")); // `a : A`, not `: I`
        assert!(k.infer(&bad).is_err());
    }

    /// A **neutral** path's boundary (`h @ i0` for an axiom `h`) is forced *exactly*
    /// to its declared endpoint (`a`, here) by the type-directed boundary rule — and
    /// *only* to that endpoint: it is not conflated with an unrelated closed value
    /// `c` that happens to share `h`'s type. The rule reads the target off `p`'s own
    /// checked type; it doesn't equate `p @ i0` with anything else.
    #[test]
    fn neutral_path_application_resolves_to_its_declared_endpoint_only() {
        let mut k = base_env();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        let p_at_i0 = Term::papp(cn("p"), Term::IZero);
        assert!(k.def_eq(&p_at_i0, &cn("a"))); // the declared left endpoint
        assert!(!k.def_eq(&p_at_i0, &cn("c"))); // not an unrelated value
        assert!(!k.def_eq(&p_at_i0, &cn("b"))); // not the *other* endpoint either
    }

    /// Applying two axiomatized, unrelated paths at the same interval endpoint
    /// resolves each to its *own* declared endpoint, and those aren't conflated with
    /// each other merely because both applications are "at `i0`".
    #[test]
    fn distinct_neutral_paths_stay_distinct_at_shared_boundary() {
        let mut k = base_env();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        k.add_axiom("q", 0, Term::path(cn("A"), cn("b"), cn("c"))).unwrap();
        let p0 = Term::papp(cn("p"), Term::IZero);
        let q0 = Term::papp(cn("q"), Term::IZero);
        assert!(!k.def_eq(&p0, &q0));
    }

    /// Sanity: an environment with `Path`/`PathP` axioms and proofs re-checks cleanly
    /// under the independent re-check harness (mirrors `kernel::recheck_all_definitions`'s
    /// existing coverage, extended to Phase-1 terms).
    #[test]
    fn cubical_definitions_survive_independent_recheck() {
        let mut k = base_env();
        k.add_definition(
            "refl_a",
            0,
            Term::path(cn("A"), cn("a"), cn("a")),
            refl(&cn("a")),
        )
        .unwrap();
        k.add_definition(
            "ap_f_refl_a",
            0,
            Term::path(cn("A"), Term::app(cn("f"), cn("a")), Term::app(cn("f"), cn("a"))),
            ap(&cn("f"), &cn("refl_a")),
        )
        .unwrap();
        assert_eq!(crate::kernel::recheck_all_definitions(k.env()).unwrap(), 2);
    }

    /// Polymorphic sanity: `refl`/`Path` also work at `Type 1` (universe-generic use),
    /// not just `Prop`/`Type 0` — nothing here is hard-wired to a specific level.
    #[test]
    fn path_at_higher_universe() {
        let mut k = Kernel::new();
        k.add_axiom("T", 0, Term::typ(1)).unwrap(); // T : Type 1
        let t = cn("T");
        k.add_axiom("x", 0, t.clone()).unwrap();
        let p = refl(&cn("x"));
        let ty = k.infer(&p).unwrap();
        assert!(k.def_eq(&ty, &Term::path(t, cn("x"), cn("x"))));
    }
}
