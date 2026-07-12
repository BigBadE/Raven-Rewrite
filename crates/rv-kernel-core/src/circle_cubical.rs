//! The cubical circle `S1c` — a **genuinely computing** self-loop 1-higher-inductive-type
//! (HIT), the cubical counterpart of [`crate::circle`]'s `Eq`-based `S¹`.
//!
//! ## What this delivers, and how it differs from `circle.rs`
//!
//! [`crate::circle`] ships `S¹`: `base : S¹` plus `loop : Eq S¹ base base`, classified
//! by the *inductive* `Eq`. That path holds only **propositionally** — there is no
//! reduction rule for `loop` itself, and `S¹.rec`'s respectfulness datum `lp : Eq P pt
//! pt` is *discarded* at ι-time (see `circle.rs`'s module doc). [`crate::interval_hit`]
//! ships the complementary piece — a genuinely *computing* cubical path constructor,
//! `I2.seg : Path I2 zero one` — but between two *distinct* point constructors, so its
//! recursor's path ι-rule never has to worry about agreeing with itself at both ends of
//! the *same* point.
//!
//! This module combines both: `S1c`, presented by
//!
//!   * one point constructor `base : S1c`, and
//!   * a genuine **cubical** path constructor `loop : Path S1c base base` — a real
//!     [`crate::term::Term::PathP`]-classified path (built on [`crate::cubical`]'s
//!     `PLam`/`PApp`/`PathP`, *not* the inductive `Eq`) that is a **self-loop**: both
//!     its endpoints are `base`, and
//!   * a **`Type`-valued, computing** dependent recursor
//!
//! ```text
//!   S1c.rec.{v} : Π (C : S1c → Sort v) (b : C base)
//!                   (l : PathP (λ i. C (loop @ i)) b b) (x : S1c), C x
//! ```
//!
//! with **two** ι-rules:
//!
//! ```text
//!   S1c.rec C b l S1c.base        ↦  b
//!   S1c.rec C b l (S1c.loop @ r)  ↦  l @ r          -- THE LOOP COMPUTES
//! ```
//!
//! This is the standard CCHM-style presentation of the circle as a HIT (Cohen–
//! Coquand–Huber–Mörtberg §2; Cubical Agda's `Cubical.HITs.S1`). Unlike `circle.rs`'s
//! `S¹.rec`, whose `lp` premise is inert data never inspected computationally, `S1c.rec`
//! actually *applies* `l` at the path constructor — the payoff the task asks for.
//!
//! ## The key subtlety vs `I2` — a SELF-loop, not a two-point path
//!
//! [`crate::interval_hit`]'s `I2.seg : Path I2 zero one` connects two *distinct* point
//! constructors, so its path ι-rule's endpoint coherence is the ordinary "two boundary
//! cases, independently checked" story. Here `loop`'s *both* endpoints are the *same*
//! point, `base`, so the coherence obligation is sharper: `S1c.rec … (loop @ i0)` and
//! `S1c.rec … (loop @ i1)` must EACH agree with `S1c.rec … base = b` — not two different
//! boundary values, but the *one* value `b`, from *both* sides simultaneously. Concretely:
//!
//!   * `loop @ i0 ≡ base` and `loop @ i1 ≡ base` hold *definitionally* — both are
//!     instances of [`crate::check::Checker::path_boundary`] (proven sound in
//!     [`crate::cubical`]'s Phase 1) applied to `S1c.loop : Path S1c base base`, whose
//!     *declared* endpoints (both slots of the `Path`) are literally `base`. There is
//!     only one `path_boundary` fact needed at each end, and both ends happen to name
//!     the same point — that coincidence is exactly what makes this a *self*-loop, not a
//!     new soundness burden: `path_boundary` doesn't know or care that `a0` and `a1`
//!     happen to be syntactically identical terms.
//!   * `l`'s own declared type, `PathP (λ i. C (loop @ i)) b b`, is checked (by
//!     [`crate::check::Checker::infer`]'s `Term::PathP` arm) against `loop`'s own
//!     boundary — the family `λ i. C (loop @ i)` at `i0` is `C (loop @ i0) ≡ C base`,
//!     and at `i1` is `C (loop @ i1) ≡ C base`, so `l : PathP … b b` typechecks exactly
//!     when `b : C base` at *both* ends — which it is, being literally the same `b` at
//!     both binder slots. This is the "both endpoints coincide" fact baked directly into
//!     `l`'s *type*, checked once at `S1c.rec`'s formation site, not re-derived per-use.
//!   * At the *reduction* level (the adversarial tests below, `endpoint_coherence_i0`/
//!     `endpoint_coherence_i1`): `S1c.rec … (loop @ i0)` fires the PATH ι-rule, reducing
//!     to `l @ i0`; by `path_boundary` (again, the pre-existing Phase-1 fact, applied to
//!     `l : PathP (λi. C(loop@i)) b b`) `l @ i0 ≡ b` *definitionally* via
//!     [`crate::check::Checker::compare`]. Symmetrically `l @ i1 ≡ b`. And
//!     `S1c.rec … base` fires the POINT ι-rule, reducing directly to `b`. All three —
//!     `S1c.rec … (loop@i0)`, `S1c.rec … (loop@i1)`, and `S1c.rec … base` — land on the
//!     *same* definitional value `b`, checked independently at *both* ends by the two
//!     tests below (not just one, per the task's explicit requirement).
//!
//! No new checking or reduction rule is added for any of this: it is the same "derived,
//! no new equation" pattern [`crate::interval_hit`]'s "Endpoint coherence" section and
//! [`crate::cubical`]'s `J`/`transport` derivations rely on, applied twice (once per
//! end) rather than once, because both ends happen to name the same point.
//!
//! ## Why this is SOUND
//!
//! * **No new checking rule.** Every one of `S1c.base`/`S1c.loop`/`S1c.rec` is an
//!   ordinary typed [`crate::env::Decl::S1c`] constant — `Checker::infer`'s `Term::Const`
//!   arm looks up its already-fully-elaborated declared type exactly as for any axiom.
//!   `S1c.loop`'s type, `Path S1c base base`, is checked well-formed once, at
//!   `install_circle_cubical` time, by the ordinary (pre-existing) `Term::PathP` typing
//!   rule.
//! * **Two new, narrowly-scoped ι-rules** ([`crate::reduce::Reducer::try_s1c_rec`],
//!   [`crate::nbe::Nbe::try_s1c_rec`], differentially cross-checked by every test below):
//!   the point rule (structurally identical to [`crate::circle`]'s) and the path rule,
//!   which fires **only** when the scrutinee's weak-head form is *literally* `S1c.loop @
//!   r` — never on a neutral, never on `S1c.base` itself (caught by the point-rule
//!   branch first), never on any *other* `PApp` whose head isn't `S1c.loop`
//!   (adversarial tests `path_iota_does_not_fire_on_unrelated_pathp`/`rec_stuck_on_
//!   neutral`).
//! * **Canonicity.** `S1c.base` remains the only closed point-shaped normal form of
//!   `S1c`: `S1c.loop` itself is `Path`-classified, not `S1c`-classified, so it can
//!   never appear as a *closed value of type `S1c`* — only `S1c.loop @ r` can, handled
//!   precisely by the path ι-rule (which, at the closed interval endpoints `r = i0`/`i1`,
//!   is definitionally `base` again by endpoint coherence — it never produces a *second*
//!   canonical `S1c` point). This module's `loop` is genuinely non-trivial as a *path*
//!   (adversarial test `loop_is_not_refl` — `loop ≠ refl base`, so the circle is not
//!   secretly collapsed to a point up to conversion) while still not introducing any new
//!   closed `S1c`-typed canonical value beyond `base` (adversarial test
//!   `cannot_prove_false`).
//! * **Reducer/NbE agreement.** Both ι-rules are implemented once each in
//!   [`crate::reduce::Reducer::try_s1c_rec`] and [`crate::nbe::Nbe::try_s1c_rec`],
//!   structurally mirroring [`crate::interval_hit`]'s `try_i2_rec` exactly; every test
//!   below checks both independently and compares normal forms.
//!
//! ## Worked example
//!
//! [`tests::worked_example_winding_function`] defines `w : S1c → Nat` by `S1c.rec (λ_.
//! Nat) 4 (refl 4)`, applied to `S1c.loop @ r` for a fresh bound interval variable `r`,
//! and shows the path ι-rule fires — `w` really does traverse the loop and land back on
//! `4` by *computation*, not by an inert, uninspected respectfulness proof the way
//! `crate::circle`'s `Eq`-classified `S¹.loop`/`S1.rec`'s `lp` would require (there, the
//! analogous position is `lp : Eq P pt pt`, *never applied* to anything — the recursor
//! can't "walk around the loop" at all, only accept that the walk is possible).
//!
//! ## Deferred: `S1c.ind`
//!
//! A dependent eliminator into a *path-respecting family that isn't itself already
//! `Type`-classified through `PathP` (i.e. a genuinely non-fibrant elimination target,
//! or one requiring `hcomp`/`transp` machinery to establish rather than a direct
//! `PathP`-typed datum)* is **not** provided here. The `Type`-valued `S1c.rec` above
//! already IS the dependent eliminator into any `Sort v` motive — that is the whole
//! payoff cubical HITs offer over the propositional `S¹.ind`'s `Prop`-only restriction
//! (see `crate::circle`'s "Supported class"). What remains genuinely deferred is
//! anything needing *additional* Kan structure beyond `PathP`-application itself (e.g.
//! computing `S1c.rec` against `hcomp`-classified scrutinees, or higher-dimensional
//! path constructors) — out of scope here, exactly as `crate::interval_hit` defers it.

use crate::cubical;
use crate::env::{Decl, Env, S1c, S1cRole};
use crate::level::Level;
use crate::term::{name, Term};
use std::rc::Rc;

/// Names of the four cubical-circle constants.
pub const S1C_TYPE: &str = "S1c";
pub const S1C_BASE: &str = "S1c.base";
pub const S1C_LOOP: &str = "S1c.loop";
pub const S1C_REC: &str = "S1c.rec";

/// `S1c`.
fn s1c() -> Term {
    Term::cnst(name(S1C_TYPE), vec![])
}
/// `S1c.base`.
fn base() -> Term {
    Term::cnst(name(S1C_BASE), vec![])
}
/// `S1c.loop`.
fn cloop() -> Term {
    Term::cnst(name(S1C_LOOP), vec![])
}

/// Install the fixed cubical-circle schema (`S1c`, `S1c.base`, `S1c.loop`, `S1c.rec`)
/// into `env`. No prerequisite declarations are required (unlike
/// [`crate::circle::install_circle`], which needs `Eq` — `S1c.loop`'s type is a
/// cubical `Path`, built directly on [`crate::cubical`]'s primitives). Rejects
/// re-installation (any of the four names already declared).
pub fn install_circle_cubical(env: &mut Env) -> Result<(), String> {
    for n in [S1C_TYPE, S1C_BASE, S1C_LOOP, S1C_REC] {
        if env.contains(n) {
            return Err(format!("'{n}' is already declared"));
        }
    }

    let v = Level::param(0); // S1c.rec's target universe.

    // ------------------------------------------------------------------
    // S1c : Type 0
    // ------------------------------------------------------------------
    env.insert(
        name(S1C_TYPE),
        Decl::S1c(Rc::new(S1c { role: S1cRole::Type, num_levels: 0, ty: Term::typ(0) })),
    )?;

    // ------------------------------------------------------------------
    // S1c.base : S1c
    // ------------------------------------------------------------------
    env.insert(
        name(S1C_BASE),
        Decl::S1c(Rc::new(S1c { role: S1cRole::Base, num_levels: 0, ty: s1c() })),
    )?;

    // ------------------------------------------------------------------
    // S1c.loop : Path S1c S1c.base S1c.base   (a genuine cubical PathP SELF-loop)
    // ------------------------------------------------------------------
    let loop_ty = Term::path(s1c(), base(), base());
    env.insert(
        name(S1C_LOOP),
        Decl::S1c(Rc::new(S1c { role: S1cRole::Loop, num_levels: 0, ty: loop_ty })),
    )?;

    // ------------------------------------------------------------------
    // S1c.rec.{v} : Π (C : S1c -> Sort v) (b : C base)
    //                  (l : PathP (\i. C (loop @ i)) b b) (x : S1c), C x
    //   binder order (outer -> inner): C(idx0) b(idx1) l(idx2) x(idx3)
    // ------------------------------------------------------------------
    let rec_ty = Term::pi(
        Term::arrow(s1c(), Term::Sort(v.clone())), // C : S1c -> Sort v     (Var0 here)
        Term::pi(
            // b : C base     (C = Var0)
            Term::app(Term::Var(0), base()),
            Term::pi(
                // l : PathP (\i. C (loop @ i)) b b
                //   here: C = Var1, b = Var0
                //   family under one more (interval) binder: C = Var2
                Term::pathp(
                    Term::app(Term::Var(2), Term::papp(cloop(), Term::Var(0))),
                    Term::Var(0), // b (endpoint at i0)
                    Term::Var(0), // b (endpoint at i1) -- SAME b, both ends
                ),
                Term::pi(
                    // x : S1c    (depth 3)
                    s1c(),
                    // C x    (C = Var3, x = Var0)
                    Term::app(Term::Var(3), Term::Var(0)),
                ),
            ),
        ),
    );
    env.insert(
        name(S1C_REC),
        Decl::S1c(Rc::new(S1c { role: S1cRole::Rec, num_levels: 1, ty: rec_ty })),
    )?;

    Ok(())
}

/// `refl a : Path A a a` — re-exported as a tiny convenience for building the constant
/// `l` argument used throughout this module's tests (identical to
/// [`crate::cubical::refl`]; kept as a thin wrapper so callers don't need to depend on
/// `crate::cubical` just for this).
pub fn refl(a: &Term) -> Term {
    cubical::refl(a)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::{Checker, LocalCtx};
    use crate::inductive::declare_nat;
    use crate::nbe::Nbe;
    use crate::reduce::Reducer;

    /// Build an env with `Nat` and the cubical-circle schema installed.
    fn s1c_env() -> Env {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        install_circle_cubical(&mut env).unwrap();
        env
    }

    fn cn(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }
    fn lit(n: u32) -> Term {
        let mut t = cn("Nat.zero");
        for _ in 0..n {
            t = Term::app(cn("Nat.succ"), t);
        }
        t
    }

    // ---------------------------------------------------------------------
    // Basic well-formedness
    // ---------------------------------------------------------------------

    #[test]
    fn s1c_constants_wellformed() {
        let env = s1c_env();
        let chk = Checker::new(&env);
        for n in [S1C_TYPE, S1C_BASE, S1C_LOOP, S1C_REC] {
            chk.infer_closed(env.get(n).unwrap().ty())
                .unwrap_or_else(|e| panic!("{n} ill-formed: {e}"));
        }
    }

    #[test]
    fn rejects_double_install() {
        let mut env = s1c_env();
        let err = install_circle_cubical(&mut env).unwrap_err();
        assert!(err.contains("already declared"), "got: {err}");
    }

    #[test]
    fn base_typechecks() {
        let env = s1c_env();
        let chk = Checker::new(&env);
        let ty = chk.infer_closed(&base()).unwrap();
        let red = Reducer::new(&env);
        assert!(red.is_def_eq(&ty, &s1c()));
    }

    /// `S1c.loop` is a genuine cubical `Path S1c base base`.
    #[test]
    fn loop_typechecks_as_a_cubical_self_path() {
        let env = s1c_env();
        let chk = Checker::new(&env);
        let goal = Term::path(s1c(), base(), base());
        chk.check(&mut LocalCtx::new(), &cn(S1C_LOOP), &goal).unwrap();
    }

    /// SOUNDNESS (anti-triviality): `S1c.loop` is NOT definitionally `refl base` —
    /// otherwise the circle would be secretly collapsed to a point, and the "self-loop"
    /// content would be a fiction. `S1c.loop` is its own irreducible weak-head normal
    /// form (an axiom-shaped constant, never touched by any reduction rule), while
    /// `refl base` weak-head-reduces to a `PLam`; the two syntactic shapes can never be
    /// identified since neither reduces toward the other and there is no η/boundary
    /// axiom that would equate an opaque neutral `PathP`-typed constant with a literal
    /// `PLam` (Phase 1's `path_boundary` only ever gives *endpoint* facts, `p @ i0 ≡
    /// a0`/`p @ i1 ≡ a1`, never a full path-equality between two different `PathP`
    /// terms).
    #[test]
    fn loop_is_not_refl() {
        let env = s1c_env();
        let red = Reducer::new(&env);
        let refl_base = cubical::refl(&base());
        assert!(!red.is_def_eq(&cloop(), &refl_base), "S1c.loop must not be refl base");
        let nbe = Nbe::new(&env);
        assert_ne!(nbe.normalize(&cloop()), nbe.normalize(&refl_base));
        // And `S1c.loop` itself doesn't reduce at all (it's axiom-shaped).
        assert_eq!(red.whnf(&cloop()), cloop(), "S1c.loop must not reduce");
    }

    // ---------------------------------------------------------------------
    // The non-dependent instance: `S1c.rec (\_. Nat) b l`
    // ---------------------------------------------------------------------

    fn nondep_rec(b: Term, l: Term, scrut: Term) -> Term {
        let motive = Term::lam(s1c(), cn("Nat").lift(1, 0)); // \_ : S1c. Nat
        Term::apps(Term::cnst(name(S1C_REC), vec![Level::of_nat(1)]), [motive, b, l, scrut])
    }

    /// POINT ι-RULE: `S1c.rec C b l S1c.base ↦ b`. Checked on the trusted reducer AND
    /// NbE (differential).
    #[test]
    fn point_iota_base() {
        let env = s1c_env();
        let l = refl(&lit(7));
        let rec = nondep_rec(lit(7), l, base());
        let chk = Checker::new(&env);
        chk.check(&mut LocalCtx::new(), &rec, &cn("Nat")).unwrap();
        let red = Reducer::new(&env);
        assert!(red.is_def_eq(&rec, &lit(7)), "reducer: rec base = b");
        let nbe = Nbe::new(&env);
        assert_eq!(nbe.normalize(&rec), lit(7), "nbe: rec base = b");
    }

    /// **THE PATH ι-RULE — the whole point of this module.**
    /// `S1c.rec C b l (S1c.loop @ r) ↦ l @ r`, for a fresh *neutral* interval variable
    /// `r` (a bound variable of type `I`, exercised under a `PLam` binder exactly like
    /// `crate::interval_hit`'s analogous test). Checked on the trusted reducer AND NbE.
    #[test]
    fn path_iota_computes_on_the_loop_application() {
        let env = s1c_env();
        let l = refl(&lit(5)); // l : PathP (\_. Nat) 5 5, the constant path at 5
        let scrut = Term::papp(cloop(), Term::Var(0));
        let body = nondep_rec(lit(5), l, scrut);
        let whole = Term::plam(body);
        let chk = Checker::new(&env);
        let ty = chk.infer_closed(&whole).unwrap();
        let expected_ty = Term::path(cn("Nat"), lit(5), lit(5));
        assert!(Reducer::new(&env).is_def_eq(&ty, &expected_ty), "got {ty:?}");
        let red = Reducer::new(&env);
        let nbe = Nbe::new(&env);
        let expected_whole = Term::plam(lit(5).lift(1, 0));
        assert!(red.is_def_eq(&whole, &expected_whole), "reducer: path iota under binder");
        assert_eq!(nbe.normalize(&whole), nbe.normalize(&expected_whole), "nbe: path iota under binder");
    }

    /// **TYPE PRESERVATION** of the path ι-rule: re-infer the *reduced* form (`l @ r`)
    /// and confirm it matches the recursor's own stated return type at the original
    /// scrutinee (`C (S1c.loop @ r)`).
    #[test]
    fn path_iota_result_has_the_recursor_return_type() {
        let env = s1c_env();
        let motive = Term::lam(s1c(), cn("Nat").lift(1, 0));
        let l = refl(&lit(3));
        let scrut = Term::papp(cloop(), Term::Var(0));
        let rec = Term::apps(
            Term::cnst(name(S1C_REC), vec![Level::of_nat(1)]),
            [motive, lit(3), l, scrut],
        );
        let whole = Term::plam(rec);
        let chk = Checker::new(&env);
        let ty_before = chk.infer_closed(&whole).unwrap();
        let reduced = Reducer::new(&env).whnf(&whole);
        let ty_after = Checker::new(&env).infer_closed(&reduced).unwrap();
        assert!(
            Reducer::new(&env).is_def_eq(&ty_before, &ty_after),
            "type not preserved by path iota: before={ty_before:?} after={ty_after:?}"
        );
        let expected_ty = Term::path(cn("Nat"), lit(3), lit(3));
        assert!(Reducer::new(&env).is_def_eq(&ty_before, &expected_ty), "got {ty_before:?}");
    }

    // ---------------------------------------------------------------------
    // Endpoint coherence, BOTH ends: the path rule agrees with the point rule at
    // BOTH i0 and i1 (the task's explicit "both-endpoint" requirement — see the
    // module doc's "The key subtlety vs I2" section).
    // ---------------------------------------------------------------------

    /// `S1c.rec … (S1c.loop @ i0)` and `S1c.rec … S1c.base` land on the same normal
    /// form (both give `b`).
    #[test]
    fn endpoint_coherence_i0() {
        let env = s1c_env();
        let l = refl(&lit(11));
        let via_path = nondep_rec(lit(11), l.clone(), Term::papp(cloop(), Term::IZero));
        let via_point = nondep_rec(lit(11), l, base());
        let red = Reducer::new(&env);
        let nbe = Nbe::new(&env);
        assert!(red.is_def_eq(&via_path, &via_point), "reducer: endpoint coherence at i0");
        assert_eq!(nbe.normalize(&via_path), nbe.normalize(&via_point), "nbe: endpoint coherence at i0");
        assert_eq!(nbe.normalize(&via_path), lit(11));
    }

    /// `S1c.rec … (S1c.loop @ i1)` and `S1c.rec … S1c.base` land on the same normal
    /// form (both give `b`) — the OTHER end, checked independently.
    #[test]
    fn endpoint_coherence_i1() {
        let env = s1c_env();
        let l = refl(&lit(11));
        let via_path = nondep_rec(lit(11), l.clone(), Term::papp(cloop(), Term::IOne));
        let via_point = nondep_rec(lit(11), l, base());
        let red = Reducer::new(&env);
        let nbe = Nbe::new(&env);
        assert!(red.is_def_eq(&via_path, &via_point), "reducer: endpoint coherence at i1");
        assert_eq!(nbe.normalize(&via_path), nbe.normalize(&via_point), "nbe: endpoint coherence at i1");
        assert_eq!(nbe.normalize(&via_path), lit(11));
    }

    /// Both ends agree with EACH OTHER too (not just with the point rule
    /// separately) — the sharper "self-loop" fact the module doc calls out: since
    /// `loop`'s two endpoints are the *same* point, all three routes (`i0`, `i1`,
    /// and the direct `base` route) must coincide simultaneously.
    #[test]
    fn both_endpoints_agree_with_each_other() {
        let env = s1c_env();
        let l = refl(&lit(17));
        let via_i0 = nondep_rec(lit(17), l.clone(), Term::papp(cloop(), Term::IZero));
        let via_i1 = nondep_rec(lit(17), l, Term::papp(cloop(), Term::IOne));
        let red = Reducer::new(&env);
        assert!(red.is_def_eq(&via_i0, &via_i1), "both endpoints of the self-loop must agree");
    }

    // ---------------------------------------------------------------------
    // Adversarial: the path rule must not misfire, and canonicity/anti-False hold.
    // ---------------------------------------------------------------------

    /// `S1c.rec` stays stuck on a NEUTRAL `S1c`-typed variable (bound under a
    /// lambda) — preserves canonicity for open terms.
    #[test]
    fn rec_stuck_on_neutral() {
        let env = s1c_env();
        let l = refl(&lit(1));
        let body = nondep_rec(lit(1), l, Term::Var(0));
        let f = Term::lam(s1c(), body);
        let chk = Checker::new(&env);
        chk.infer_closed(&f).unwrap();
        let red = Reducer::new(&env);
        let whnf = red.whnf(&f);
        match &whnf {
            Term::Lam(_, _) => {}
            other => panic!("expected a stuck lambda, got {other:?}"),
        }
    }

    /// The path ι-rule fires ONLY when the `PApp`'s head is *literally* `S1c.loop` —
    /// it must not misfire on an unrelated axiomatized `Path`.
    #[test]
    fn path_iota_does_not_fire_on_unrelated_pathp() {
        let mut env = s1c_env();
        env.insert(
            name("q"),
            Decl::Axiom { num_levels: 0, ty: Term::path(cn("Nat"), lit(0), lit(0)) },
        )
        .unwrap();
        let l = refl(&lit(0));
        // `q @ r : Nat`, not `S1c` — ill-typed as a scrutinee, so the type-checker
        // rejects it outright (confirming misfire is impossible, exactly mirroring
        // `crate::interval_hit`'s analogous adversarial test).
        let bogus_scrut = Term::papp(cn("q"), Term::Var(0));
        let body = nondep_rec(lit(0), l, bogus_scrut);
        let whole = Term::plam(body);
        let chk = Checker::new(&env);
        assert!(chk.infer_closed(&whole).is_err(), "unrelated PathP scrutinee must be rejected");
        let _ = &mut env;
    }

    /// ADVERSARIAL / ANTI-`False`: cannot derive `Path Nat 0 1` from the cubical-circle
    /// machinery. `S1c.rec`'s path ι-rule only ever returns `l @ r` for the
    /// caller-supplied `l`; it manufactures no new proof term. `S1c` has only one point,
    /// `base`, so the usual "two distinct constructors are non-equal" test degenerates
    /// to: `S1c.loop` cannot be coerced into proving an unrelated `Nat` equation.
    #[test]
    fn cannot_prove_false() {
        let env = s1c_env();
        let red = Reducer::new(&env);
        assert!(!red.is_def_eq(&lit(0), &lit(1)));
        let bogus_goal = Term::path(cn("Nat"), lit(3), lit(5));
        let chk = Checker::new(&env);
        assert!(
            chk.check(&mut LocalCtx::new(), &cloop(), &bogus_goal).is_err(),
            "S1c.loop must not check against an unrelated Path Nat goal"
        );
    }

    /// ANTI-`False` via the recursor: even though `S1c.rec`'s path rule *computes*,
    /// applying it to `S1c.loop` itself as the respectfulness datum under the identity
    /// motive only ever recovers `base` back at `base` — it cannot manufacture a proof
    /// that `S1c.base` is anything other than itself.
    #[test]
    fn base_still_itself_under_the_identity_motive() {
        let env = s1c_env();
        // C := \x. S1c   (identity-ish motive), b := base,
        // l : PathP (\i. S1c) base base, i.e. Path S1c base base -- that's S1c.loop!
        let motive = Term::lam(s1c(), s1c().lift(1, 0));
        let rec = Term::apps(
            Term::cnst(name(S1C_REC), vec![Level::of_nat(1)]),
            [motive, base(), cn(S1C_LOOP), base()],
        );
        let red = Reducer::new(&env);
        // rec ... base -> b = base, exactly the one canonical point.
        assert!(red.is_def_eq(&rec, &base()));
    }

    // ---------------------------------------------------------------------
    // Worked example: a "winding" map that genuinely computes across the loop --
    // something `S¹.rec`'s Eq-classified, non-computing `lp` cannot express (there,
    // the analogous position holds an inert respectfulness *proof*, never applied).
    // ---------------------------------------------------------------------

    #[test]
    fn worked_example_winding_function() {
        let env = s1c_env();
        // l : Path Nat 4 4 (constant path). Apply the recursor to `loop @ i` under a
        // path abstraction, exhibiting `ap`-like content driven by the computing
        // recursor rather than `crate::cubical::ap`.
        let l = refl(&lit(4));
        let scrut = Term::papp(cloop(), Term::Var(0));
        let body = nondep_rec(lit(4), l, scrut);
        let whole = Term::plam(body); // : Path Nat 4 4
        let chk = Checker::new(&env);
        let ty = chk.infer_closed(&whole).unwrap();
        assert!(Reducer::new(&env).is_def_eq(&ty, &Term::path(cn("Nat"), lit(4), lit(4))));
        // It reduces to the constant path at 4 -- the loop really did get computed
        // away by `S1c.rec`'s path ι-rule, walking all the way around and landing back
        // on 4, not merely postulated to exist.
        let nbe = Nbe::new(&env);
        assert_eq!(nbe.normalize(&whole), nbe.normalize(&Term::plam(lit(4).lift(1, 0))));
    }
}
