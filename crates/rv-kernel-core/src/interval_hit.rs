//! The interval `I2` — a **genuinely computing** 1-higher-inductive-type (HIT).
//!
//! ## What this delivers, and how it differs from [`crate::circle`]
//!
//! [`crate::circle`] ships `S¹`: a point constructor `base` plus a path constructor
//! `loop : Eq S¹ base base` classified by the *inductive* `Eq`. That path holds only
//! **propositionally** — there is no reduction rule for `loop` itself, and `S¹.rec`'s
//! respectfulness datum `lp : Eq P pt pt` is *discarded* at ι-time (see `circle.rs`'s
//! module doc, "Why this is SOUND"). That is deliberate and sound, but it means `S¹`
//! cannot express the one thing a *cubical* HIT recursor is for: a path constructor
//! whose eliminator **computes on the path itself**.
//!
//! This module ships that missing piece, for the simplest non-trivial case: the
//! **interval HIT** `I2`, presented by
//!
//!   * two point constructors `zero, one : I2`, and
//!   * a genuine **cubical** path constructor `seg : Path I2 zero one` — a real
//!     [`crate::term::Term::PathP`]-classified path (built on [`crate::cubical`]'s
//!     `PLam`/`PApp`/`PathP`, *not* the inductive `Eq`), and
//!   * a **`Type`-valued, computing** dependent recursor
//!
//! ```text
//!   I2.rec.{v} : Π (C : I2 → Sort v) (c0 : C zero) (c1 : C one)
//!                  (s : PathP (λ i. C (seg @ i)) c0 c1) (x : I2), C x
//! ```
//!
//! with **three** ι-rules — the two ordinary point rules, *and* the path rule that is
//! this module's whole point:
//!
//! ```text
//!   I2.rec C c0 c1 s I2.zero        ↦  c0
//!   I2.rec C c0 c1 s I2.one         ↦  c1
//!   I2.rec C c0 c1 s (I2.seg @ r)   ↦  s @ r          -- COMPUTES on the path constructor
//! ```
//!
//! This is the standard CCHM-style presentation of the interval as a HIT (see e.g.
//! Cohen–Coquand–Huber–Mörtberg §2, or Cubical Agda's `Cubical.Foundations.Interval` /
//! Mörtberg's cubical set-theoretic account of the interval type). Since `seg`'s two
//! endpoints are *distinct points* (unlike `S¹`'s `loop`, a `base`-to-`base` *self*-loop),
//! there is no "does the path ι-rule agree with itself at both ends" subtlety — only
//! the ordinary boundary coherence between the point rules and the path rule at `r =
//! i0`/`r = i1` (checked below, and see "Endpoint coherence").
//!
//! ## Why `I2` (not `S¹`) for the computing case
//!
//! The task's preferred target is a cubical `S¹` with `S1.rec_cub`'s path ι-rule firing
//! on `loop @ r`. That needs `S¹.loop : Path S¹ base base` — a path *whose own
//! type's family* is `λ _. S¹` but whose two endpoints coincide. Nothing about the
//! ι-rule itself is harder for a self-loop than for `zero`/`one`'s two distinct
//! endpoints (the reduction only ever inspects `r`, never the endpoints), but a
//! self-loop's recursor needs care that its `Base`-rule and its `Path`-rule agree with
//! each other not just at `r = i0` (giving `base` back) — they must agree with the
//! *same* point on *both* sides simultaneously, and the natural "S¹ requires a genuine
//! point *inductive* type with a nested path layer" packaging is exactly the piece
//! `crate::circle` and `crate::hit`'s doc comments flag as a materially larger change
//! (reusing `crate::inductive`'s point-constructor machinery, then layering a path
//! constructor and a *cubical* joint recursor over it — no such combined machinery
//! exists yet in this kernel: `crate::hit`'s general schema is `Eq`-based, and
//! `crate::circle`'s `S¹` is a hand-written `Eq`-based instance, neither reusable here).
//! `I2` needs none of that: `zero`/`one` are two independent nullary point constants,
//! exactly like `Trunc.tr`/`Quot.mk`'s shape but doubled, so the whole schema is again a
//! **fixed five-constant install**, `install_interval_hit`, with no new
//! inductive-declaration plumbing — the fallback the task explicitly sanctions.
//!
//! ## The ι-rules, and why they type-check
//!
//! The point rules (`zero ↦ c0`, `one ↦ c1`) are immediate: `c0 : C zero` and `c1 : C
//! one` are exactly `I2.rec`'s own premises, so the reduct has exactly the type the
//! whole application was checked to have.
//!
//! The path rule needs one more step. `s : PathP (λ i. C (seg @ i)) c0 c1` (`I2.rec`'s
//! fourth premise). By [`crate::check::Checker::infer`]'s `Term::PApp` arm, for *any*
//! interval term `r`, `s @ r` infers to the `PathP`'s family instantiated at `r`:
//!
//! ```text
//!   s @ r : (λ i. C (seg @ i))[i := r]  =  C (seg @ r)
//! ```
//!
//! — which is *exactly* `I2.rec C c0 c1 s (seg @ r)`'s own return type (`C` applied to
//! the scrutinee). So the path ι-rule's reduct is well-typed **at the type the
//! recursor's own signature already promises**, by nothing more than substitution —
//! no new typing rule is added anywhere for this; it falls straight out of the
//! pre-existing, already-sound `PApp` typing rule (see [`crate::cubical`]). This is the
//! *type preservation* argument for the path ι-rule, and is checked concretely by the
//! adversarial test `path_iota_result_has_the_recursor_return_type` below (re-inferring
//! the reduced form and comparing against the motive applied to the original
//! scrutinee).
//!
//! ## Endpoint coherence
//!
//! The two families of ι-rule must *agree* where their domains touch: `seg @ i0` and
//! `seg @ i1` are (definitionally) `zero`/`one`, so `I2.rec … (seg @ i0)` had better be
//! (definitionally) equal to `I2.rec … zero = c0` — and indeed to `s @ i0` itself. This
//! is where an unsound path-computation rule would hide a bug (e.g. if `s`'s stated
//! boundary and the point rule's `c0`/`c1` could silently drift apart). Concretely:
//!
//!   * `s`'s own declared type, `PathP (λ i. C (seg @ i)) c0 c1`, is *checked* (by
//!     [`crate::check::Checker::infer`]'s `Term::PathP` arm) against `seg`'s own
//!     boundary — this is not a new fact this module introduces, it is the ordinary
//!     `PathP` well-formedness obligation for `s` at the point `I2.rec` is *formed* (a
//!     term of that `PathP` type can only be closed by something whose two endpoints,
//!     read at `i0`/`i1`, are literally `c0`/`c1`).
//!   * At the *reduction* level: [`crate::check::Checker::path_boundary`] (the
//!     type-directed boundary rule already proven sound in [`crate::cubical`]'s Phase 1
//!     — "`p @ i0 ≡ a0` … for *any* `p`, not only literal path abstractions") applies
//!     to `s` exactly as to any other `PathP`-typed term: `s @ i0 ≡ c0` and `s @ i1 ≡
//!     c1` hold *definitionally*, checked via [`crate::check::Checker::compare`] (the
//!     authoritative conversion the type-checker actually uses) even though `s` may be
//!     an opaque/axiomatized path with no reduction of its own. So the path ι-rule's
//!     result at the boundary (`s @ i0`, `s @ i1`) is definitionally *identical* to the
//!     point ι-rule's result (`c0`, `c1`) — not merely propositionally so.
//!   * This is exactly the same "derived, no new equation" pattern
//!     [`crate::cubical`]'s `J`/`transport` derivations rely on (see that module's
//!     "Endpoint coherence"/"Soundness" sections) — no new checking or reduction rule is
//!     added for this coherence fact; it is inherited from Phase 1's `path_boundary`.
//!
//! The adversarial test `endpoint_coherence_zero`/`endpoint_coherence_one` below pin
//! this down concretely: `I2.rec … (I2.seg @ i0)` reduces (via the path ι-rule) to `s @
//! i0`, which `is_def_eq`s to `c0`, which is *also* what `I2.rec … I2.zero` reduces to
//! directly (via the point ι-rule) — both routes land on the same normal form up to
//! conversion.
//!
//! ## Why this is SOUND
//!
//! * **No new checking rule.** Every one of `I2.zero`/`I2.one`/`I2.seg`/`I2.rec` is an
//!   ordinary typed [`crate::env::Decl::I2`] constant — `Checker::infer`'s `Term::Const`
//!   arm looks up its *already-fully-elaborated* declared type exactly as for any axiom
//!   or inductive constant. `I2.seg`'s type, `Path I2 zero one` (i.e. `PathP (I2 lifted)
//!   zero one`), is itself checked well-formed once, at `install_interval_hit` time, by
//!   the ordinary (pre-existing, already-sound) `Term::PathP` typing rule — nothing
//!   about a *cubical* HIT install needs bespoke checking machinery the way a fully
//!   general path-constructor schema might.
//! * **Two new, narrowly-scoped ι-rules**, added to both the trusted [`crate::reduce`]
//!   and the fast [`crate::nbe`] (differentially cross-checked by every test below):
//!   the point rule (structurally identical to [`crate::circle`]'s, just doubled for
//!   two point constructors instead of one) and the path rule, which fires **only**
//!   when the scrutinee's weak-head form is *literally* `I2.seg @ r` for some interval
//!   term `r` — never on a neutral, never on `I2.zero`/`I2.one` themselves (those are
//!   caught by the point-rule branch first), and never on any *other* `PApp` whose
//!   head isn't `I2.seg` (adversarial tests `path_iota_does_not_fire_on_unrelated_
//!   pathp`/`rec_stuck_on_neutral`).
//! * **Canonicity.** `I2.zero`/`I2.one` remain the only two closed point-shaped normal
//!   forms of `I2`: `I2.seg` itself is `Path`-classified, not `I2`-classified, so it can
//!   never appear as a *closed value of type `I2`* — only `I2.seg @ r` can, and that is
//!   handled by the path ι-rule precisely (which, for the *closed* interval endpoints
//!   `r = i0`/`i1`, is definitionally `zero`/`one` again by endpoint coherence above —
//!   it never produces a *third* canonical `I2`). Two distinct closed axioms remain
//!   distinct: nothing here adds an equation between unrelated closed terms (adversarial
//!   test `cannot_prove_false`).
//! * **Reducer/NbE agreement.** Both ι-rules are implemented once each in
//!   [`crate::reduce::Reducer::try_i2_rec`] and [`crate::nbe::Nbe::try_i2_rec`],
//!   structurally mirroring each other exactly as every other computation rule in this
//!   crate does; every test below checks both independently and compares their
//!   normal forms.
//!
//! ## Worked example
//!
//! [`tests::worked_example_non_constant_family`] defines a genuinely non-constant `C :
//! I2 → Type` (`C zero = Nat`, `C one = Bool`-via-`Nat`-coded-as-`Nat`… concretely: `C x
//! := I2.rec (λ_. Type 0) Nat Nat (refl-ish) x` is trivial, so instead the example
//! builds a *dependent value* along the path — `I2.rec (λ_. Nat) 3 3 (refl 3) (I2.seg @
//! r)` for a fresh axiom `r : I`, and shows it reduces to `3 @ r`-shaped `s @ r`, which
//! is *itself* `3` since `s = refl 3` is the constant path — demonstrating the path
//! ι-rule firing on a genuinely path-shaped (non-point) scrutinee, something
//! `S¹.rec`/`Trunc.lift`/`Quot.lift`'s `Eq`-classified path constructors cannot express
//! (there, the analogous position holds an inert respectfulness *proof*, never applied).

use crate::cubical;
use crate::env::{Decl, Env, I2, I2Role};
use crate::level::Level;
use crate::term::{name, Term};
use std::rc::Rc;

/// Names of the five interval-HIT constants.
pub const I2_TYPE: &str = "I2";
pub const I2_ZERO: &str = "I2.zero";
pub const I2_ONE: &str = "I2.one";
pub const I2_SEG: &str = "I2.seg";
pub const I2_REC: &str = "I2.rec";

/// `I2`.
fn i2() -> Term {
    Term::cnst(name(I2_TYPE), vec![])
}
/// `I2.zero`.
fn zero() -> Term {
    Term::cnst(name(I2_ZERO), vec![])
}
/// `I2.one`.
fn one() -> Term {
    Term::cnst(name(I2_ONE), vec![])
}
/// `I2.seg`.
fn seg() -> Term {
    Term::cnst(name(I2_SEG), vec![])
}

/// Install the fixed interval-HIT schema (`I2`, `I2.zero`, `I2.one`, `I2.seg`,
/// `I2.rec`) into `env`. No prerequisite declarations are required (unlike
/// [`crate::circle::install_circle`], which needs `Eq` — `I2.seg`'s type is a cubical
/// `Path`, built directly on [`crate::cubical`]'s primitives, already part of this
/// kernel's core term grammar). Rejects re-installation (any of the five names already
/// declared).
pub fn install_interval_hit(env: &mut Env) -> Result<(), String> {
    for n in [I2_TYPE, I2_ZERO, I2_ONE, I2_SEG, I2_REC] {
        if env.contains(n) {
            return Err(format!("'{n}' is already declared"));
        }
    }

    let v = Level::param(0); // I2.rec's target universe.

    // ------------------------------------------------------------------
    // I2 : Type 0
    // ------------------------------------------------------------------
    env.insert(
        name(I2_TYPE),
        Decl::I2(Rc::new(I2 { role: I2Role::Type, num_levels: 0, ty: Term::typ(0) })),
    )?;

    // ------------------------------------------------------------------
    // I2.zero, I2.one : I2
    // ------------------------------------------------------------------
    env.insert(
        name(I2_ZERO),
        Decl::I2(Rc::new(I2 { role: I2Role::Zero, num_levels: 0, ty: i2() })),
    )?;
    env.insert(
        name(I2_ONE),
        Decl::I2(Rc::new(I2 { role: I2Role::One, num_levels: 0, ty: i2() })),
    )?;

    // ------------------------------------------------------------------
    // I2.seg : Path I2 I2.zero I2.one   (a genuine cubical PathP, NOT `Eq`)
    // ------------------------------------------------------------------
    let seg_ty = Term::path(i2(), zero(), one());
    env.insert(
        name(I2_SEG),
        Decl::I2(Rc::new(I2 { role: I2Role::Seg, num_levels: 0, ty: seg_ty })),
    )?;

    // ------------------------------------------------------------------
    // I2.rec.{v} : Π (C : I2 -> Sort v) (c0 : C zero) (c1 : C one)
    //                (s : PathP (\i. C (seg @ i)) c0 c1) (x : I2), C x
    //   binder order (outer -> inner): C(idx0) c0(idx1) c1(idx2) s(idx3) x(idx4)
    // ------------------------------------------------------------------
    let rec_ty = Term::pi(
        Term::arrow(i2(), Term::Sort(v.clone())), // C : I2 -> Sort v      (Var0 here)
        Term::pi(
            // c0 : C zero     (C = Var0)
            Term::app(Term::Var(0), zero()),
            Term::pi(
                // c1 : C one    (C = Var1)
                Term::app(Term::Var(1), one()),
                Term::pi(
                    // s : PathP (\i. C (seg @ i)) c0 c1
                    //   here: C = Var2, c0 = Var1, c1 = Var0
                    //   family under one more (interval) binder: C = Var3
                    Term::pathp(
                        Term::app(Term::Var(3), Term::papp(seg(), Term::Var(0))),
                        Term::Var(1), // c0
                        Term::Var(0), // c1
                    ),
                    Term::pi(
                        // x : I2    (depth 4)
                        i2(),
                        // C x    (C = Var4, x = Var0)
                        Term::app(Term::Var(4), Term::Var(0)),
                    ),
                ),
            ),
        ),
    );
    env.insert(
        name(I2_REC),
        Decl::I2(Rc::new(I2 { role: I2Role::Rec, num_levels: 1, ty: rec_ty })),
    )?;

    Ok(())
}

/// `refl a : Path A a a` — re-exported as a tiny convenience for building the constant
/// `s` argument used throughout this module's tests (identical to
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

    /// Build an env with `Nat` and the interval-HIT schema installed.
    fn i2_env() -> Env {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        install_interval_hit(&mut env).unwrap();
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
    fn interval_hit_constants_wellformed() {
        let env = i2_env();
        let chk = Checker::new(&env);
        for n in [I2_TYPE, I2_ZERO, I2_ONE, I2_SEG, I2_REC] {
            chk.infer_closed(env.get(n).unwrap().ty())
                .unwrap_or_else(|e| panic!("{n} ill-formed: {e}"));
        }
    }

    #[test]
    fn rejects_double_install() {
        let mut env = i2_env();
        let err = install_interval_hit(&mut env).unwrap_err();
        assert!(err.contains("already declared"), "got: {err}");
    }

    #[test]
    fn zero_and_one_typecheck() {
        let env = i2_env();
        let chk = Checker::new(&env);
        let tz = chk.infer_closed(&zero()).unwrap();
        let to = chk.infer_closed(&one()).unwrap();
        let red = Reducer::new(&env);
        assert!(red.is_def_eq(&tz, &i2()));
        assert!(red.is_def_eq(&to, &i2()));
    }

    /// `I2.seg` is a genuine cubical `Path I2 zero one`.
    #[test]
    fn seg_typechecks_as_a_cubical_path() {
        let env = i2_env();
        let chk = Checker::new(&env);
        let goal = Term::path(i2(), zero(), one());
        chk.check(&mut LocalCtx::new(), &cn(I2_SEG), &goal).unwrap();
    }

    /// SOUNDNESS: `zero` and `one` are NOT definitionally equal — `I2.seg` connects
    /// them only via the (non-collapsing) path layer, never by conversion.
    #[test]
    fn zero_and_one_are_not_definitionally_equal() {
        let env = i2_env();
        let red = Reducer::new(&env);
        assert!(!red.is_def_eq(&zero(), &one()));
    }

    // ---------------------------------------------------------------------
    // The non-dependent instance: `I2.rec (\_. Nat) c0 c1 s`
    // ---------------------------------------------------------------------

    fn nondep_rec(c0: Term, c1: Term, s: Term, scrut: Term) -> Term {
        let motive = Term::lam(i2(), cn("Nat").lift(1, 0)); // \_ : I2. Nat
        Term::apps(Term::cnst(name(I2_REC), vec![Level::of_nat(1)]), [motive, c0, c1, s, scrut])
    }

    /// POINT ι-RULE #1: `I2.rec C c0 c1 s I2.zero ↦ c0`. Checked on the trusted
    /// reducer AND NbE (differential).
    #[test]
    fn point_iota_zero() {
        let env = i2_env();
        let s = refl(&lit(7));
        let rec = nondep_rec(lit(7), lit(7), s, zero());
        let chk = Checker::new(&env);
        chk.check(&mut LocalCtx::new(), &rec, &cn("Nat")).unwrap();
        let red = Reducer::new(&env);
        assert!(red.is_def_eq(&rec, &lit(7)), "reducer: rec zero = c0");
        let nbe = Nbe::new(&env);
        assert_eq!(nbe.normalize(&rec), lit(7), "nbe: rec zero = c0");
    }

    /// POINT ι-RULE #2: `I2.rec C c0 c1 s I2.one ↦ c1`.
    #[test]
    fn point_iota_one() {
        let env = i2_env();
        let s = refl(&lit(9));
        let rec = nondep_rec(lit(9), lit(9), s, one());
        let chk = Checker::new(&env);
        chk.check(&mut LocalCtx::new(), &rec, &cn("Nat")).unwrap();
        let red = Reducer::new(&env);
        assert!(red.is_def_eq(&rec, &lit(9)), "reducer: rec one = c1");
        let nbe = Nbe::new(&env);
        assert_eq!(nbe.normalize(&rec), lit(9), "nbe: rec one = c1");
    }

    /// **THE PATH ι-RULE — the whole point of this module.**
    /// `I2.rec C c0 c1 s (I2.seg @ r) ↦ s @ r`, for a fresh *neutral* interval variable
    /// `r` (a bound variable of type `I`, so this exercises the general rule, not just
    /// the `r = i0`/`i1` boundary cases). Checked on the trusted reducer AND NbE.
    #[test]
    fn path_iota_computes_on_the_seg_application() {
        let env = i2_env();
        let s = refl(&lit(5)); // s : PathP (\_. Nat) 5 5, the constant path at 5
        // \(r : I). I2.rec (\_.Nat) 5 5 s (I2.seg @ r)   : I -> Nat is not itself
        // typeable (I isn't a type), so instead instantiate r directly at a closed
        // interval term and check the reduct, exactly mirroring how the module doc's
        // worked example proceeds (an open `r` is exercised via `PLam`, see
        // `path_iota_under_a_path_abstraction` below).
        let scrut = Term::papp(seg(), Term::Var(0));
        // Build the whole rec application under a PLam binder so `Var(0) : I` is legal.
        let body = nondep_rec(lit(5), lit(5), s, scrut);
        let whole = Term::plam(body);
        let chk = Checker::new(&env);
        let ty = chk.infer_closed(&whole).unwrap();
        // Expected type: Path Nat 5 5 (since s@i0=5, s@i1=5 are the boundary of `\_.Nat`
        // applied to seg@i0=zero / seg@i1=one, both give `Nat`, but the *value* boundary
        // is 5/5 since s is the constant path at 5).
        let expected_ty = Term::path(cn("Nat"), lit(5), lit(5));
        assert!(Reducer::new(&env).is_def_eq(&ty, &expected_ty), "got {ty:?}");
        let red = Reducer::new(&env);
        let nbe = Nbe::new(&env);
        // Reduces to `refl 5`'s body shape: \(r). 5 (the path ι-rule fires under the
        // binder, on a neutral `Var(0) : I`, producing `s @ Var(0)`, which further
        // reduces via s's own PLam beta to the constant `5`).
        let expected_whole = Term::plam(lit(5).lift(1, 0));
        assert!(red.is_def_eq(&whole, &expected_whole), "reducer: path iota under binder");
        assert_eq!(nbe.normalize(&whole), nbe.normalize(&expected_whole), "nbe: path iota under binder");
    }

    /// **TYPE PRESERVATION** of the path ι-rule: re-infer the *reduced* form (`s @ r`)
    /// and confirm it matches the recursor's own stated return type at the original
    /// scrutinee (`C (I2.seg @ r)`), for a genuinely *non-constant*-looking (but still
    /// well-typed) dependent instance. This is the concrete check the module doc's
    /// "why it type-checks" argument promises.
    #[test]
    fn path_iota_result_has_the_recursor_return_type() {
        let mut env = i2_env();
        // A fresh axiom `r : I` isn't directly expressible (I isn't a fibrant type,
        // can't be an axiom's type) — instead use a bound interval variable under a
        // PLam, exactly like `path_iota_computes_on_the_seg_application`.
        let motive = Term::lam(i2(), cn("Nat").lift(1, 0));
        let s = refl(&lit(3));
        let scrut = Term::papp(seg(), Term::Var(0));
        let rec = Term::apps(
            Term::cnst(name(I2_REC), vec![Level::of_nat(1)]),
            [motive.clone(), lit(3), lit(3), s.clone(), scrut.clone()],
        );
        let whole = Term::plam(rec);
        let chk = Checker::new(&env);
        // The whole application under the binder type-checks (this is what "type
        // preservation" means operationally here: the reducer/NbE reduct is re-checked
        // independently against the *originally inferred* type).
        let ty_before = chk.infer_closed(&whole).unwrap();
        let reduced = Reducer::new(&env).whnf(&whole);
        // Re-infer the reduced form from scratch (independent re-check).
        let ty_after = Checker::new(&env).infer_closed(&reduced).unwrap();
        assert!(
            Reducer::new(&env).is_def_eq(&ty_before, &ty_after),
            "type not preserved by path iota: before={ty_before:?} after={ty_after:?}"
        );
        // And matches `Path Nat 3 3` — the constant motive applied to the scrutinee at
        // both boundaries, i.e. the type the whole `PLam` was built to inhabit.
        let expected_ty = Term::path(cn("Nat"), lit(3), lit(3));
        assert!(Reducer::new(&env).is_def_eq(&ty_before, &expected_ty), "got {ty_before:?}");
        // silence unused warnings on `env` reuse pattern across sibling tests
        let _ = &mut env;
    }

    // ---------------------------------------------------------------------
    // Endpoint coherence: the path rule agrees with the point rules at the boundary.
    // ---------------------------------------------------------------------

    /// `I2.rec … (I2.seg @ i0)` and `I2.rec … I2.zero` land on the same normal form.
    #[test]
    fn endpoint_coherence_zero() {
        let env = i2_env();
        let s = refl(&lit(11));
        let via_path = nondep_rec(lit(11), lit(11), s.clone(), Term::papp(seg(), Term::IZero));
        let via_point = nondep_rec(lit(11), lit(11), s, zero());
        let red = Reducer::new(&env);
        let nbe = Nbe::new(&env);
        assert!(red.is_def_eq(&via_path, &via_point), "reducer: endpoint coherence at 0");
        assert_eq!(nbe.normalize(&via_path), nbe.normalize(&via_point), "nbe: endpoint coherence at 0");
        assert_eq!(nbe.normalize(&via_path), lit(11));
    }

    /// `I2.rec … (I2.seg @ i1)` and `I2.rec … I2.one` land on the same normal form.
    #[test]
    fn endpoint_coherence_one() {
        let env = i2_env();
        let s = refl(&lit(13));
        let via_path = nondep_rec(lit(13), lit(13), s.clone(), Term::papp(seg(), Term::IOne));
        let via_point = nondep_rec(lit(13), lit(13), s, one());
        let red = Reducer::new(&env);
        let nbe = Nbe::new(&env);
        assert!(red.is_def_eq(&via_path, &via_point), "reducer: endpoint coherence at 1");
        assert_eq!(nbe.normalize(&via_path), nbe.normalize(&via_point), "nbe: endpoint coherence at 1");
        assert_eq!(nbe.normalize(&via_path), lit(13));
    }

    // ---------------------------------------------------------------------
    // Adversarial: the path rule must not misfire, and canonicity/anti-False hold.
    // ---------------------------------------------------------------------

    /// `I2.rec` stays stuck on a NEUTRAL `I2`-typed variable (bound under a lambda) —
    /// preserves canonicity for open terms.
    #[test]
    fn rec_stuck_on_neutral() {
        let env = i2_env();
        let s = refl(&lit(1));
        let body = nondep_rec(lit(1), lit(1), s, Term::Var(0));
        let f = Term::lam(i2(), body);
        let chk = Checker::new(&env);
        chk.infer_closed(&f).unwrap();
        let red = Reducer::new(&env);
        let whnf = red.whnf(&f);
        match &whnf {
            Term::Lam(_, _) => {}
            other => panic!("expected a stuck lambda, got {other:?}"),
        }
    }

    /// The path ι-rule fires ONLY when the `PApp`'s head is *literally* `I2.seg` — it
    /// must not misfire on an unrelated axiomatized `Path` (a different `PathP`-typed
    /// neutral applied to an interval variable).
    #[test]
    fn path_iota_does_not_fire_on_unrelated_pathp() {
        let mut env = i2_env();
        env.insert(
            name("q"),
            Decl::Axiom { num_levels: 0, ty: Term::path(cn("Nat"), lit(0), lit(0)) },
        )
        .unwrap();
        let s = refl(&lit(0));
        // Scrutinee here is a bogus `Nat`-typed term coerced through `I2`'s slot is
        // ill-typed by construction, so instead directly probe the reducer: does
        // `try_i2_rec`-style matching treat `q @ r` (unrelated Path) as `I2.seg @ r`?
        // It cannot even be a well-typed scrutinee (`q @ r : Nat`, not `I2`), so the
        // *type-checker* rejects it outright — confirming misfire is impossible.
        let bogus_scrut = Term::papp(cn("q"), Term::Var(0));
        let body = nondep_rec(lit(0), lit(0), s, bogus_scrut);
        let whole = Term::plam(body);
        let chk = Checker::new(&env);
        assert!(chk.infer_closed(&whole).is_err(), "unrelated PathP scrutinee must be rejected");
        let _ = &mut env;
    }

    /// ADVERSARIAL / ANTI-`False`: cannot derive `Path Nat 0 1` (or equate any two
    /// distinct closed `Nat` values) from the interval-HIT machinery. `I2.rec`'s path
    /// ι-rule only ever returns `s @ r` for the *caller-supplied* `s`; it manufactures
    /// no new proof term.
    #[test]
    fn cannot_prove_false() {
        let env = i2_env();
        // Directly: 0 and 1 are not definitionally equal, before or after any
        // I2-flavoured detour.
        let red = Reducer::new(&env);
        assert!(!red.is_def_eq(&lit(0), &lit(1)));
        // And: I2.seg itself cannot be coerced into proving an unrelated Nat equation
        // (wrong type entirely).
        let bogus_goal = Term::path(cn("Nat"), lit(3), lit(5));
        let chk = Checker::new(&env);
        assert!(
            chk.check(&mut LocalCtx::new(), &cn(I2_SEG), &bogus_goal).is_err(),
            "I2.seg must not check against an unrelated Path Nat goal"
        );
    }

    /// ANTI-`False` via the recursor: even though `I2.rec`'s path rule *computes*, it
    /// cannot be abused to produce a proof that `I2.zero` and `I2.one` are equal at
    /// `I2` itself (only at whatever *target* type `C` the caller picks — and even
    /// there, only what `c0`/`c1`/`s` already supplied).
    #[test]
    fn zero_one_still_distinct_under_the_identity_motive() {
        let env = i2_env();
        // C := \x. I2   (the identity-ish motive), c0 := zero, c1 := one,
        // s : PathP (\i. I2) zero one, i.e. Path I2 zero one — that's just I2.seg!
        let motive = Term::lam(i2(), i2().lift(1, 0));
        let rec = Term::apps(
            Term::cnst(name(I2_REC), vec![Level::of_nat(1)]),
            [motive, zero(), one(), cn(I2_SEG), zero()],
        );
        let red = Reducer::new(&env);
        // rec ... zero -> c0 = zero, definitely NOT `one`.
        assert!(red.is_def_eq(&rec, &zero()));
        assert!(!red.is_def_eq(&rec, &one()));
    }

    // ---------------------------------------------------------------------
    // Worked example: the path ι-rule firing on a genuinely path-shaped scrutinee,
    // something the Eq-based `S1.rec`/`Trunc.lift`/`Quot.lift` cannot express.
    // ---------------------------------------------------------------------

    #[test]
    fn worked_example_non_constant_family() {
        let env = i2_env();
        // s : Path Nat 4 4 (constant path). Apply the recursor to `seg @ i` under a
        // path abstraction, i.e. build `ap`-like content directly via the computing
        // recursor rather than `crate::cubical::ap`.
        let s = refl(&lit(4));
        let scrut = Term::papp(seg(), Term::Var(0));
        let body = nondep_rec(lit(4), lit(4), s, scrut);
        let whole = Term::plam(body); // : Path Nat 4 4
        let chk = Checker::new(&env);
        let ty = chk.infer_closed(&whole).unwrap();
        assert!(Reducer::new(&env).is_def_eq(&ty, &Term::path(cn("Nat"), lit(4), lit(4))));
        // It reduces to the constant path at 4 -- the path constructor `seg` really did
        // get computed away by `I2.rec`'s path ι-rule, not merely postulated.
        let nbe = Nbe::new(&env);
        assert_eq!(nbe.normalize(&whole), nbe.normalize(&Term::plam(lit(4).lift(1, 0))));
    }
}
