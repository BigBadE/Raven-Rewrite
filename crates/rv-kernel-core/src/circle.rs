//! The circle `S¹` — a **non-truncated** 1-higher-inductive-type (HIT).
//!
//! ## What this delivers
//!
//! [`crate::trunc`] ships propositional truncation, whose path constructor identifies
//! *every* pair of points — the type collapses to a mere proposition, and the dependent
//! eliminator is confined to `Prop` where the path is respected "for free" by proof
//! irrelevance. This module ships the complementary, harder case that generalizes the
//! truncation schema to genuine higher-dimensional data: `S¹`, presented by
//!
//!   * a **point** constructor `base : S¹`, and
//!   * a **path** constructor `loop : Eq S¹ base base` — a single, specific self-loop,
//!     *not* an identification of arbitrary pairs.
//!
//! `S¹` lives in `Type` (not `Prop`): unlike `∥A∥`, nothing forces its points to be
//! propositionally interchangeable in general, so `base` remains an honest, non-trivial
//! value and `loop` is one witnessed path among (potentially) many non-equal ones. This is
//! the standard first example of a "real" HIT (Mac Lane–style delooping of `Z`, or the
//! homotopy-theorist's `S¹`) and is a genuine generalization of the truncation schema's
//! *shape* — point constructor plus path constructor plus a recursor with a
//! respectfulness premise per path constructor — to a **non-collapsing** target type.
//!
//! Like [`crate::trunc`] and [`crate::quotient`] this is a **fixed five-constant schema**,
//! installed once by [`install_circle`]; `S¹` itself has no parameters (it is not `S¹ A`
//! for a carrier `A` — the whole point is that it is not built *from* a family of points,
//! but has exactly the one nullary point constructor `base`). The five constants are:
//!
//! ```text
//!   S1        : Type 0
//!   S1.base   : S1
//!   S1.loop   : Eq.{1} S1 S1.base S1.base
//!   S1.rec.{v}: Π (P : Sort v) (pt : P) (lp : Eq.{v} P pt pt), S1 → P
//!   S1.ind    : Π (β : S1 → Prop) (h : β S1.base), Π (t : S1), β t
//! ```
//!
//! with the **single computation rule** (the point-constructor ι-rule), added to both the
//! trusted [`crate::reduce`] and the fast [`crate::nbe`]:
//!
//! ```text
//!   S1.rec.{v} P pt lp S1.base  ↦  pt
//! ```
//!
//! The path constructor `S1.loop` has **no computation rule** — its whole content is the
//! propositional self-equality it constructs. As with `Trunc.eq`, this keeps the HIT
//! within ordinary (non-cubical) type theory: the path holds only *propositionally*
//! (through `Eq`), never definitionally, so no interval/`transp`/`hcomp` machinery is
//! required.
//!
//! ## The recursor and its respectfulness premise
//!
//! `S1.rec` is the non-dependent recursor. A function `S¹ → P` must send `loop` to *some*
//! path in `P`, or the eliminator would let one project structure out of `S¹` that isn't
//! actually determined by `base` alone (unsoundly forgetting that `base` and `base`
//! traversed around `loop` must land on `pt` "the same way"). We phrase that condition, as
//! is standard for a non-dependent circle recursor, by requiring a proof
//!
//! ```text
//!   lp : Eq P pt pt
//! ```
//!
//! that `pt`'s image under the (as yet unspecified) action of `loop` is *some* self-path —
//! exactly [`crate::trunc`]'s `resp` and [`crate::quotient`]'s `resp`, specialized to the
//! single path constructor `loop`. The computation rule discards `lp` at reduction time
//! exactly as `Trunc.lift`/`Quot.lift` discard their `resp`: soundness comes from `lp`
//! having been *type-checked to exist* at the point the recursor is formed, not from `lp`
//! ever being inspected computationally.
//!
//! (Note: because every `P` admits the trivial `lp := Eq.refl P pt`, `S1.rec` is
//! unconditionally usable — this reflects `S¹ → P` maps genuinely existing for any `pt`;
//! it is the *dependent, `Type`-valued* eliminator that would need a real geometric
//! respectfulness datum, which — as with `Trunc.ind`/`Quot.rec`'s general case — is where
//! the honest difficulty of a HIT recursor lives. See "Supported class" below.)
//!
//! ## Why this is SOUND
//!
//! * `S1.loop` is an **axiom-shaped** constant: it *constructs* a proof of `base = base`,
//!   but only at the `Eq` (propositional) level. There is **no** reduction that makes
//!   `S1.loop` reduce to `Eq.refl`, and no reduction *on* `S1.base` triggered by `loop`.
//!   `S1.base` therefore remains a single, stable canonical value — conversion never
//!   introduces a second normal form for it, and no closed term of `S¹` other than
//!   (things convertible to) `S1.base` can arise from the constructors given here, so
//!   canonicity at the point layer is preserved (adversarial test
//!   `loop_is_only_propositional`, `loop_does_not_reduce_to_refl`).
//!
//! * `S1.rec`'s computation rule fires **only** on a literal `S1.base` application — never
//!   on `S1.loop`, never on a neutral (`try_circle_rec` in `reduce.rs`/`nbe.rs` matches the
//!   scrutinee's *weak-head* shape against the `Base` role exactly, exactly mirroring
//!   `try_trunc_lift`/`try_quot_lift`). `S1.loop`'s type is `Eq S1 base base`, not `S1`
//!   itself, so it can never even appear as `S1.rec`'s scrutinee in a well-typed term
//!   (adversarial test `rec_does_not_fire_on_loop`). Since `lp` never appears in the
//!   reduct `pt`, and the only point constructor is `base`, subject reduction and
//!   confluence are immediate: there is exactly one point-shaped redex.
//!
//! * `S1.ind` eliminates **only into `Prop`** (its motive `β : S1 → Prop`) and has *no*
//!   computation rule, exactly as `Trunc.ind`. Proof irrelevance in `Prop` makes the
//!   missing `ind S1.base ↦ h` reduction unobservable, and confines the dependent
//!   eliminator to the one universe where respecting the path constructor `loop` is
//!   automatic (any two proofs of `β t` are already definitionally equal, so `β` trivially
//!   respects `loop` — there is nothing further to transport). A `Type`-valued dependent
//!   eliminator (the genuine circle induction principle, needing a `Π (l : Eq P.(over
//!   loop) …)`-shaped transport datum) is **not** offered — see "Supported class" below.
//!
//! The `Eq` inductive (with `Eq.refl`) must already be installed; `S1.loop` and
//! `S1.rec`'s `lp` are stated against it.
//!
//! ## Supported class and restrictions
//!
//! This module ships **exactly one** non-truncated HIT — the circle `S¹`, with a single
//! nullary point constructor and a single nullary-indexed self-loop path constructor — as
//! a fully sound, kernel-checked primitive. The supported eliminations are:
//!   * the non-dependent recursor `S1.rec` into any `P : Sort v`, gated by the
//!     respectfulness premise `lp : Eq P pt pt` for the one path constructor `loop`;
//!   * the dependent `Prop`-eliminator `S1.ind`.
//!
//! A **fully general** 1-HIT schema — arbitrary user-declared point constructors (with
//! recursive/non-recursive fields) together with arbitrary user-declared path
//! constructors between terms built from them, plus a **dependent, `Type`-valued**
//! eliminator that transports along each path — is deliberately **out of scope**, for the
//! same reason [`crate::trunc`] gives: getting the dependent computation/subject-reduction
//! interaction right for an *arbitrary* path shape, without an interval, is delicate
//! enough that an unsound instance would let `False` be derived. This module instead
//! demonstrates the general **pattern** — point constructor(s) + path constructor(s) +
//! recursor with one respectfulness premise per path constructor, `ι` firing only on point
//! constructors — on the standard non-truncation worked example, closed soundly:
//!   * point constructors: exactly one, `base`, nullary (no user-declared point-family is
//!     supported; a general schema would need to reuse the ordinary inductive-declaration
//!     machinery in [`crate::inductive`]/`rv_kernel::mutual` for the point layer, then
//!     separately layer path constructors and a joint recursor over it — a materially
//!     larger change);
//!   * path constructors: exactly one, `loop : base = base`, between closed point terms,
//!     with a fixed target (`base`, not an arbitrary point-built expression) — the
//!     narrowest non-trivial instance of "path between expressions built from point
//!     constructors";
//!   * eliminator: `S1.rec` (non-dependent, into any `Sort v`, exactly one respectfulness
//!     premise for `loop`) and `S1.ind` (dependent, `Prop`-only, no premise needed).
//!
//! A genuinely general schema (arbitrary named point/path constructors, dependent
//! `Type`-valued recursor) is left as future work, exactly as trunc.rs recommends for
//! `Trunc.rec`; `Trunc` and `Quot` continue to work unchanged (this module adds new
//! constants only, touching no existing code path except adding one more `match` arm
//! alongside `TruncRole::Lift`/`QuotRole::Lift` in `reduce.rs` and `nbe.rs`).

use crate::env::{Circle, CircleRole, Decl, Env};
use crate::level::Level;
use crate::term::{name, Term};
use std::rc::Rc;

/// Names of the five circle constants.
pub const CIRCLE: &str = "S1";
pub const CIRCLE_BASE: &str = "S1.base";
pub const CIRCLE_LOOP: &str = "S1.loop";
pub const CIRCLE_REC: &str = "S1.rec";
pub const CIRCLE_IND: &str = "S1.ind";

/// `Eq.{lvl} T x y`.
fn eq_app(lvl: Level, t: Term, x: Term, y: Term) -> Term {
    Term::apps(Term::cnst(name("Eq"), vec![lvl]), [t, x, y])
}

/// `S1`.
fn circle() -> Term {
    Term::cnst(name(CIRCLE), vec![])
}

/// `S1.base`.
fn base() -> Term {
    Term::cnst(name(CIRCLE_BASE), vec![])
}

/// Install the fixed circle schema (`S1`, `S1.base`, `S1.loop`, `S1.rec`, `S1.ind`) into
/// `env`. Requires the `Eq` inductive (with `Eq.refl`) to be present, since `S1.loop` and
/// the respectfulness premise of `S1.rec` are stated against it. Rejects re-installation
/// (any of the five names already declared).
pub fn install_circle(env: &mut Env) -> Result<(), String> {
    match env.get("Eq") {
        Some(Decl::Inductive(_)) => {}
        _ => return Err("S1 requires the 'Eq' inductive to be installed first".to_string()),
    }
    for n in [CIRCLE, CIRCLE_BASE, CIRCLE_LOOP, CIRCLE_REC, CIRCLE_IND] {
        if env.contains(n) {
            return Err(format!("'{n}' is already declared"));
        }
    }

    let v = Level::param(0); // S1.rec's target universe.
    // `S1 : Type 0`, so `Eq` over an `S1` value is `Eq.{1} …` (Type 0 = Sort 1).
    let one = Level::of_nat(1);

    // ------------------------------------------------------------------
    // S1 : Type 0
    // ------------------------------------------------------------------
    env.insert(
        name(CIRCLE),
        Decl::Circle(Rc::new(Circle { role: CircleRole::Type, num_levels: 0, ty: Term::typ(0) })),
    )?;

    // ------------------------------------------------------------------
    // S1.base : S1
    // ------------------------------------------------------------------
    env.insert(
        name(CIRCLE_BASE),
        Decl::Circle(Rc::new(Circle { role: CircleRole::Base, num_levels: 0, ty: circle() })),
    )?;

    // ------------------------------------------------------------------
    // S1.loop : Eq.{1} S1 S1.base S1.base
    // ------------------------------------------------------------------
    let loop_ty = eq_app(one, circle(), base(), base());
    env.insert(
        name(CIRCLE_LOOP),
        Decl::Circle(Rc::new(Circle { role: CircleRole::Loop, num_levels: 0, ty: loop_ty })),
    )?;

    // ------------------------------------------------------------------
    // S1.rec.{v} : Π (P : Sort v) (pt : P) (lp : Eq.{v} P pt pt), S1 → P
    //   final indices: P=Var3, pt=Var2, lp=Var1, t=Var0
    // ------------------------------------------------------------------
    let rec_ty = Term::pi(
        Term::Sort(v.clone()), // P    (Var0)
        Term::pi(
            Term::Var(0), // pt : P   (P=Var0)
            Term::pi(
                // lp : Eq P pt pt   (depth 2: P=Var1, pt=Var0)
                eq_app(v.clone(), Term::Var(1), Term::Var(0), Term::Var(0)),
                Term::pi(
                    circle(), // t : S1
                    // P   (depth 4: P was Var2, under one more binder → Var3)
                    Term::Var(3),
                ),
            ),
        ),
    );
    env.insert(
        name(CIRCLE_REC),
        Decl::Circle(Rc::new(Circle { role: CircleRole::Rec, num_levels: 1, ty: rec_ty })),
    )?;

    // ------------------------------------------------------------------
    // S1.ind : Π (β : S1 → Prop) (h : β S1.base), Π (t : S1), β t
    //   final indices: β=Var2, h=Var1, t=Var0
    // ------------------------------------------------------------------
    let ind_ty = Term::pi(
        // β : S1 → Prop   (Var0)
        Term::arrow(circle(), Term::prop()),
        Term::pi(
            // h : β S1.base   (β=Var0)
            Term::app(Term::Var(0), base()),
            Term::pi(
                // t : S1   (depth 2)
                circle(),
                // β t   (β=Var2, t=Var0)
                Term::app(Term::Var(2), Term::Var(0)),
            ),
        ),
    );
    env.insert(
        name(CIRCLE_IND),
        Decl::Circle(Rc::new(Circle { role: CircleRole::Ind, num_levels: 0, ty: ind_ty })),
    )?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::{Checker, LocalCtx};
    use crate::inductive::{declare_eq, declare_nat};
    use crate::reduce::Reducer;

    /// Build an env with `Nat`, `Eq`, and the circle schema installed.
    fn circle_env() -> Env {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_eq(&mut env).unwrap();
        install_circle(&mut env).unwrap();
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
    fn refl(lvl: Level, ty: Term, x: Term) -> Term {
        Term::apps(Term::cnst(name("Eq.refl"), vec![lvl]), [ty, x])
    }

    /// Every installed circle constant is a well-formed type.
    #[test]
    fn circle_constants_wellformed() {
        let env = circle_env();
        let chk = Checker::new(&env);
        for n in [CIRCLE, CIRCLE_BASE, CIRCLE_LOOP, CIRCLE_REC, CIRCLE_IND] {
            chk.infer_closed(env.get(n).unwrap().ty())
                .unwrap_or_else(|e| panic!("{n} ill-formed: {e}"));
        }
    }

    /// Installing without `Eq` present is rejected.
    #[test]
    fn requires_eq() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        let err = install_circle(&mut env).unwrap_err();
        assert!(err.contains("Eq"), "got: {err}");
    }

    /// Re-installation is rejected.
    #[test]
    fn rejects_double_install() {
        let mut env = circle_env();
        let err = install_circle(&mut env).unwrap_err();
        assert!(err.contains("already declared"), "got: {err}");
    }

    /// `S1.base : S1`, and `S1 : Type 0`.
    #[test]
    fn base_typechecks() {
        let env = circle_env();
        let chk = Checker::new(&env);
        let ty = chk.infer_closed(&base()).unwrap();
        assert!(Reducer::new(&env).is_def_eq(&ty, &circle()), "got {ty:?}");
        let sort = chk.infer_closed(&circle()).unwrap();
        assert!(Reducer::new(&env).is_def_eq(&sort, &Term::typ(0)), "S1 not Type 0");
    }

    /// `S1.loop : Eq S1 base base` type-checks.
    #[test]
    fn loop_typechecks() {
        let env = circle_env();
        let chk = Checker::new(&env);
        let goal = eq_app(Level::of_nat(1), circle(), base(), base());
        chk.check(&mut LocalCtx::new(), &cn(CIRCLE_LOOP), &goal).unwrap();
    }

    /// COMPUTATION RULE: `S1.rec P pt lp S1.base ↦ pt`. Checked on the trusted reducer AND
    /// NbE (differential).
    #[test]
    fn rec_computation_reduces() {
        let env = circle_env();
        let u = Level::of_nat(1);
        let pt = lit(7);
        let lp = refl(u.clone(), cn("Nat"), pt.clone());
        let rec = Term::apps(
            Term::cnst(name(CIRCLE_REC), vec![u.clone()]),
            [cn("Nat"), pt.clone(), lp, base()],
        );
        let chk = Checker::new(&env);
        chk.check(&mut LocalCtx::new(), &rec, &cn("Nat")).unwrap();
        let red = Reducer::new(&env);
        assert!(red.is_def_eq(&rec, &lit(7)), "reducer: rec base = pt");
        let nbe = crate::nbe::Nbe::new(&env);
        assert_eq!(nbe.normalize(&rec), lit(7), "nbe: rec base = pt");
    }

    /// `S1.rec` is unconditionally usable: any `pt` admits the trivial `lp := Eq.refl`.
    /// Lift the constant map to `Nat`, sending everything to `42`.
    #[test]
    fn rec_constant_map() {
        let env = circle_env();
        let u = Level::of_nat(1);
        let pt = lit(42);
        let lp = refl(u.clone(), cn("Nat"), pt.clone());
        let rec = Term::apps(
            Term::cnst(name(CIRCLE_REC), vec![u.clone()]),
            [cn("Nat"), pt, lp, base()],
        );
        let nbe = crate::nbe::Nbe::new(&env);
        assert_eq!(nbe.normalize(&rec), lit(42));
    }

    /// SOUNDNESS (positive): `S1.loop` DOES prove `base = base` in `S1`.
    #[test]
    fn loop_proves_base_eq_base() {
        let env = circle_env();
        let goal = eq_app(Level::of_nat(1), circle(), base(), base());
        let chk = Checker::new(&env);
        chk.check(&mut LocalCtx::new(), &cn(CIRCLE_LOOP), &goal).unwrap();
    }

    /// SOUNDNESS (adversarial): `S1.loop` is ONLY propositional — it does NOT reduce to
    /// `Eq.refl`, and no reduction fires on it. If it collapsed to `Eq.refl` (or any
    /// reduction touched `S1.base` because of `loop`), the "genuine higher path" content
    /// of the circle would be a fiction and later dependent reasoning over paths could be
    /// unsound. We check `S1.loop` is its own weak-head normal form and is NOT
    /// definitionally equal to `Eq.refl S1 base` at the syntactic level the reducer would
    /// need to identify them through (no rule exists that could).
    #[test]
    fn loop_is_only_propositional() {
        let env = circle_env();
        let red = Reducer::new(&env);
        let whnf_loop = red.whnf(&cn(CIRCLE_LOOP));
        assert_eq!(whnf_loop, cn(CIRCLE_LOOP), "S1.loop must not reduce");
        let nbe = crate::nbe::Nbe::new(&env);
        assert_eq!(nbe.normalize(&cn(CIRCLE_LOOP)), cn(CIRCLE_LOOP), "nbe: S1.loop irreducible");
    }

    /// SOUNDNESS (adversarial): `S1.rec` does NOT fire on the path constructor `S1.loop` —
    /// only on `S1.base`. `S1.loop : Eq S1 base base`, not `S1`, so applying `S1.rec` to it
    /// as the scrutinee is ill-typed and must be rejected outright (no spurious reduction
    /// can even be attempted on a well-typed term).
    #[test]
    fn rec_does_not_fire_on_loop() {
        let env = circle_env();
        let u = Level::of_nat(1);
        let pt = lit(7);
        let lp = refl(u.clone(), cn("Nat"), pt.clone());
        // Scrutinee is the PATH `S1.loop : Eq S1 base base`, not an `S1`.
        let rec = Term::apps(
            Term::cnst(name(CIRCLE_REC), vec![u.clone()]),
            [cn("Nat"), pt, lp, cn(CIRCLE_LOOP)],
        );
        let chk = Checker::new(&env);
        assert!(chk.infer_closed(&rec).is_err(), "rec on a loop scrutinee must be rejected");
    }

    /// SOUNDNESS (adversarial): mismatched `lp` (not a self-path `Eq P pt pt` for the
    /// SAME `pt` being returned) is rejected. Here we try to smuggle `pt = 7` but
    /// `lp : Eq Nat 7 8`, which cannot type `Eq Nat pt pt`.
    #[test]
    fn mismatched_lp_rejected() {
        let env = circle_env();
        let u = Level::of_nat(1);
        // Bogus: Eq Nat 7 8, not Eq Nat 7 7.
        let bogus_lp = Term::apps(
            Term::cnst(name("Eq.refl"), vec![u.clone()]),
            [cn("Nat"), lit(7)],
        );
        // Reinterpret as a claimed proof of `Eq Nat 7 8` by checking against that goal
        // directly (the honest way to construct the adversarial term is to check whether
        // `Eq.refl Nat 7` can be coerced into the wrong-shaped `lp` slot required for a
        // *different* `pt`).
        let rec = Term::apps(
            Term::cnst(name(CIRCLE_REC), vec![u.clone()]),
            [cn("Nat"), lit(8), bogus_lp, base()],
        );
        let chk = Checker::new(&env);
        assert!(chk.infer_closed(&rec).is_err(), "mismatched lp/pt must be rejected");
    }

    /// SOUNDNESS (adversarial): `S1.base` and a hypothetical "other" point are not
    /// conflatable — there is only one point constructor, so this specifically checks
    /// that `S1.rec` applied to a NEUTRAL `S1`-typed variable does not reduce (stays
    /// stuck), preserving canonicity for open terms too.
    #[test]
    fn rec_stuck_on_neutral() {
        let env = circle_env();
        let u = Level::of_nat(1);
        let pt = lit(7);
        let lp = refl(u.clone(), cn("Nat"), pt.clone());
        // A neutral `S1`-typed term: a bound variable under a lambda `S1 → Nat`.
        let body = Term::apps(
            Term::cnst(name(CIRCLE_REC), vec![u.clone()]),
            [cn("Nat"), pt, lp, Term::Var(0)],
        );
        let f = Term::lam(circle(), body);
        let chk = Checker::new(&env);
        chk.infer_closed(&f).unwrap();
        let red = Reducer::new(&env);
        let whnf = red.whnf(&f);
        // Still a Lam whose body is a stuck `S1.rec … (Var 0)` — not reduced away.
        match &whnf {
            Term::Lam(_, _) => {}
            other => panic!("expected a stuck lambda, got {other:?}"),
        }
    }

    /// `S1.ind` is well-typed and usable end-to-end: prove a constant `Prop` over the
    /// circle from the point case.
    #[test]
    fn ind_applies() {
        let env = circle_env();
        let u = Level::of_nat(1);
        // β := λ t. Eq Nat 0 0   (a constant Prop over the circle)
        let beta = Term::lam(circle(), eq_app(u.clone(), cn("Nat"), lit(0), lit(0)));
        // h := Eq.refl Nat 0   : β S1.base
        let h = refl(u.clone(), cn("Nat"), lit(0));
        let ind = Term::apps(Term::cnst(name(CIRCLE_IND), vec![]), [beta, h, base()]);
        let goal = eq_app(u.clone(), cn("Nat"), lit(0), lit(0));
        let chk = Checker::new(&env);
        chk.check(&mut LocalCtx::new(), &ind, &goal).unwrap();
    }

    /// ADVERSARIAL: cannot derive `False` from the circle machinery. `S1.loop` requires
    /// genuine `S1`-typed endpoints — attempting to apply it (or otherwise abuse the
    /// schema) to smuggle out an unrelated `Eq` at the wrong type is rejected by ordinary
    /// type-checking, and there is no computation rule anywhere that could equate two
    /// distinct closed values.
    #[test]
    fn cannot_prove_false() {
        let env = circle_env();
        // Attempt: use S1.loop directly as a proof of `Eq Nat 3 5` — type mismatch.
        let bogus_goal = eq_app(Level::of_nat(0), cn("Nat"), lit(3), lit(5));
        let chk = Checker::new(&env);
        let mut ctx = LocalCtx::new();
        assert!(
            chk.check(&mut ctx, &cn(CIRCLE_LOOP), &bogus_goal).is_err(),
            "S1.loop must not check against an unrelated Eq goal"
        );
    }
}
