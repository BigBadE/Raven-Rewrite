//! Quotient types — `A / R`, the Lean/Coq-style sound quotient primitive.
//!
//! ## What this delivers
//!
//! Given a type `A : Sort u` and a relation `R : A → A → Prop`, a **quotient type**
//! `Quot A R : Sort u` whose points are the points of `A` *identified* whenever `R`
//! relates them. Quotients let a proof phrase honest equalities that would otherwise
//! need setoid / pointwise bookkeeping (e.g. `separation.rv`'s heaps, integers as
//! `Nat × Nat`, `Int` mod `n`).
//!
//! This is the **fixed five-constant schema** of Lean's `Quot` (not a per-quotient
//! datatype declaration like [`crate::generate`] or [`crate::coinductive`]). It is
//! installed **once** into the environment by [`install_quot`]; every quotient the user
//! forms is `Quot A R` for their own `A`, `R`. The five constants are:
//!
//! ```text
//!   Quot.{u}       : Π (A : Sort u), (A → A → Prop) → Sort u
//!   Quot.mk.{u}    : Π (A : Sort u) (R : A → A → Prop), A → Quot.{u} A R
//!   Quot.sound.{u} : Π (A : Sort u) (R : A → A → Prop) (a b : A),
//!                        R a b → Eq.{u} (Quot.{u} A R) (Quot.mk.{u} A R a) (Quot.mk.{u} A R b)
//!   Quot.lift.{u v}: Π (A : Sort u) (R : A → A → Prop) (B : Sort v)
//!                        (f : A → B)
//!                        (resp : Π (a b : A), R a b → Eq.{v} B (f a) (f b)),
//!                        Quot.{u} A R → B
//!   Quot.ind.{u}   : Π (A : Sort u) (R : A → A → Prop)
//!                        (β : Quot.{u} A R → Prop)
//!                        (h : Π (a : A), β (Quot.mk.{u} A R a)),
//!                        Π (q : Quot.{u} A R), β q
//! ```
//!
//! with the **single computation rule** (ι/quotient-reduction), added to both the
//! trusted [`crate::reduce`] and the fast [`crate::nbe`]:
//!
//! ```text
//!   Quot.lift.{u v} A R B f resp (Quot.mk.{u} A R a)  ↦  f a
//! ```
//!
//! ## Why this is SOUND
//!
//! These are *exactly* the standard quotient rules; nothing more is added to
//! conversion.
//!
//! * `Quot.sound` is an **axiom-shaped** constant: it *constructs* a proof of
//!   `Quot.mk a = Quot.mk b`, but only when handed an `R a b` witness. There is no
//!   reduction that fabricates such an equality, and no definitional identification of
//!   `Quot.mk a` with `Quot.mk b` — the identification is purely *propositional*
//!   (through `Eq`), so it can never equate two *distinct closed values* and let the
//!   checker's conversion collapse. You **cannot** obtain `mk a = mk b` without first
//!   supplying `R a b` (adversarial test `cannot_prove_mk_eq_without_witness`).
//!
//! * `Quot.lift`'s computation rule fires **only** on a literal `Quot.mk` application.
//!   Type-checking a `Quot.lift … f resp …` *forces* `resp` to prove `f` respects `R`;
//!   an unrespectful `f` has no such `resp`, so the term does not type-check
//!   (adversarial test `unrespectful_lift_rejected`). The reduction itself discards
//!   `resp` (as Lean does): soundness comes from `resp` having been *checked to exist*
//!   at typing time, exactly like a recursor's minor premises. Because `resp` only ever
//!   proves an `Eq` and never participates in the reduct, and the reduct `f a` is
//!   independent of *which* representative was chosen up to the propositional equality
//!   `sound` gives, the rule is confluent with `sound` and does not break subject
//!   reduction.
//!
//! * `Quot.ind` eliminates **only into `Prop`** (its motive `β : Quot A R → Prop`). It
//!   has *no computation rule* — it is a `Prop`-level induction principle whose only
//!   role is to let you prove `∀ q, β q` from `∀ a, β (mk a)`. Since the target is a
//!   `Prop`, proof irrelevance means the missing `ind (mk a) ↦ h a` reduction is
//!   unobservable: any two proofs of `β q` are already definitionally equal. Restricting
//!   `ind` to `Prop` is what keeps it sound *without* a computation rule (a `Type`-valued
//!   dependent eliminator would need the `mk`-computation to preserve subject reduction,
//!   and getting that exactly right is delicate — so we conservatively do not offer it).
//!
//! The `Eq` inductive (with `Eq.refl`) must already be installed; `Quot.sound` and
//! `Quot.lift`/`resp` are stated against it.

use crate::env::{Decl, Env, QuotRole, Quotient};
use crate::level::Level;
use crate::term::{name, Grade, Term};
use std::rc::Rc;

/// Names of the five quotient constants.
pub const QUOT: &str = "Quot";
pub const QUOT_MK: &str = "Quot.mk";
pub const QUOT_SOUND: &str = "Quot.sound";
pub const QUOT_LIFT: &str = "Quot.lift";
pub const QUOT_IND: &str = "Quot.ind";

/// `A → A → Prop`, the type of a relation on `A` (here `A` is the given term). Both
/// arrows are non-dependent.
fn rel_ty(a: Term) -> Term {
    Term::arrow(a.clone(), Term::arrow(a, Term::prop()))
}

/// `Quot.{lvl} A R`.
fn quot_app(lvl: Level, a: Term, r: Term) -> Term {
    Term::apps(Term::cnst(name(QUOT), vec![lvl]), [a, r])
}

/// `Quot.mk.{lvl} A R x`.
fn mk_app(lvl: Level, a: Term, r: Term, x: Term) -> Term {
    Term::apps(Term::cnst(name(QUOT_MK), vec![lvl]), [a, r, x])
}

/// `Eq.{lvl} T x y`.
fn eq_app(lvl: Level, t: Term, x: Term, y: Term) -> Term {
    Term::apps(Term::cnst(name("Eq"), vec![lvl]), [t, x, y])
}

/// Install the fixed quotient schema (`Quot`, `Quot.mk`, `Quot.sound`, `Quot.lift`,
/// `Quot.ind`) into `env`. Requires the `Eq` inductive (with `Eq.refl`) to be present,
/// since `Quot.sound` and the respectfulness premise of `Quot.lift` are stated against
/// it. Rejects re-installation (any of the five names already declared).
pub fn install_quot(env: &mut Env) -> Result<(), String> {
    match env.get("Eq") {
        Some(Decl::Inductive(_)) => {}
        _ => return Err("Quot requires the 'Eq' inductive to be installed first".to_string()),
    }
    for n in [QUOT, QUOT_MK, QUOT_SOUND, QUOT_LIFT, QUOT_IND] {
        if env.contains(n) {
            return Err(format!("'{n}' is already declared"));
        }
    }

    let u = Level::param(0); // the carrier universe, shared by all but Quot.lift's v.
    let v = Level::param(1); // Quot.lift's result universe.

    // ------------------------------------------------------------------
    // Quot.{u} : Π (A : Sort u), (A → A → Prop) → Sort u
    // ------------------------------------------------------------------
    let quot_ty = Term::pi(
        Term::Sort(u.clone()), // A : Sort u              (Var 0 = A)
        Term::arrow(rel_ty(Term::Var(0)), Term::Sort(u.clone())), // (A→A→Prop) → Sort u
    );
    env.insert(
        name(QUOT),
        Decl::Quot(Rc::new(Quotient { role: QuotRole::Type, num_levels: 1, ty: quot_ty })),
    )?;

    // ------------------------------------------------------------------
    // Quot.mk.{u} : Π (A : Sort u) (R : A → A → Prop), A → Quot A R
    //   binders: A = Var2, R = Var1, x = Var0
    // ------------------------------------------------------------------
    let mk_ty = Term::pi(
        Term::Sort(u.clone()), // A       (Var0 here)
        Term::pi(
            rel_ty(Term::Var(0)), // R : A→A→Prop      (A=Var0)
            Term::pi(
                Term::Var(1),                                    // x : A         (A=Var1)
                quot_app(u.clone(), Term::Var(2), Term::Var(1)), // Quot A R  (A=Var2,R=Var1)
            ),
        ),
    );
    env.insert(
        name(QUOT_MK),
        Decl::Quot(Rc::new(Quotient { role: QuotRole::Mk, num_levels: 1, ty: mk_ty })),
    )?;

    // ------------------------------------------------------------------
    // Quot.sound.{u} : Π (A : Sort u) (R : A→A→Prop) (a b : A),
    //                     R a b → Eq (Quot A R) (Quot.mk A R a) (Quot.mk A R b)
    //   after all Πs: A=Var4, R=Var3, a=Var2, b=Var1, (R a b)=Var0
    // ------------------------------------------------------------------
    let sound_ty = Term::pi(
        Term::Sort(u.clone()), // A   (Var0)
        Term::pi(
            rel_ty(Term::Var(0)), // R   (A=Var0)
            Term::pi(
                Term::Var(1), // a:A (A=Var1)
                Term::pi(
                    Term::Var(2), // b:A (A=Var2)
                    Term::pi(
                        // R a b : Prop   (R=Var2, a=Var1, b=Var0)
                        Term::apps(Term::Var(2), [Term::Var(1), Term::Var(0)]),
                        // Eq (Quot A R) (mk A R a) (mk A R b)
                        //   A=Var4, R=Var3, a=Var2, b=Var1
                        eq_app(
                            u.clone(),
                            quot_app(u.clone(), Term::Var(4), Term::Var(3)),
                            mk_app(u.clone(), Term::Var(4), Term::Var(3), Term::Var(2)),
                            mk_app(u.clone(), Term::Var(4), Term::Var(3), Term::Var(1)),
                        ),
                    ),
                ),
            ),
        ),
    );
    env.insert(
        name(QUOT_SOUND),
        Decl::Quot(Rc::new(Quotient { role: QuotRole::Sound, num_levels: 1, ty: sound_ty })),
    )?;

    // ------------------------------------------------------------------
    // Quot.lift.{u v} : Π (A : Sort u) (R : A→A→Prop) (B : Sort v)
    //                      (f : A → B)
    //                      (resp : Π (a b : A), R a b → Eq B (f a) (f b)),
    //                      Quot A R → B
    //   final indices: A=Var5, R=Var4, B=Var3, f=Var2, resp=Var1, q=Var0
    // ------------------------------------------------------------------
    // resp built in context [A=Var3, R=Var2, B=Var1, f=Var0] (depth 4).
    // resp : Π (a b : A). R a b → Eq B (f a) (f b)
    let resp_ty = Term::pi(
        Term::Var(3), // a : A          (depth 4: A=Var3)
        Term::pi(
            Term::Var(4), // b : A       (depth 5: A=Var4)
            Term::pi(
                // R a b            (depth 6: R=Var4, a=Var1, b=Var0)
                Term::apps(Term::Var(4), [Term::Var(1), Term::Var(0)]),
                // Eq B (f a) (f b) (depth 7: B=Var4, f=Var3, a=Var2, b=Var1)
                eq_app(
                    v.clone(),
                    Term::Var(4),
                    Term::app(Term::Var(3), Term::Var(2)),
                    Term::app(Term::Var(3), Term::Var(1)),
                ),
            ),
        ),
    );
    let lift_ty = Term::pi(
        Term::Sort(u.clone()), // A       (Var0)
        Term::pi(
            rel_ty(Term::Var(0)), // R       (A=Var0)
            Term::pi(
                Term::Sort(v.clone()), // B       (Var0 here)
                Term::pi(
                    Term::arrow(Term::Var(2), Term::Var(0)), // f : A → B (depth 3: A=Var2,B=Var0)
                    Term::pi(
                        resp_ty, // resp
                        Term::pi(
                            // Quot A R   (A=Var4,R=Var3 at depth 5)
                            quot_app(u.clone(), Term::Var(4), Term::Var(3)),
                            Term::Var(3), // B  (B=Var2 at depth 5 → Var3 under q)
                        ),
                    ),
                ),
            ),
        ),
    );
    env.insert(
        name(QUOT_LIFT),
        Decl::Quot(Rc::new(Quotient { role: QuotRole::Lift, num_levels: 2, ty: lift_ty })),
    )?;

    // ------------------------------------------------------------------
    // Quot.ind.{u} : Π (A : Sort u) (R : A→A→Prop)
    //                   (β : Quot A R → Prop)
    //                   (h : Π (a : A), β (Quot.mk A R a)),
    //                   Π (q : Quot A R), β q
    //   final indices: A=Var4, R=Var3, β=Var2, h=Var1, q=Var0
    // ------------------------------------------------------------------
    let ind_ty = Term::pi(
        Term::Sort(u.clone()), // A   (Var0)
        Term::pi(
            rel_ty(Term::Var(0)), // R   (A=Var0)
            Term::pi(
                // β : Quot A R → Prop   (A=Var1,R=Var0)
                Term::arrow(quot_app(u.clone(), Term::Var(1), Term::Var(0)), Term::prop()),
                Term::pi(
                    // h : Π (a : A), β (Quot.mk A R a)   (A=Var2,R=Var1,β=Var0)
                    Term::pi_graded(
                        Grade::Many,
                        Term::Var(2), // a : A  (A=Var2)
                        // β (mk A R a)   (β=Var1, A=Var3,R=Var2,a=Var0)
                        Term::app(
                            Term::Var(1),
                            mk_app(u.clone(), Term::Var(3), Term::Var(2), Term::Var(0)),
                        ),
                    ),
                    Term::pi(
                        // q : Quot A R   (A=Var3,R=Var2)
                        quot_app(u.clone(), Term::Var(3), Term::Var(2)),
                        // β q   (β=Var2, q=Var0)
                        Term::app(Term::Var(2), Term::Var(0)),
                    ),
                ),
            ),
        ),
    );
    env.insert(
        name(QUOT_IND),
        Decl::Quot(Rc::new(Quotient { role: QuotRole::Ind, num_levels: 1, ty: ind_ty })),
    )?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::Checker;
    use crate::generate::{declare_inductive, eq_spec, nat_spec};
    use crate::reduce::Reducer;

    /// Build an env with `Nat`, `Eq`, and the quotient schema installed.
    fn quot_env() -> Env {
        let mut env = Env::new();
        declare_inductive(&mut env, nat_spec()).unwrap();
        declare_inductive(&mut env, eq_spec()).unwrap();
        install_quot(&mut env).unwrap();
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

    /// The trivial relation `λ _ _. True'`, where `True'` is any inhabited Prop we can
    /// point at — here we use `Eq Nat 0 0`, so the relation is provable for all pairs.
    /// Returns the relation term `A → A → Prop` for `A = Nat`.
    fn triv_rel() -> Term {
        // λ (a : Nat) (b : Nat). Eq Nat 0 0
        Term::lam(
            cn("Nat"),
            Term::lam(cn("Nat"), eq_app(Level::of_nat(1), cn("Nat"), lit(0), lit(0))),
        )
    }

    /// Every installed quotient constant is a well-formed type.
    #[test]
    fn quotient_constants_wellformed() {
        let env = quot_env();
        let chk = Checker::new(&env);
        for n in [QUOT, QUOT_MK, QUOT_SOUND, QUOT_LIFT, QUOT_IND] {
            chk.infer_closed(env.get(n).unwrap().ty())
                .unwrap_or_else(|e| panic!("{n} ill-formed: {e}"));
        }
    }

    /// Installing without `Eq` present is rejected.
    #[test]
    fn requires_eq() {
        let mut env = Env::new();
        declare_inductive(&mut env, nat_spec()).unwrap();
        let err = install_quot(&mut env).unwrap_err();
        assert!(err.contains("Eq"), "got: {err}");
    }

    /// `Quot.mk Nat R 3 : Quot Nat R` type-checks.
    #[test]
    fn mk_typechecks() {
        let env = quot_env();
        let chk = Checker::new(&env);
        let r = triv_rel();
        let mk = mk_app(Level::of_nat(1), cn("Nat"), r.clone(), lit(3));
        let ty = chk.infer_closed(&mk).unwrap();
        let expected = quot_app(Level::of_nat(1), cn("Nat"), r);
        assert!(Reducer::new(&env).is_def_eq(&ty, &expected), "got {ty:?}");
    }

    /// COMPUTATION RULE: `Quot.lift Nat R Nat f resp (Quot.mk Nat R a) ↦ f a`.
    ///
    /// We take the equality graph of `f` as the relation, `R a b := Eq Nat (f a) (f b)`,
    /// so `resp := λ a b h. h` proves respect trivially. Here `f = succ`, so lifting
    /// `mk 3` must reduce to `succ 3 = 4`. Checked on the trusted reducer AND NbE
    /// (differential), and shown to type-check at `Nat`.
    #[test]
    fn lift_computation_reduces() {
        let env = quot_env();
        let u = Level::of_nat(1);
        // f = λ n. succ n
        let f = Term::lam(cn("Nat"), Term::app(cn("Nat.succ"), Term::Var(0)));
        // R a b := Eq Nat (succ a) (succ b)   (a = Var1, b = Var0 under the two λ's).
        let rel = Term::lam(
            cn("Nat"),
            Term::lam(
                cn("Nat"),
                eq_app(
                    u.clone(),
                    cn("Nat"),
                    Term::app(cn("Nat.succ"), Term::Var(1)),
                    Term::app(cn("Nat.succ"), Term::Var(0)),
                ),
            ),
        );
        // resp = λ a b (h : R a b). h.  R a b ≡ Eq Nat (succ a) (succ b) ≡ Eq Nat (f a)(f b).
        let resp = Term::lam(
            cn("Nat"),
            Term::lam(
                cn("Nat"),
                Term::lam(
                    eq_app(
                        u.clone(),
                        cn("Nat"),
                        Term::app(cn("Nat.succ"), Term::Var(1)),
                        Term::app(cn("Nat.succ"), Term::Var(0)),
                    ),
                    Term::Var(0),
                ),
            ),
        );
        let mk = mk_app(u.clone(), cn("Nat"), rel.clone(), lit(3));
        let lift = Term::apps(
            Term::cnst(name(QUOT_LIFT), vec![u.clone(), u.clone()]),
            [cn("Nat"), rel, cn("Nat"), f, resp, mk],
        );
        // It type-checks at Nat, and reduces to 4.
        let chk = Checker::new(&env);
        chk.check(&mut crate::check::LocalCtx::new(), &lift, &cn("Nat")).unwrap();
        let red = Reducer::new(&env);
        assert!(red.is_def_eq(&lift, &lit(4)), "reducer: lift (mk 3) = 4");
        let nbe = crate::nbe::Nbe::new(&env);
        assert_eq!(nbe.normalize(&lift), lit(4), "nbe: lift (mk 3) = 4");
    }

    /// SOUNDNESS (adversarial): `Quot.sound` DOES prove `mk a = mk b` when given a real
    /// `R a b` witness; and with the *trivial always-true* relation, `mk 3 = mk 5`.
    #[test]
    fn sound_proves_mk_eq_with_witness() {
        let env = quot_env();
        let u = Level::of_nat(1);
        let r = triv_rel(); // R a b := Eq Nat 0 0, provable by Eq.refl.
        // witness : R 3 5  ==  Eq Nat 0 0  ==  Eq.refl Nat 0
        let witness = Term::apps(Term::cnst(name("Eq.refl"), vec![u.clone()]), [cn("Nat"), lit(0)]);
        // Quot.sound Nat R 3 5 witness : Eq (Quot Nat R) (mk 3) (mk 5)
        let sound = Term::apps(
            Term::cnst(name(QUOT_SOUND), vec![u.clone()]),
            [cn("Nat"), r.clone(), lit(3), lit(5), witness],
        );
        let goal = eq_app(
            u.clone(),
            quot_app(u.clone(), cn("Nat"), r.clone()),
            mk_app(u.clone(), cn("Nat"), r.clone(), lit(3)),
            mk_app(u.clone(), cn("Nat"), r, lit(5)),
        );
        let chk = Checker::new(&env);
        chk.check(&mut crate::check::LocalCtx::new(), &sound, &goal).unwrap();
    }

    /// SOUNDNESS (adversarial): you CANNOT prove `mk 3 = mk 5` without a witness. We
    /// try to pass a `Nat` (`0`) where the `R a b` proof must go — it must be rejected.
    #[test]
    fn cannot_prove_mk_eq_without_witness() {
        let env = quot_env();
        let u = Level::of_nat(1);
        // The EMPTY relation `λ a b. False`, where `False := Π (X:Prop). X`. No witness
        // for any pair exists, so `mk a = mk b` is unprovable for distinct a,b.
        let false_ty = Term::pi(Term::prop(), Term::Var(0)); // Π (X:Prop). X
        let empty_rel = Term::lam(cn("Nat"), Term::lam(cn("Nat"), false_ty.clone()));
        // Attempt: hand `Quot.sound` a bogus witness of the wrong type (`0 : Nat`).
        let sound = Term::apps(
            Term::cnst(name(QUOT_SOUND), vec![u.clone()]),
            [cn("Nat"), empty_rel.clone(), lit(3), lit(5), lit(0)],
        );
        let chk = Checker::new(&env);
        // `0 : Nat` is not a proof of `empty_rel 3 5 = False`, so this must NOT type-check.
        assert!(
            chk.infer_closed(&sound).is_err(),
            "must not fabricate mk 3 = mk 5 from a non-witness"
        );
    }

    /// SOUNDNESS (adversarial): lifting an **unrespectful** `f` is rejected, because no
    /// `resp` proof exists. With the *always-true* relation and `f = id`, respectfulness
    /// would require `Eq Nat a b` for ALL a,b — unprovable — so a bogus `resp` (here we
    /// pass `Eq.refl`-shaped term that cannot have the right dependent type) is rejected.
    #[test]
    fn unrespectful_lift_rejected() {
        let env = quot_env();
        let u = Level::of_nat(1);
        // Always-true relation: R a b := Eq Nat 0 0.
        let rel = triv_rel();
        // f = id : Nat → Nat.  Respectfulness demands `∀ a b, R a b → Eq Nat a b`, i.e.
        // Eq Nat a b for every a,b — false. Any closed `resp` we supply must fail typing.
        let f = Term::lam(cn("Nat"), Term::Var(0));
        // Bogus resp: λ a b h. Eq.refl Nat a  :  claims Eq Nat a a, but the codomain
        // required is Eq Nat a b (b ≠ a in general) — type mismatch.
        let resp = Term::lam(
            cn("Nat"),
            Term::lam(
                cn("Nat"),
                Term::lam(
                    eq_app(u.clone(), cn("Nat"), lit(0), lit(0)), // h : R a b
                    Term::apps(Term::cnst(name("Eq.refl"), vec![u.clone()]), [cn("Nat"), Term::Var(2)]),
                ),
            ),
        );
        let lift = Term::apps(
            Term::cnst(name(QUOT_LIFT), vec![u.clone(), u.clone()]),
            [cn("Nat"), rel, cn("Nat"), f, resp],
        );
        let chk = Checker::new(&env);
        assert!(
            chk.infer_closed(&lift).is_err(),
            "unrespectful lift must be rejected: no valid resp exists"
        );
    }

    /// `Quot.ind` is well-typed and can be applied (proving a Prop over the quotient).
    /// We instantiate the motive to a constant `True'` prop and discharge it, checking
    /// the eliminator's type is usable end-to-end.
    #[test]
    fn ind_applies() {
        let env = quot_env();
        let u = Level::of_nat(1);
        let r = triv_rel();
        // β := λ q. Eq Nat 0 0   (a constant Prop over the quotient)
        let beta = Term::lam(
            quot_app(u.clone(), cn("Nat"), r.clone()),
            eq_app(u.clone(), cn("Nat"), lit(0), lit(0)),
        );
        // h := λ a. Eq.refl Nat 0   : Π a, β (mk a)
        let h = Term::lam(
            cn("Nat"),
            Term::apps(Term::cnst(name("Eq.refl"), vec![u.clone()]), [cn("Nat"), lit(0)]),
        );
        // q := mk 7
        let q = mk_app(u.clone(), cn("Nat"), r.clone(), lit(7));
        let ind = Term::apps(
            Term::cnst(name(QUOT_IND), vec![u.clone()]),
            [cn("Nat"), r.clone(), beta, h, q.clone()],
        );
        // Result type: β q = Eq Nat 0 0.
        let goal = eq_app(u.clone(), cn("Nat"), lit(0), lit(0));
        let chk = Checker::new(&env);
        chk.check(&mut crate::check::LocalCtx::new(), &ind, &goal).unwrap();
    }
}
