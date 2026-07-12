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
//! This is the **fixed six-constant schema** of Lean's `Quot` plus its dependent
//! recursor (not a per-quotient datatype declaration like [`crate::generate`] or
//! [`crate::coinductive`]). It is installed **once** into the environment by
//! [`install_quot`]; every quotient the user forms is `Quot A R` for their own `A`, `R`.
//! The six constants are:
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
//!   Quot.rec.{u v} : Π (A : Sort u) (R : A → A → Prop)
//!                        (C : Quot.{u} A R → Sort v)
//!                        (f : Π (a : A), C (Quot.mk.{u} A R a))
//!                        (resp : Π (a b : A) (h : R a b),
//!                            Eq.{v} (C (Quot.mk.{u} A R b))
//!                                (Eq.rec.{u,v} (Quot.{u} A R) (Quot.mk.{u} A R a)
//!                                    (λ (y : Quot.{u} A R) (_ : Eq.{u} (Quot.{u} A R)
//!                                        (Quot.mk.{u} A R a) y). C y)
//!                                    (f a) (Quot.mk.{u} A R b) (Quot.sound.{u} A R a b h))
//!                                (f b)),
//!                        Π (q : Quot.{u} A R), C q
//! ```
//!
//! `Quot.rec` is the **dependent** recursor: it eliminates into an arbitrary `Sort v`
//! (not just non-dependent `B`), given the honest respectfulness premise that the
//! transport of `f a` along `Quot.sound A R a b h` lands (propositionally) on `f b`.
//!
//! with the **single computation rule** (ι/quotient-reduction), fired identically by
//! `Quot.lift` and `Quot.rec` (their argument spines place `f`/the scrutinee at the same
//! positions — see [`crate::reduce::Reducer::try_quot_lift`]), added to both the
//! trusted [`crate::reduce`] and the fast [`crate::nbe`]:
//!
//! ```text
//!   Quot.lift.{u v} A R B f resp (Quot.mk.{u} A R a)  ↦  f a
//!   Quot.rec.{u v}  A R C f resp (Quot.mk.{u} A R a)  ↦  f a
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
//! * `Quot.rec` generalizes `Quot.lift` to a dependent motive `C : Quot A R → Sort v`,
//!   and is sound for the same reason: its computation rule fires **only** on a literal
//!   `Quot.mk`, discarding `resp`, and `resp`'s (richer, `Eq.rec`-transporting) type must
//!   still be *type-checked to exist* before the term is accepted — an unrespectful `f`
//!   (no valid transport-respecting proof) has no such `resp` and is rejected (adversarial
//!   test `unrespectful_rec_rejected`). Setting `C := λ_. B` (constant) and building
//!   `resp` from `Quot.lift`'s simpler `Eq B (f a) (f b)` premise by transporting along
//!   `Quot.sound` recovers `Quot.lift` exactly, so `Quot.rec` is a strict
//!   generalization — it adds no proof-strength beyond what a well-typed `resp` already
//!   grants pointwise (adversarial test `rec_cannot_derive_false`), and, like `Quot.lift`,
//!   never makes `Quot.mk a` and `Quot.mk b` definitionally equal for distinct `a`, `b`
//!   absent a real `Quot.sound` witness (adversarial test
//!   `rec_does_not_collapse_distinct_mks`).
//!
//! The `Eq` inductive (with `Eq.refl` and `Eq.rec`) must already be installed;
//! `Quot.sound`, `Quot.lift`/`resp`, and `Quot.rec`/`resp` are all stated against it.

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
pub const QUOT_REC: &str = "Quot.rec";

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

/// `Quot.sound.{lvl} A R a b h`.
fn sound_app(lvl: Level, a: Term, r: Term, x: Term, y: Term, h: Term) -> Term {
    Term::apps(Term::cnst(name(QUOT_SOUND), vec![lvl]), [a, r, x, y, h])
}

/// `Eq.rec.{lvl_a, lvl_v} A' a' motive refl_case b' h'`.
#[allow(clippy::too_many_arguments)]
fn eq_rec_app(
    lvl_a: Level,
    lvl_v: Level,
    a_ty: Term,
    a_pt: Term,
    motive: Term,
    refl_case: Term,
    b_pt: Term,
    h: Term,
) -> Term {
    Term::apps(
        Term::cnst(name("Eq.rec"), vec![lvl_a, lvl_v]),
        [a_ty, a_pt, motive, refl_case, b_pt, h],
    )
}

/// Install the fixed quotient schema (`Quot`, `Quot.mk`, `Quot.sound`, `Quot.lift`,
/// `Quot.ind`, `Quot.rec`) into `env`. Requires the `Eq` inductive (with `Eq.refl` and
/// `Eq.rec`) to be present, since `Quot.sound`, the respectfulness premise of
/// `Quot.lift`, and `Quot.rec`'s dependent respectfulness premise are all stated
/// against it. Rejects re-installation (any of the six names already declared).
pub fn install_quot(env: &mut Env) -> Result<(), String> {
    match env.get("Eq") {
        Some(Decl::Inductive(_)) => {}
        _ => return Err("Quot requires the 'Eq' inductive to be installed first".to_string()),
    }
    if env.get("Eq.rec").is_none() {
        return Err("Quot requires the 'Eq.rec' recursor to be installed first".to_string());
    }
    for n in [QUOT, QUOT_MK, QUOT_SOUND, QUOT_LIFT, QUOT_IND, QUOT_REC] {
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

    // ------------------------------------------------------------------
    // Quot.rec.{u v} : Π (A : Sort u) (R : A→A→Prop)
    //                     (C : Quot A R → Sort v)
    //                     (f : Π (a : A), C (Quot.mk A R a))
    //                     (resp : Π (a b : A) (h : R a b),
    //                         Eq (C (Quot.mk A R b))
    //                            (Eq.rec.{u,v} (Quot A R) (Quot.mk A R a)
    //                                (λ (y : Quot A R) (_ : Eq (Quot A R) (Quot.mk A R a) y).
    //                                    C y)
    //                                (f a) (Quot.mk A R b) (Quot.sound A R a b h))
    //                            (f b)),
    //                     Π (q : Quot A R), C q
    //
    // This is the *dependent* recursor: `C` targets an arbitrary `Sort v`, not just
    // `Prop`. `resp` is the honest respectfulness premise for the dependent case —
    // transporting `f a : C (mk a)` along the path `Quot.sound A R a b h : mk a = mk b`
    // must land on (be propositionally equal to) `f b : C (mk b)`. It is checked to
    // *exist* at typing time (exactly like `Quot.lift`'s `resp`) and discarded by the
    // reduction rule, which fires only on the literal `Quot.mk` point constructor:
    //
    //   Quot.rec.{u v} A R C f resp (Quot.mk.{u} A R a)  ↦  f a
    //
    // Soundness: this is *exactly* the standard Lean/Coq-style dependent quotient
    // recursor. It does not weaken anything already proven sound for `Quot.lift`/
    // `Quot.sound` — `Quot.rec` with a non-dependent `C := λ _. B` and a `resp` built by
    // `Eq.rec`-transporting `Quot.lift`'s simpler `Eq B (f a) (f b)` premise recovers
    // `Quot.lift` exactly, so `Quot.rec` is a strict generalisation, not a new axiom.
    // Its computation rule fires on the *same* `Quot.mk` scrutinee condition as
    // `Quot.lift`'s (same spine layout — `f` at index 3, `q` at index 5 — see
    // `crate::reduce::Reducer::try_quot_lift`), so it inherits the identical
    // "point-constructor only, never `sound`, never neutral" firing discipline: no new
    // definitional identification of `mk a` and `mk b` is introduced.
    //   final indices: A=Var5, R=Var4, C=Var3, f=Var2, resp=Var1, q=Var0
    // ------------------------------------------------------------------
    // C's type, in context [A=Var1, R=Var0] (depth 2): Quot A R → Sort v
    let c_ty = Term::arrow(quot_app(u.clone(), Term::Var(1), Term::Var(0)), Term::Sort(v.clone()));

    // f's type, in context [A=Var2, R=Var1, C=Var0] (depth 3): Π (a:A), C (mk A R a)
    let f_ty = Term::pi(
        Term::Var(2), // a : A     (depth 4: A=Var3)
        Term::app(
            Term::Var(1), // C  (depth 4: C=Var1)
            mk_app(u.clone(), Term::Var(3), Term::Var(2), Term::Var(0)), // mk A R a
        ),
    );

    // resp's type, in context [A=Var3, R=Var2, C=Var1, f=Var0] (depth 4):
    //   Π (a b : A) (h : R a b),
    //     Eq (C (mk A R b)) (transport (f a) along (sound A R a b h)) (f b)
    let resp_ty = {
        // bind a (A=Var3): depth5  A=4,R=3,C=2,f=1,a=0
        // bind b (A=Var4): depth6  A=5,R=4,C=3,f=2,a=1,b=0
        // bind h (R a b)  : depth7 A=6,R=5,C=4,f=3,a=2,b=1,h=0
        let h_ty_at_depth6 = Term::apps(Term::Var(4), [Term::Var(1), Term::Var(0)]); // R a b

        // The conclusion, built at depth 7: A=6,R=5,C=4,f=3,a=2,b=1,h=0.
        // motive = λ (y : Quot A R) (_ : Eq (Quot A R) (mk A R a) y). C y
        let motive = {
            let y_ty = quot_app(u.clone(), Term::Var(6), Term::Var(5)); // Quot A R (depth7)
            // under y (depth8): A=7,R=6,C=5,f=4,a=3,b=2,h=1,y=0
            let under_ty = eq_app(
                u.clone(),
                quot_app(u.clone(), Term::Var(7), Term::Var(6)), // Quot A R
                mk_app(u.clone(), Term::Var(7), Term::Var(6), Term::Var(3)), // mk A R a
                Term::Var(0),                                    // y
            );
            // under _ (depth9): A=8,R=7,C=6,f=5,a=4,b=3,h=2,y=1,_=0
            let body = Term::app(Term::Var(6), Term::Var(1)); // C y
            Term::lam(y_ty, Term::lam(under_ty, body))
        };
        let refl_case = Term::app(Term::Var(3), Term::Var(2)); // f a  (depth7: f=3,a=2)
        let b_pt = mk_app(u.clone(), Term::Var(6), Term::Var(5), Term::Var(1)); // mk A R b
        let h_witness = sound_app(
            u.clone(),
            Term::Var(6),
            Term::Var(5),
            Term::Var(2),
            Term::Var(1),
            Term::Var(0),
        ); // sound A R a b h
        let a_ty_arg = quot_app(u.clone(), Term::Var(6), Term::Var(5)); // Quot A R
        let a_pt_arg = mk_app(u.clone(), Term::Var(6), Term::Var(5), Term::Var(2)); // mk A R a
        let transport = eq_rec_app(
            u.clone(),
            v.clone(),
            a_ty_arg,
            a_pt_arg,
            motive,
            refl_case,
            b_pt.clone(),
            h_witness,
        );
        let f_b = Term::app(Term::Var(3), Term::Var(1)); // f b (depth7)
        let c_of_b = Term::app(Term::Var(4), b_pt); // C (mk A R b)
        let conclusion = eq_app(v.clone(), c_of_b, transport, f_b);

        Term::pi(
            Term::Var(3), // a : A (depth4: A=Var3)
            Term::pi(
                Term::Var(4), // b : A (depth5: A=Var4)
                Term::pi(h_ty_at_depth6, conclusion),
            ),
        )
    };

    let rec_ty = Term::pi(
        Term::Sort(u.clone()), // A       (Var0)
        Term::pi(
            rel_ty(Term::Var(0)), // R       (A=Var0)
            Term::pi(
                c_ty, // C
                Term::pi(
                    f_ty, // f
                    Term::pi(
                        resp_ty, // resp
                        Term::pi(
                            // q : Quot A R   (A=Var4,R=Var3 at depth5, after resp added)
                            quot_app(u.clone(), Term::Var(4), Term::Var(3)),
                            // C q   (C=Var2 at depth5 → Var3 under q, at depth6)
                            Term::app(Term::Var(3), Term::Var(0)),
                        ),
                    ),
                ),
            ),
        ),
    );
    env.insert(
        name(QUOT_REC),
        Decl::Quot(Rc::new(Quotient { role: QuotRole::Rec, num_levels: 2, ty: rec_ty })),
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
        for n in [QUOT, QUOT_MK, QUOT_SOUND, QUOT_LIFT, QUOT_IND, QUOT_REC] {
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

    // ------------------------------------------------------------------
    // Quot.rec — the dependent recursor.
    // ------------------------------------------------------------------

    /// `transport_const A a b K x h : Eq K (Eq.rec A a (λ_ _. K) x b h) x` — the standard
    /// proof that transporting along *any* path `h : Eq A a b` is the identity when the
    /// motive is a **constant** family `K`. Built by `Eq.rec`-induction on `h` itself
    /// (motive: `λ y h'. Eq K (Eq.rec A a (λ_ _. K) x y h') x`); the base case reduces
    /// (via the *already-installed, generic* `Eq.rec` ι-rule on `Eq.refl`) to `Eq K x x`,
    /// discharged by `Eq.refl K x`. Used below to build `Quot.rec`'s `resp` premise for a
    /// **constant** motive `C := λ_. K` (the recursor still targets an arbitrary `Sort v`
    /// — this exercises the dependent constant `C` is applied through, not a special case
    /// in `Quot.rec`'s own type).
    /// `Eq.rec a_ty a_pt (λ_ _. k_ty) x b h` — the constant-motive transport term itself
    /// (not a proof about it), reusable both inside [`transport_const`] and by callers
    /// that need to name the transport as a value (e.g. as the LHS of a further `eq_trans`
    /// composition).
    #[allow(clippy::too_many_arguments)]
    fn transport_const_term(
        a_lvl: Level,
        k_lvl: Level,
        a_ty: Term,
        a_pt: Term,
        k_ty: Term,
        x: Term,
        b_pt: Term,
        h: Term,
    ) -> Term {
        // motive : Π (b:a_ty) (h:Eq a_ty a_pt b). Sort k_lvl, constant in both.
        //   domain of `b` at ambient depth D (unlifted); domain of `h` at depth D+1
        //   (a_ty/a_pt lifted by 1); body at depth D+2 (k_ty lifted by 2).
        let motive = Term::lam(
            a_ty.clone(),
            Term::lam(
                eq_app(a_lvl.clone(), a_ty.lift(1, 0), a_pt.lift(1, 0), Term::Var(0)),
                k_ty.lift(2, 0),
            ),
        );
        eq_rec_app(a_lvl, k_lvl, a_ty, a_pt, motive, x, b_pt, h)
    }

    /// `transport_const A a b K x h : Eq K (Eq.rec A a (λ_ _. K) x b h) x` — the standard
    /// proof that transporting along *any* path `h : Eq A a b` is the identity when the
    /// motive is a **constant** family `K`. Built by `Eq.rec`-induction on `h` itself
    /// (motive: `λ y h'. Eq K (Eq.rec A a (λ_ _. K) x y h') x`); the base case reduces
    /// (via the *already-installed, generic* `Eq.rec` ι-rule on `Eq.refl`) to `Eq K x x`,
    /// discharged by `Eq.refl K x`.
    #[allow(clippy::too_many_arguments)]
    fn transport_const(
        a_lvl: Level,
        k_lvl: Level,
        a_ty: Term,
        a_pt: Term,
        k_ty: Term,
        x: Term,
        b_pt: Term,
        h: Term,
    ) -> Term {
        // Outer motive `λ (y:a_ty) (h':Eq a_ty a_pt y). Eq k_ty (Eq.rec a_ty a_pt
        // (λ_ _. k_ty) x y h') x`, targeting `Prop` (`Eq` is always `Prop`-valued,
        // regardless of `k_lvl`) — this is the motive of the *outer* induction on `h`.
        let outer_motive = Term::lam(
            a_ty.clone(), // y : a_ty
            Term::lam(
                eq_app(a_lvl.clone(), a_ty.lift(1, 0), a_pt.lift(1, 0), Term::Var(0)), // h' : Eq a_ty a_pt y
                {
                    // Under [y, h'] (depth 2): a_ty/a_pt/k_ty/x need lifting by 2.
                    let transp = transport_const_term(
                        a_lvl.clone(),
                        k_lvl.clone(),
                        a_ty.lift(2, 0),
                        a_pt.lift(2, 0),
                        k_ty.lift(2, 0),
                        x.lift(2, 0),
                        Term::Var(1), // y
                        Term::Var(0), // h'
                    );
                    eq_app(k_lvl.clone(), k_ty.lift(2, 0), transp, x.lift(2, 0))
                },
            ),
        );
        let refl_case = Term::apps(Term::cnst(name("Eq.refl"), vec![k_lvl.clone()]), [k_ty.clone(), x.clone()]);
        // The *outer* Eq.rec's motive targets `Prop` (Sort 0), not `k_lvl`.
        eq_rec_app(a_lvl, Level::Zero, a_ty, a_pt, outer_motive, refl_case, b_pt, h)
    }

    /// `eq_trans k_ty lhs mid rhs p h : Eq k_ty lhs rhs`, given `p : Eq k_ty lhs mid` and
    /// `h : Eq k_ty mid rhs` — ordinary transitivity, built by `Eq.rec`-induction on `h`
    /// with motive `λ (z:k_ty) (_:Eq k_ty mid z). Eq k_ty lhs z` (base case: `p` itself,
    /// since the motive at `(mid, refl)` reduces to `Eq k_ty lhs mid`).
    fn eq_trans(k_lvl: Level, k_ty: Term, lhs: Term, mid: Term, rhs: Term, p: Term, h: Term) -> Term {
        // motive, under [z, _] (depth 2): lhs/mid lifted by 2.
        let motive = Term::lam(
            k_ty.clone(), // z : k_ty
            Term::lam(
                eq_app(k_lvl.clone(), k_ty.lift(1, 0), mid.lift(1, 0), Term::Var(0)), // _ : Eq k_ty mid z
                eq_app(k_lvl.clone(), k_ty.lift(2, 0), lhs.lift(2, 0), Term::Var(1)), // Eq k_ty lhs z
            ),
        );
        eq_rec_app(k_lvl, Level::Zero, k_ty, mid, motive, p, rhs, h)
    }

    /// COMPUTATION RULE (dependent): `Quot.rec A R C f resp (Quot.mk A R a) ↦ f a`, for a
    /// (constant) `Sort v`-valued motive `C := λ_. Nat`. Checked on the trusted reducer
    /// AND NbE (differential), exactly like `lift_computation_reduces`.
    #[test]
    fn rec_computation_reduces_dependent() {
        let env = quot_env();
        let u = Level::of_nat(1);
        let v = Level::of_nat(1);
        // R a b := Eq Nat (succ a) (succ b)  (a=Var1,b=Var0 under the two λ's)
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
        let quot_ty = quot_app(u.clone(), cn("Nat"), rel.clone());
        // C := λ (_:Quot Nat R). Nat   (constant motive into Type 0)
        let c = Term::lam(quot_ty.clone(), cn("Nat"));
        // f := λ n. succ n
        let f = Term::lam(cn("Nat"), Term::app(cn("Nat.succ"), Term::Var(0)));
        // resp := λ a b h. transport_const (Quot Nat R) (mk a) (mk b) Nat (f a) (sound a b h) : Eq Nat (Eq.rec ... ) (f b)
        //   built under [a:Nat, b:Nat, h:R a b] (depth3: a=2,b=1,h=0)
        let resp = Term::lam(
            cn("Nat"),
            Term::lam(
                cn("Nat"),
                Term::lam(
                    Term::apps(rel.lift(2, 0), [Term::Var(1), Term::Var(0)]), // R a b, lifted under a,b
                    {
                        let a_ty = quot_ty.clone().lift(3, 0);
                        let a_pt = mk_app(u.clone(), cn("Nat").lift(3, 0), rel.clone().lift(3, 0), Term::Var(2));
                        let b_pt = mk_app(u.clone(), cn("Nat").lift(3, 0), rel.clone().lift(3, 0), Term::Var(1));
                        let h_witness = sound_app(
                            u.clone(),
                            cn("Nat").lift(3, 0),
                            rel.clone().lift(3, 0),
                            Term::Var(2),
                            Term::Var(1),
                            Term::Var(0),
                        );
                        let f_a = Term::app(f.clone().lift(3, 0), Term::Var(2));
                        let f_b = Term::app(f.clone().lift(3, 0), Term::Var(1));
                        // p : Eq Nat (transport (f a)) (f a)   — transport is the identity
                        // on a constant motive, regardless of *which* path it transports
                        // along.
                        let transport_term = transport_const_term(
                            u.clone(),
                            v.clone(),
                            a_ty.clone(),
                            a_pt.clone(),
                            cn("Nat"),
                            f_a.clone(),
                            b_pt.clone(),
                            h_witness.clone(),
                        );
                        let p = transport_const(
                            u.clone(),
                            v.clone(),
                            a_ty,
                            a_pt,
                            cn("Nat"),
                            f_a.clone(),
                            b_pt,
                            h_witness,
                        );
                        // `h : R a b` unfolds (by construction of `rel`) to exactly
                        // `Eq Nat (f a) (f b)` — compose `p` with it via transitivity to
                        // land on the required `Eq Nat (transport (f a)) (f b)`.
                        eq_trans(v.clone(), cn("Nat"), transport_term, f_a, f_b, p, Term::Var(0))
                    },
                ),
            ),
        );
        let mk = mk_app(u.clone(), cn("Nat"), rel.clone(), lit(3));
        let rec = Term::apps(
            Term::cnst(name(QUOT_REC), vec![u.clone(), v.clone()]),
            [cn("Nat"), rel, c, f, resp, mk],
        );
        let chk = Checker::new(&env);
        chk.check(&mut crate::check::LocalCtx::new(), &rec, &cn("Nat")).unwrap();
        let red = Reducer::new(&env);
        assert!(red.is_def_eq(&rec, &lit(4)), "reducer: rec (mk 3) = 4");
        let nbe = crate::nbe::Nbe::new(&env);
        assert_eq!(nbe.normalize(&rec), lit(4), "nbe: rec (mk 3) = 4");
    }

    /// `Quot.rec` is well-typed at every quantifier level (in addition to the blanket
    /// `quotient_constants_wellformed` test already exercising this).
    #[test]
    fn rec_constant_wellformed() {
        let env = quot_env();
        let chk = Checker::new(&env);
        chk.infer_closed(env.get(QUOT_REC).unwrap().ty()).unwrap();
    }

    /// SOUNDNESS (adversarial): a `Quot.rec` application with a bogus `resp` (wrong type,
    /// no valid respectfulness proof) is rejected — mirrors `unrespectful_lift_rejected`.
    #[test]
    fn unrespectful_rec_rejected() {
        let env = quot_env();
        let u = Level::of_nat(1);
        let v = Level::of_nat(1);
        let rel = triv_rel(); // R a b := Eq Nat 0 0 (always true)
        let quot_ty = quot_app(u.clone(), cn("Nat"), rel.clone());
        let c = Term::lam(quot_ty, cn("Nat"));
        let f = Term::lam(cn("Nat"), Term::Var(0)); // f = id
        // Bogus resp: claims `Eq Nat (f a) (f a)` regardless of b — ill-typed against the
        // required `Eq Nat (transport (f a)) (f b)` (the checker must catch the mismatch;
        // we pass a term whose *type* is simply wrong: `0 : Nat` where a proof is required).
        let resp = Term::lam(cn("Nat"), Term::lam(cn("Nat"), Term::lam(eq_app(u.clone(), cn("Nat"), lit(0), lit(0)), lit(0))));
        let rec = Term::apps(
            Term::cnst(name(QUOT_REC), vec![u.clone(), v]),
            [cn("Nat"), rel, c, f, resp],
        );
        let chk = Checker::new(&env);
        assert!(chk.infer_closed(&rec).is_err(), "bogus resp must be rejected");
    }

    /// SOUNDNESS (adversarial): `Quot.rec` cannot be used to derive `False`. We eliminate
    /// into the constant motive `C := λ_. False` (`False := Π (X:Prop). X`); since no `f :
    /// Π a, False` exists in the empty context (there is no way to inhabit `False`), any
    /// attempt to build the eliminator application without first having a term of type
    /// `False` fails to type-check — `Quot.rec` grants no extra proof-strength.
    #[test]
    fn rec_cannot_derive_false() {
        let env = quot_env();
        let u = Level::of_nat(1);
        let v = Level::of_nat(1);
        let rel = triv_rel();
        let quot_ty = quot_app(u.clone(), cn("Nat"), rel.clone());
        let false_ty = Term::pi(Term::prop(), Term::Var(0)); // Π (X:Prop). X
        let c = Term::lam(quot_ty, false_ty);
        // We do NOT have a real `f : Π a, False`; try to fabricate one out of thin air by
        // using an ill-typed placeholder (`0 : Nat`, not a function `Nat → False`). Even
        // getting this far requires `f` to type-check against `Π a, C (mk a)` before
        // `resp`/`q` are ever considered, so the partial application already fails.
        let bogus_f = lit(0);
        let rec = Term::apps(Term::cnst(name(QUOT_REC), vec![u.clone(), v]), [cn("Nat"), rel, c, bogus_f]);
        let chk = Checker::new(&env);
        assert!(chk.infer_closed(&rec).is_err(), "must not be able to derive False via Quot.rec");
    }

    /// SOUNDNESS (adversarial): `Quot.mk a` and `Quot.mk b` are still not made
    /// **definitionally** equal by the presence of `Quot.rec` — the reducer only fires the
    /// ι-rule on a literal `Quot.mk` scrutinee, and distinct closed representatives remain
    /// distinct values under `whnf`/`is_def_eq` absent an actual `Eq` proof between them.
    #[test]
    fn rec_does_not_collapse_distinct_mks() {
        let env = quot_env();
        let u = Level::of_nat(1);
        // The EMPTY relation: no witness exists for any pair, so mk 3 and mk 5 are
        // propositionally *unrelated*, and must remain definitionally distinct.
        let false_ty = Term::pi(Term::prop(), Term::Var(0));
        let empty_rel = Term::lam(cn("Nat"), Term::lam(cn("Nat"), false_ty));
        let mk3 = mk_app(u.clone(), cn("Nat"), empty_rel.clone(), lit(3));
        let mk5 = mk_app(u.clone(), cn("Nat"), empty_rel, lit(5));
        let red = Reducer::new(&env);
        assert!(!red.is_def_eq(&mk3, &mk5), "mk 3 and mk 5 must not collapse definitionally");
    }
}
