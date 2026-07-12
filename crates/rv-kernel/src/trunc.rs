//! Propositional truncation `∥A∥` — the canonical **higher inductive type** (HIT).
//!
//! ## What this delivers
//!
//! Given `A : Sort u`, the **propositional truncation** `Trunc A : Prop` is the type `A`
//! with *all of its elements identified*. It is a HIT with two constructors:
//!
//! * a **point** constructor `tr : A → ∥A∥` (every `a : A` yields an element `tr a`), and
//! * a **path/equality** constructor making `∥A∥` a *mere proposition*: any two of its
//!   elements are equal. Where a point constructor introduces *inhabitants*, a path
//!   constructor introduces *equalities between inhabitants* — this is exactly what lifts
//!   an inductive type to a **higher** inductive type.
//!
//! Propositional truncation is the 1-HIT: it lets a proof "forget" the witness of an
//! existential while keeping its truth. `∥A∥` is inhabited iff `A` is, but `∥A∥` carries
//! *no more information* than the bare proposition "`A` is inhabited" — you may use a
//! proof of `∥A∥` only to build another proposition (or a type already known to be a mere
//! proposition), never to project the underlying `a : A` back out. That restriction is
//! precisely what the recursor's respectfulness premise enforces.
//!
//! Like [`crate::quotient`] this is a **fixed six-constant schema**, installed once by
//! [`install_trunc`]; every truncation the user forms is `Trunc A` for their own `A`.
//! The six constants are:
//!
//! ```text
//!   Trunc.{u}       : Π (A : Sort u), Prop
//!   Trunc.tr.{u}    : Π (A : Sort u), A → Trunc.{u} A
//!   Trunc.eq.{u}    : Π (A : Sort u) (x y : Trunc.{u} A),
//!                         Eq.{0} (Trunc.{u} A) x y
//!   Trunc.lift.{u v}: Π (A : Sort u) (P : Sort v)
//!                         (f : A → P)
//!                         (resp : Π (x y : A), Eq.{v} P (f x) (f y)),
//!                         Trunc.{u} A → P
//!   Trunc.ind.{u}   : Π (A : Sort u) (β : Trunc.{u} A → Prop)
//!                         (h : Π (a : A), β (Trunc.tr.{u} A a)),
//!                         Π (t : Trunc.{u} A), β t
//!   Trunc.rec.{u v} : Π (A : Sort u) (C : Trunc.{u} A → Sort v)
//!                         (isProp : Π (t : Trunc.{u} A) (x y : C t), Eq.{v} (C t) x y)
//!                         (f : Π (a : A), C (Trunc.tr.{u} A a)),
//!                         Π (t : Trunc.{u} A), C t
//! ```
//!
//! `Trunc.rec` is the **isProp-guarded dependent** recursor: it eliminates into an
//! arbitrary `Sort v` (not just `Prop`), given a proof `isProp` that the motive `C` is a
//! mere proposition *at every point* — see "The isProp-guarded dependent recursor" below.
//!
//! with the **single computation rule** (the point-constructor ι-rule), fired identically
//! by `Trunc.lift` and `Trunc.rec` (their argument spines place `f`/the scrutinee at
//! analogous positions — see [`crate::reduce::Reducer::try_trunc_lift`] and
//! [`crate::reduce::Reducer::try_trunc_rec`]), added to both the trusted
//! [`crate::reduce`] and the fast [`crate::nbe`]:
//!
//! ```text
//!   Trunc.lift.{u v} A P f resp        (Trunc.tr.{u} A a)  ↦  f a
//!   Trunc.rec.{u v}  A C isProp f      (Trunc.tr.{u} A a)  ↦  f a
//! ```
//!
//! The path constructor `Trunc.eq` has **no computation rule** — its whole content is the
//! propositional equality it constructs. This is what keeps the HIT within ordinary
//! (non-cubical) type theory: the path holds only *propositionally* (through `Eq`), never
//! definitionally, so no interval/`transp`/`hcomp` machinery is required.
//!
//! ## The recursor and its respectfulness premise
//!
//! `Trunc.lift` is the non-dependent recursor. Since `∥A∥` collapses every element to a
//! single one, a function `∥A∥ → P` may only exist when the composite `A --tr--> ∥A∥ --> P`
//! *cannot observe which representative it came from* — i.e. `f`'s image is a mere
//! proposition. We phrase that condition, as is standard, by requiring a proof
//!
//! ```text
//!   resp : Π (x y : A), Eq P (f x) (f y)
//! ```
//!
//! that `f` sends **all** inputs to *equal* outputs. (For a general `P` this is the honest
//! statement that `f` factors through `∥A∥`; for `P : Prop` it is automatic, and one may
//! pass `λ x y. proof-irrelevance …`.) The computation rule discards `resp` at reduction
//! time exactly as `Quot.lift` discards its `resp`: soundness comes from `resp` having
//! been *type-checked to exist*.
//!
//! ## Why this is SOUND
//!
//! * `Trunc.eq` is an **axiom-shaped** constant: it *constructs* a proof of `x = y` in
//!   `∥A∥`, but does so only at the `Eq` (propositional) level. There is **no** reduction
//!   that makes `tr a` and `tr b` definitionally convertible, and no reduction on `eq`
//!   itself. Two distinct closed point values `tr a`, `tr b` therefore remain distinct
//!   *values* — conversion never collapses them — so canonicity is preserved and `False`
//!   cannot be derived by turning the path into a definitional equality (adversarial test
//!   `path_is_only_propositional`).
//!
//! * `Trunc.lift`'s computation rule fires **only** on a literal `Trunc.tr` application —
//!   never on `eq`, never on a neutral. Type-checking a `Trunc.lift … f resp …` *forces*
//!   `resp` to prove `f` is constant up to `Eq`; a non-constant `f` into a type that is
//!   not a mere proposition has no such `resp`, so the term does not type-check
//!   (adversarial test `unrespectful_lift_rejected`, `cannot_extract_witness`). Because
//!   `resp` only ever proves an `Eq` and never appears in the reduct `f a`, and because
//!   `resp` guarantees `f x` and `f y` are propositionally equal for *any* two
//!   representatives, the rule is confluent with `eq` and preserves subject reduction:
//!   whichever representative a value of `∥A∥` "is", the reduct is the same up to the
//!   equality `eq`/`resp` supply.
//!
//! * `Trunc.ind` eliminates **only into `Prop`** (its motive `β : Trunc A → Prop`) and has
//!   *no computation rule*. As with `Quot.ind`, proof irrelevance in `Prop` makes the
//!   missing `ind (tr a) ↦ h a` reduction unobservable, and confines the dependent
//!   eliminator to the one universe where respecting the path constructor `eq` is
//!   automatic (any two proofs of `β t` are already definitionally equal, so `β`
//!   trivially respects `eq`).
//!
//! * `Trunc.rec` generalizes elimination to an arbitrary `Sort v` — see "The
//!   isProp-guarded dependent recursor" below for why its `isProp` premise alone (with
//!   no per-witness transport clause, unlike `Quot.rec`'s `resp`) suffices for soundness.
//!
//! The `Eq` inductive (with `Eq.refl`) must already be installed; `Trunc.eq`,
//! `Trunc.lift`/`resp`, and `Trunc.rec`/`isProp` are all stated against it.
//!
//! ## The isProp-guarded dependent recursor
//!
//! `Trunc.rec A C isProp f` eliminates `∥A∥` into a **dependent** motive
//! `C : ∥A∥ → Sort v` (not just a non-dependent `P`), given
//!
//! ```text
//!   isProp : Π (t : ∥A∥) (x y : C t), Eq (C t) x y
//! ```
//!
//! — a proof that `C t` is a mere proposition **at every point** `t`, and
//! `f : Π (a : A), C (tr a)` handling the point case. Unlike `Quot.rec` (see
//! [`crate::quotient`]), whose path constructor `Quot.sound` is *indexed by a user
//! relation* `R a b`, so its respectfulness premise `resp` is stated pointwise over
//! `R`'s actual witnesses, `Trunc.eq` is a path **between every pair** of already
//! truncated points, with no user-supplied index to case on. `isProp` compensates for
//! that missing index by being a **global**, not per-witness, guarantee: because it
//! proves *any two* elements of `C t` equal for a fixed `t`, it in particular proves any
//! transported value in `C t` equal to any other value of `C t` — including the specific
//! transport that respecting `Trunc.eq` would require — **without** needing to name that
//! transport inside `Trunc.rec`'s own type (contrast `Quot.rec`'s `resp`, whose type
//! literally mentions `Eq.rec`-transporting `f a` along `Quot.sound A R a b h`). This is
//! what makes `Trunc.rec`'s type strictly simpler than `Quot.rec`'s despite eliminating a
//! "harder" HIT (unconditional path vs. relation-indexed path): the same fact that makes
//! `∥A∥`'s path constructor *global* also makes its respectfulness condition
//! *point-local* rather than *pairwise-witnessed*.
//!
//! Concretely: for any `x y : ∥A∥` connected by `Trunc.eq x y : x = y`, transporting
//! `Trunc.rec … x` along that path lands in `C y`; that transported value and
//! `Trunc.rec … y` are *both* elements of `C y`, so `isProp y` (applied to those two
//! particular elements) proves them equal — for **every** path `Trunc.eq` can produce,
//! simultaneously, with a single global premise. Its computation rule fires only on the
//! literal `Trunc.tr` point constructor, exactly like `Trunc.lift`'s, discarding
//! `isProp` (checked to *exist* at typing time, never appearing in the reduct):
//!
//! ```text
//!   Trunc.rec.{u v} A C isProp f (Trunc.tr.{u} A a)  ↦  f a
//! ```
//!
//! `C := λ_. Nat` is **not** a mere proposition — `isProp` would require `Eq Nat x y`
//! for *all* naturals `x y`, which is false and has no closed proof — so no witness can
//! be extracted out of `∥A∥` this way (adversarial tests `rec_cannot_extract_witness`,
//! `rec_unrespectful_rejected`). Setting `C := λ_. P` (constant) and taking `isProp` from
//! the *always-true-because-`P`-is-a-Prop* case recovers exactly `Trunc.lift`'s
//! shape, so `Trunc.rec` is a genuine generalization, not a new axiom (adversarial test
//! `rec_cannot_derive_false`); like `Trunc.lift`, it never makes `tr a` and `tr b`
//! definitionally equal for distinct `a`, `b` — the reducer's ι-rule fires only on a
//! literal `Trunc.tr` scrutinee, never on `eq` (adversarial test
//! `rec_does_not_fire_on_path`), and `Trunc.eq`'s identification stays purely
//! propositional (`path_is_only_propositional` already covers this at the value level,
//! independent of which eliminator is in play).
//!
//! ## Supported class
//!
//! This module ships **exactly one** HIT — propositional truncation — as a fully sound,
//! kernel-checked primitive. The supported eliminations are:
//!   * the non-dependent recursor `Trunc.lift` into any `P : Sort v`, gated by the
//!     respectfulness premise `resp`;
//!   * the dependent `Prop`-eliminator `Trunc.ind`;
//!   * the **isProp-guarded dependent** recursor `Trunc.rec` into any `C : ∥A∥ → Sort v`,
//!     gated by the pointwise mere-proposition premise `isProp`.
//!
//! A fully **general** 1-HIT schema (arbitrary point + path constructors, each with its
//! own independent respectfulness premise) remains out of scope — it is `Trunc.eq`'s
//! specific shape (a path between *every* pair of points, needing no user witness) that
//! makes `isProp` alone sufficient here; an arbitrary path constructor indexed by
//! genuine witness data would need a `Quot.rec`-style per-witness transport premise
//! instead, which this module does not attempt to generalize to.

use crate::env::{Decl, Env, Trunc, TruncRole};
use crate::level::Level;
use crate::term::{name, Grade, Term};
use std::rc::Rc;

/// Names of the five propositional-truncation constants.
pub const TRUNC: &str = "Trunc";
pub const TRUNC_TR: &str = "Trunc.tr";
pub const TRUNC_EQ: &str = "Trunc.eq";
pub const TRUNC_LIFT: &str = "Trunc.lift";
pub const TRUNC_IND: &str = "Trunc.ind";
pub const TRUNC_REC: &str = "Trunc.rec";

/// `Trunc.{lvl} A`.
fn trunc_app(lvl: Level, a: Term) -> Term {
    Term::app(Term::cnst(name(TRUNC), vec![lvl]), a)
}

/// `Trunc.tr.{lvl} A x`.
fn tr_app(lvl: Level, a: Term, x: Term) -> Term {
    Term::apps(Term::cnst(name(TRUNC_TR), vec![lvl]), [a, x])
}

/// `Eq.{lvl} T x y`.
fn eq_app(lvl: Level, t: Term, x: Term, y: Term) -> Term {
    Term::apps(Term::cnst(name("Eq"), vec![lvl]), [t, x, y])
}

/// Install the fixed propositional-truncation schema (`Trunc`, `Trunc.tr`, `Trunc.eq`,
/// `Trunc.lift`, `Trunc.ind`) into `env`. Requires the `Eq` inductive (with `Eq.refl`) to
/// be present, since `Trunc.eq` and the respectfulness premise of `Trunc.lift` are stated
/// against it. Rejects re-installation (any of the five names already declared).
pub fn install_trunc(env: &mut Env) -> Result<(), String> {
    match env.get("Eq") {
        Some(Decl::Inductive(_)) => {}
        _ => return Err("Trunc requires the 'Eq' inductive to be installed first".to_string()),
    }
    for n in [TRUNC, TRUNC_TR, TRUNC_EQ, TRUNC_LIFT, TRUNC_IND, TRUNC_REC] {
        if env.contains(n) {
            return Err(format!("'{n}' is already declared"));
        }
    }

    let u = Level::param(0); // the carrier universe.
    let v = Level::param(1); // Trunc.lift's result universe.
    // `Trunc A : Prop`, and `Eq` over a `Prop` value is `Eq.{0} …` (its type arg lives in
    // `Sort 0 = Prop`).
    let zero = Level::of_nat(0);

    // ------------------------------------------------------------------
    // Trunc.{u} : Π (A : Sort u), Prop
    // ------------------------------------------------------------------
    let trunc_ty = Term::pi(Term::Sort(u.clone()), Term::prop());
    env.insert(
        name(TRUNC),
        Decl::Trunc(Rc::new(Trunc { role: TruncRole::Type, num_levels: 1, ty: trunc_ty })),
    )?;

    // ------------------------------------------------------------------
    // Trunc.tr.{u} : Π (A : Sort u), A → Trunc A
    //   binders: A = Var1, x = Var0
    // ------------------------------------------------------------------
    let tr_ty = Term::pi(
        Term::Sort(u.clone()), // A            (Var0)
        Term::pi(
            Term::Var(0),                       // x : A     (A=Var0)
            trunc_app(u.clone(), Term::Var(1)), // Trunc A   (A=Var1)
        ),
    );
    env.insert(
        name(TRUNC_TR),
        Decl::Trunc(Rc::new(Trunc { role: TruncRole::Tr, num_levels: 1, ty: tr_ty })),
    )?;

    // ------------------------------------------------------------------
    // Trunc.eq.{u} : Π (A : Sort u) (x y : Trunc A), Eq (Trunc A) x y
    //   after all Πs: A=Var2, x=Var1, y=Var0
    // ------------------------------------------------------------------
    let eq_ty = Term::pi(
        Term::Sort(u.clone()), // A   (Var0)
        Term::pi(
            trunc_app(u.clone(), Term::Var(0)), // x : Trunc A   (A=Var0)
            Term::pi(
                trunc_app(u.clone(), Term::Var(1)), // y : Trunc A   (A=Var1)
                // Eq (Trunc A) x y   (A=Var2, x=Var1, y=Var0)
                eq_app(
                    zero.clone(),
                    trunc_app(u.clone(), Term::Var(2)),
                    Term::Var(1),
                    Term::Var(0),
                ),
            ),
        ),
    );
    env.insert(
        name(TRUNC_EQ),
        Decl::Trunc(Rc::new(Trunc { role: TruncRole::Eq, num_levels: 1, ty: eq_ty })),
    )?;

    // ------------------------------------------------------------------
    // Trunc.lift.{u v} : Π (A : Sort u) (P : Sort v)
    //                       (f : A → P)
    //                       (resp : Π (x y : A), Eq P (f x) (f y)),
    //                       Trunc A → P
    //   final indices: A=Var4, P=Var3, f=Var2, resp=Var1, t=Var0
    // ------------------------------------------------------------------
    // resp built in context [A=Var2, P=Var1, f=Var0] (depth 3).
    // resp : Π (x y : A). Eq P (f x) (f y)
    let resp_ty = Term::pi(
        Term::Var(2), // x : A          (depth 3: A=Var2)
        Term::pi(
            Term::Var(3), // y : A       (depth 4: A=Var3)
            // Eq P (f x) (f y)  (depth 5: P=Var3, f=Var2, x=Var1, y=Var0)
            eq_app(
                v.clone(),
                Term::Var(3),
                Term::app(Term::Var(2), Term::Var(1)),
                Term::app(Term::Var(2), Term::Var(0)),
            ),
        ),
    );
    let lift_ty = Term::pi(
        Term::Sort(u.clone()), // A       (Var0)
        Term::pi(
            Term::Sort(v.clone()), // P       (Var0 here)
            Term::pi(
                Term::arrow(Term::Var(1), Term::Var(0)), // f : A → P (depth 2: A=Var1,P=Var0)
                Term::pi(
                    resp_ty, // resp
                    Term::pi(
                        trunc_app(u.clone(), Term::Var(3)), // Trunc A (depth 4: A=Var3)
                        Term::Var(3),                       // P  (P=Var2 at depth 4 → Var3 under t)
                    ),
                ),
            ),
        ),
    );
    env.insert(
        name(TRUNC_LIFT),
        Decl::Trunc(Rc::new(Trunc { role: TruncRole::Lift, num_levels: 2, ty: lift_ty })),
    )?;

    // ------------------------------------------------------------------
    // Trunc.ind.{u} : Π (A : Sort u) (β : Trunc A → Prop)
    //                    (h : Π (a : A), β (Trunc.tr A a)),
    //                    Π (t : Trunc A), β t
    //   final indices: A=Var3, β=Var2, h=Var1, t=Var0
    // ------------------------------------------------------------------
    let ind_ty = Term::pi(
        Term::Sort(u.clone()), // A   (Var0)
        Term::pi(
            // β : Trunc A → Prop   (A=Var0)
            Term::arrow(trunc_app(u.clone(), Term::Var(0)), Term::prop()),
            Term::pi(
                // h : Π (a : A), β (Trunc.tr A a)   (A=Var1, β=Var0)
                Term::pi_graded(
                    Grade::Many,
                    Term::Var(1), // a : A  (A=Var1)
                    // β (tr A a)   (β=Var1, A=Var2, a=Var0)
                    Term::app(Term::Var(1), tr_app(u.clone(), Term::Var(2), Term::Var(0))),
                ),
                Term::pi(
                    // t : Trunc A   (A=Var2)
                    trunc_app(u.clone(), Term::Var(2)),
                    // β t   (β=Var2, t=Var0)
                    Term::app(Term::Var(2), Term::Var(0)),
                ),
            ),
        ),
    );
    env.insert(
        name(TRUNC_IND),
        Decl::Trunc(Rc::new(Trunc { role: TruncRole::Ind, num_levels: 1, ty: ind_ty })),
    )?;

    // ------------------------------------------------------------------
    // Trunc.rec.{u v} : Π (A : Sort u) (C : Trunc A → Sort v)
    //                      (isProp : Π (t : Trunc A) (x y : C t), Eq (C t) x y)
    //                      (f : Π (a : A), C (Trunc.tr A a)),
    //                      Π (t : Trunc A), C t
    //
    // The **isProp-guarded dependent** recursor. Unlike `Quot.rec` (whose path
    // constructor `Quot.sound` is indexed by a user relation `R a b`, so its
    // respectfulness premise is stated pointwise over `R`'s witnesses), `Trunc.eq`
    // relates *every* pair of points with no witness data to case on. The guard that
    // makes elimination sound here is instead a **global** one: `isProp` asserts that
    // `C t` is a mere proposition for *every* `t : Trunc A`, which is exactly the
    // condition under which the choice of representative becomes unobservable —
    // *any* two elements of `C t` (in particular a transported `f a` and a `f b`) are
    // already provably equal, so no `Eq.rec`-transport premise per path witness is
    // needed at all (contrast `Quot.rec`'s `resp`, which must mention the specific
    // `Quot.sound A R a b h` witness because `Quot`'s path constructor is conditional).
    //
    //   Trunc.rec.{u v} A C isProp f (Trunc.tr.{u} A a)  ↦  f a
    //
    // Soundness: this fires only on the literal point constructor `Trunc.tr`, never on
    // `Trunc.eq`, and discards `isProp`/nothing else — `isProp` is checked to *exist*
    // at typing time. For any `x y : Trunc A` connected by `Trunc.eq x y : x = y`,
    // transporting `Trunc.rec … x` along that path lands in `C y`; `isProp y` proves
    // that transported value equal to `Trunc.rec … y` *because it proves ALL pairs of
    // elements of `C y` equal*, without needing to construct the transport term inside
    // `Trunc.rec`'s own type. `C := λ_. Nat` (not a mere proposition — `isProp` would
    // require `Eq Nat x y` for all naturals, unprovable) has no valid `isProp`, so no
    // witness can be extracted out of `Trunc A` this way (adversarial test
    // `rec_unrespectful_rejected`/`rec_cannot_extract_witness`).
    //   final indices: A=Var4, C=Var3, isProp=Var2, f=Var1, t=Var0
    // ------------------------------------------------------------------
    // C's type, in context [A=Var0] (depth 1): Trunc A → Sort v
    let rec_c_ty = Term::arrow(trunc_app(u.clone(), Term::Var(0)), Term::Sort(v.clone()));

    // isProp's type, in context [A=Var1, C=Var0] (depth 2):
    //   Π (t : Trunc A) (x y : C t), Eq (C t) x y
    let is_prop_ty = Term::pi(
        trunc_app(u.clone(), Term::Var(1)), // t : Trunc A   (depth3: A=Var2)
        Term::pi(
            Term::app(Term::Var(1), Term::Var(0)), // x : C t   (depth4: C=Var2,t=Var1 -> at depth3 C=Var1,t=Var0)
            Term::pi(
                Term::app(Term::Var(2), Term::Var(1)), // y : C t   (depth5)
                // Eq (C t) x y   (depth6: C=Var3,t=Var2,x=Var1,y=Var0)
                eq_app(
                    v.clone(),
                    Term::app(Term::Var(3), Term::Var(2)),
                    Term::Var(1),
                    Term::Var(0),
                ),
            ),
        ),
    );

    // f's type, in context [A=Var2, C=Var1, isProp=Var0] (depth 3): Π (a:A), C (Trunc.tr A a)
    let rec_f_ty = Term::pi(
        Term::Var(2), // a : A     (depth4: A=Var3)
        Term::app(
            Term::Var(2), // C   (depth4: C=Var2)
            tr_app(u.clone(), Term::Var(3), Term::Var(0)), // Trunc.tr A a
        ),
    );

    let rec_ty = Term::pi(
        Term::Sort(u.clone()), // A       (Var0)
        Term::pi(
            rec_c_ty, // C
            Term::pi(
                is_prop_ty, // isProp
                Term::pi(
                    rec_f_ty, // f
                    Term::pi(
                        // t : Trunc A   (A=Var3 at depth4, after f added)
                        trunc_app(u.clone(), Term::Var(3)),
                        // C t   (C=Var3 at depth4 -> Var4 under t, at depth5)
                        Term::app(Term::Var(3), Term::Var(0)),
                    ),
                ),
            ),
        ),
    );
    env.insert(
        name(TRUNC_REC),
        Decl::Trunc(Rc::new(Trunc { role: TruncRole::Rec, num_levels: 2, ty: rec_ty })),
    )?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::Checker;
    use crate::generate::{declare_inductive, eq_spec, nat_spec};
    use crate::reduce::Reducer;

    /// Build an env with `Nat`, `Eq`, and the truncation schema installed.
    fn trunc_env() -> Env {
        let mut env = Env::new();
        declare_inductive(&mut env, nat_spec()).unwrap();
        declare_inductive(&mut env, eq_spec()).unwrap();
        install_trunc(&mut env).unwrap();
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

    /// Every installed truncation constant is a well-formed type.
    #[test]
    fn trunc_constants_wellformed() {
        let env = trunc_env();
        let chk = Checker::new(&env);
        for n in [TRUNC, TRUNC_TR, TRUNC_EQ, TRUNC_LIFT, TRUNC_IND, TRUNC_REC] {
            chk.infer_closed(env.get(n).unwrap().ty())
                .unwrap_or_else(|e| panic!("{n} ill-formed: {e}"));
        }
    }

    /// Installing without `Eq` present is rejected.
    #[test]
    fn requires_eq() {
        let mut env = Env::new();
        declare_inductive(&mut env, nat_spec()).unwrap();
        let err = install_trunc(&mut env).unwrap_err();
        assert!(err.contains("Eq"), "got: {err}");
    }

    /// Re-installation is rejected.
    #[test]
    fn rejects_double_install() {
        let mut env = trunc_env();
        let err = install_trunc(&mut env).unwrap_err();
        assert!(err.contains("already declared"), "got: {err}");
    }

    /// `Trunc.tr Nat 3 : Trunc Nat` type-checks, and `Trunc Nat : Prop`.
    #[test]
    fn tr_typechecks() {
        let env = trunc_env();
        let chk = Checker::new(&env);
        let u = Level::of_nat(1);
        let tr = tr_app(u.clone(), cn("Nat"), lit(3));
        let ty = chk.infer_closed(&tr).unwrap();
        let expected = trunc_app(u.clone(), cn("Nat"));
        assert!(Reducer::new(&env).is_def_eq(&ty, &expected), "got {ty:?}");
        // Trunc Nat : Prop
        let sort = chk.infer_closed(&expected).unwrap();
        assert!(Reducer::new(&env).is_def_eq(&sort, &Term::prop()), "Trunc Nat not a Prop");
    }

    /// COMPUTATION RULE: `Trunc.lift Nat Nat f resp (Trunc.tr Nat a) ↦ f a`.
    ///
    /// We lift into `Nat` with `f = succ`; respectfulness demands `succ x = succ y` for
    /// ALL x,y, which is false — so to have a valid `resp` we instead take `f` *constant*
    /// (`f = λ_. 7`), whose `resp := λ x y. Eq.refl Nat 7` is honest. Lifting `tr 3` must
    /// reduce to `f 3 = 7`. Checked on the trusted reducer AND NbE (differential).
    #[test]
    fn lift_computation_reduces() {
        let env = trunc_env();
        let u = Level::of_nat(1);
        // f = λ (n : Nat). 7   (constant)
        let f = Term::lam(cn("Nat"), lit(7));
        // resp = λ (x y : Nat). Eq.refl Nat 7   :  Π x y. Eq Nat (f x) (f y) = Eq Nat 7 7
        let resp = Term::lam(
            cn("Nat"),
            Term::lam(
                cn("Nat"),
                Term::apps(Term::cnst(name("Eq.refl"), vec![u.clone()]), [cn("Nat"), lit(7)]),
            ),
        );
        let tr = tr_app(u.clone(), cn("Nat"), lit(3));
        let lift = Term::apps(
            Term::cnst(name(TRUNC_LIFT), vec![u.clone(), u.clone()]),
            [cn("Nat"), cn("Nat"), f, resp, tr],
        );
        // It type-checks at Nat, and reduces to 7.
        let chk = Checker::new(&env);
        chk.check(&mut crate::check::LocalCtx::new(), &lift, &cn("Nat")).unwrap();
        let red = Reducer::new(&env);
        assert!(red.is_def_eq(&lift, &lit(7)), "reducer: lift (tr 3) = 7");
        let nbe = crate::nbe::Nbe::new(&env);
        assert_eq!(nbe.normalize(&lift), lit(7), "nbe: lift (tr 3) = 7");
    }

    /// SOUNDNESS (positive): the path constructor `Trunc.eq` DOES prove `tr 3 = tr 5` in
    /// `Trunc Nat` — the whole point of the truncation is that all elements are equal.
    #[test]
    fn path_proves_all_elements_equal() {
        let env = trunc_env();
        let u = Level::of_nat(1);
        let x = tr_app(u.clone(), cn("Nat"), lit(3));
        let y = tr_app(u.clone(), cn("Nat"), lit(5));
        // Trunc.eq Nat (tr 3) (tr 5) : Eq (Trunc Nat) (tr 3) (tr 5)
        let path = Term::apps(
            Term::cnst(name(TRUNC_EQ), vec![u.clone()]),
            [cn("Nat"), x.clone(), y.clone()],
        );
        let goal = eq_app(Level::of_nat(0), trunc_app(u.clone(), cn("Nat")), x, y);
        let chk = Checker::new(&env);
        chk.check(&mut crate::check::LocalCtx::new(), &path, &goal).unwrap();
    }

    /// SOUNDNESS (adversarial): the path is ONLY propositional — `tr 3` and `tr 5` are NOT
    /// definitionally equal. If they were, conversion would collapse distinct closed
    /// values and canonicity would break. We check the reducer/NbE keep them apart.
    #[test]
    fn path_is_only_propositional() {
        let env = trunc_env();
        let u = Level::of_nat(1);
        let x = tr_app(u.clone(), cn("Nat"), lit(3));
        let y = tr_app(u.clone(), cn("Nat"), lit(5));
        let red = Reducer::new(&env);
        assert!(!red.is_def_eq(&x, &y), "tr 3 and tr 5 must NOT be definitionally equal");
        let nbe = crate::nbe::Nbe::new(&env);
        assert_ne!(nbe.normalize(&x), nbe.normalize(&y), "nbe: tr 3 ≠ tr 5 as normal forms");
    }

    /// SOUNDNESS (adversarial): you CANNOT extract the underlying witness. Lifting the
    /// IDENTITY `f = λn.n : Nat → Nat` out of `Trunc Nat` would recover the representative;
    /// it must be rejected because its `resp` would need `Eq Nat x y` for ALL x,y (false).
    /// We supply a bogus `resp` (`λ x y. Eq.refl Nat x : Eq Nat x x`, wrong codomain) and
    /// require rejection.
    #[test]
    fn cannot_extract_witness() {
        let env = trunc_env();
        let u = Level::of_nat(1);
        let f = Term::lam(cn("Nat"), Term::Var(0)); // identity
        // Bogus resp: λ x y. Eq.refl Nat x  :  Eq Nat x x, but codomain must be Eq Nat x y.
        let resp = Term::lam(
            cn("Nat"),
            Term::lam(
                cn("Nat"),
                Term::apps(Term::cnst(name("Eq.refl"), vec![u.clone()]), [cn("Nat"), Term::Var(1)]),
            ),
        );
        let lift = Term::apps(
            Term::cnst(name(TRUNC_LIFT), vec![u.clone(), u.clone()]),
            [cn("Nat"), cn("Nat"), f, resp],
        );
        let chk = Checker::new(&env);
        assert!(
            chk.infer_closed(&lift).is_err(),
            "extracting the witness via identity lift must be rejected"
        );
    }

    /// SOUNDNESS (adversarial): an unrespectful `f` into a non-proposition is rejected —
    /// no valid `resp` exists. `f = succ` into `Nat` needs `Eq Nat (succ x) (succ y)` for
    /// all x,y; the honest-looking `resp = λ x y. Eq.refl Nat (succ x)` has codomain
    /// `Eq Nat (succ x) (succ x)`, not `Eq Nat (succ x) (succ y)`, so typing fails.
    #[test]
    fn unrespectful_lift_rejected() {
        let env = trunc_env();
        let u = Level::of_nat(1);
        let f = Term::lam(cn("Nat"), Term::app(cn("Nat.succ"), Term::Var(0)));
        let resp = Term::lam(
            cn("Nat"),
            Term::lam(
                cn("Nat"),
                Term::apps(
                    Term::cnst(name("Eq.refl"), vec![u.clone()]),
                    [cn("Nat"), Term::app(cn("Nat.succ"), Term::Var(1))],
                ),
            ),
        );
        let lift = Term::apps(
            Term::cnst(name(TRUNC_LIFT), vec![u.clone(), u.clone()]),
            [cn("Nat"), cn("Nat"), f, resp],
        );
        let chk = Checker::new(&env);
        assert!(chk.infer_closed(&lift).is_err(), "unrespectful lift must be rejected");
    }

    /// SOUNDNESS (adversarial): `Trunc.lift` does NOT fire on the path constructor `eq` —
    /// only on `tr`. A `lift … (Trunc.eq …)`-shaped scrutinee is ill-typed anyway (`eq`
    /// proves an `Eq`, not a `Trunc A`), so it must be rejected, and no spurious reduction
    /// occurs.
    #[test]
    fn lift_does_not_fire_on_path() {
        let env = trunc_env();
        let u = Level::of_nat(1);
        let f = Term::lam(cn("Nat"), lit(7));
        let resp = Term::lam(
            cn("Nat"),
            Term::lam(
                cn("Nat"),
                Term::apps(Term::cnst(name("Eq.refl"), vec![u.clone()]), [cn("Nat"), lit(7)]),
            ),
        );
        // Scrutinee is the PATH `Trunc.eq Nat (tr 3) (tr 5) : Eq …`, not a `Trunc Nat`.
        let path = Term::apps(
            Term::cnst(name(TRUNC_EQ), vec![u.clone()]),
            [cn("Nat"), tr_app(u.clone(), cn("Nat"), lit(3)), tr_app(u.clone(), cn("Nat"), lit(5))],
        );
        let lift = Term::apps(
            Term::cnst(name(TRUNC_LIFT), vec![u.clone(), u.clone()]),
            [cn("Nat"), cn("Nat"), f, resp, path],
        );
        let chk = Checker::new(&env);
        assert!(chk.infer_closed(&lift).is_err(), "lift on a path scrutinee must be rejected");
    }

    /// `Trunc.ind` is well-typed and usable end-to-end: prove a constant `Prop` over the
    /// truncation from the point case.
    #[test]
    fn ind_applies() {
        let env = trunc_env();
        let u = Level::of_nat(1);
        // β := λ t. Eq Nat 0 0   (a constant Prop over the truncation)
        let beta = Term::lam(
            trunc_app(u.clone(), cn("Nat")),
            eq_app(u.clone(), cn("Nat"), lit(0), lit(0)),
        );
        // h := λ a. Eq.refl Nat 0   : Π a, β (tr a)
        let h = Term::lam(
            cn("Nat"),
            Term::apps(Term::cnst(name("Eq.refl"), vec![u.clone()]), [cn("Nat"), lit(0)]),
        );
        let t = tr_app(u.clone(), cn("Nat"), lit(7));
        let ind = Term::apps(
            Term::cnst(name(TRUNC_IND), vec![u.clone()]),
            [cn("Nat"), beta, h, t],
        );
        let goal = eq_app(u.clone(), cn("Nat"), lit(0), lit(0));
        let chk = Checker::new(&env);
        chk.check(&mut crate::check::LocalCtx::new(), &ind, &goal).unwrap();
    }

    /// ADVERSARIAL: `Trunc.eq` cannot be abused to derive `False`. A closed proof of
    /// `False := Π (X:Prop). X` from truncation machinery should be impossible; we sanity
    /// check that `Trunc.eq` requires its arguments to be genuine `Trunc A` elements and
    /// cannot be applied to raw `Nat`s to smuggle out an `Eq Nat 3 5`.
    #[test]
    fn cannot_prove_false() {
        let env = trunc_env();
        let u = Level::of_nat(1);
        // Attempt: Trunc.eq Nat 3 5 — but 3,5 : Nat, not Trunc Nat.  Must be rejected.
        let bogus = Term::apps(
            Term::cnst(name(TRUNC_EQ), vec![u.clone()]),
            [cn("Nat"), lit(3), lit(5)],
        );
        let chk = Checker::new(&env);
        assert!(
            chk.infer_closed(&bogus).is_err(),
            "Trunc.eq must not accept raw Nats — no Eq Nat 3 5 leaks out"
        );
    }

    // ------------------------------------------------------------------
    // Trunc.rec — the isProp-guarded dependent recursor.
    // ------------------------------------------------------------------

    /// `Trunc.rec` is well-typed at every quantifier level (in addition to the blanket
    /// `trunc_constants_wellformed` test already exercising this).
    #[test]
    fn rec_constant_wellformed() {
        let env = trunc_env();
        let chk = Checker::new(&env);
        chk.infer_closed(env.get(TRUNC_REC).unwrap().ty()).unwrap();
    }

    /// COMPUTATION RULE (dependent): `Trunc.rec A C isProp f (Trunc.tr A a) ↦ f a`, for
    /// a motive `C := λ_. Eq Nat 0 0` — a genuine mere proposition (any two of its
    /// proofs are equal by *proof irrelevance*, which is exactly what lets us build a
    /// valid `isProp` with `Eq.refl`). Checked on the trusted reducer AND NbE
    /// (differential), exactly like `lift_computation_reduces`/`rec_computation_reduces_dependent`
    /// in `quotient.rs`.
    #[test]
    fn rec_computation_reduces_dependent() {
        let env = trunc_env();
        let u = Level::of_nat(1);
        let v = Level::of_nat(0);
        let trunc_ty = trunc_app(u.clone(), cn("Nat"));
        // C := λ (_:Trunc Nat). Eq Nat 0 0   (a genuine mere proposition)
        let c = Term::lam(trunc_ty.clone(), eq_app(u.clone(), cn("Nat"), lit(0), lit(0)));
        // isProp := λ t x y. Eq.refl (Eq Nat 0 0) x
        //   : Eq (Eq Nat 0 0) x y  — valid ONLY via proof irrelevance (x ≡ y, both proofs
        //   of the Prop `Eq Nat 0 0`).
        let is_prop = Term::lam(
            trunc_ty.clone(),
            Term::lam(
                eq_app(u.clone(), cn("Nat"), lit(0), lit(0)),
                Term::lam(
                    eq_app(u.clone(), cn("Nat"), lit(0), lit(0)),
                    Term::apps(
                        Term::cnst(name("Eq.refl"), vec![v.clone()]),
                        [eq_app(u.clone(), cn("Nat"), lit(0), lit(0)), Term::Var(1)],
                    ),
                ),
            ),
        );
        // f := λ a. Eq.refl Nat 0   : Π a, C (tr a)
        let f = Term::lam(
            cn("Nat"),
            Term::apps(Term::cnst(name("Eq.refl"), vec![u.clone()]), [cn("Nat"), lit(0)]),
        );
        let tr = tr_app(u.clone(), cn("Nat"), lit(3));
        let rec = Term::apps(
            Term::cnst(name(TRUNC_REC), vec![u.clone(), v.clone()]),
            [cn("Nat"), c, is_prop, f, tr],
        );
        let goal = eq_app(u.clone(), cn("Nat"), lit(0), lit(0));
        let chk = Checker::new(&env);
        chk.check(&mut crate::check::LocalCtx::new(), &rec, &goal).unwrap();
        let expected = Term::apps(Term::cnst(name("Eq.refl"), vec![u.clone()]), [cn("Nat"), lit(0)]);
        let red = Reducer::new(&env);
        assert!(red.is_def_eq(&rec, &expected), "reducer: rec (tr 3) = f 3");
        let nbe = crate::nbe::Nbe::new(&env);
        assert_eq!(nbe.normalize(&rec), nbe.normalize(&expected), "nbe: rec (tr 3) = f 3");
    }

    /// SOUNDNESS (adversarial): you CANNOT extract the underlying witness via `Trunc.rec`
    /// with `C := λ_. Nat`, which is NOT a mere proposition — `isProp` would need to prove
    /// `Eq Nat x y` for ALL naturals x,y, which is false and unprovable. We supply a bogus
    /// `isProp` (`λ t x y. Eq.refl Nat x`, wrong codomain `Eq Nat x x` instead of the
    /// required `Eq Nat x y`) and require rejection. Mirrors `cannot_extract_witness` for
    /// `Trunc.lift`.
    #[test]
    fn rec_cannot_extract_witness() {
        let env = trunc_env();
        let u = Level::of_nat(1);
        let trunc_ty = trunc_app(u.clone(), cn("Nat"));
        // C := λ (_:Trunc Nat). Nat  — NOT a mere proposition.
        let c = Term::lam(trunc_ty.clone(), cn("Nat"));
        // Bogus isProp: λ t x y. Eq.refl Nat x  :  Eq Nat x x, but codomain must be
        // Eq Nat x y (x ≠ y required to hold generally — impossible for `Nat`, and `Nat`
        // is data, not a `Prop`, so proof irrelevance never bails us out here).
        let is_prop = Term::lam(
            trunc_ty,
            Term::lam(
                cn("Nat"),
                Term::lam(
                    cn("Nat"),
                    Term::apps(Term::cnst(name("Eq.refl"), vec![u.clone()]), [cn("Nat"), Term::Var(1)]),
                ),
            ),
        );
        // f := identity : Π a:Nat, C (tr a) = Nat → Nat.
        let f = Term::lam(cn("Nat"), Term::Var(0));
        let rec = Term::apps(
            Term::cnst(name(TRUNC_REC), vec![u.clone(), u.clone()]),
            [cn("Nat"), c, is_prop, f],
        );
        let chk = Checker::new(&env);
        assert!(
            chk.infer_closed(&rec).is_err(),
            "extracting the witness via identity Trunc.rec must be rejected"
        );
    }

    /// SOUNDNESS (adversarial): an `isProp` premise that is simply the wrong type (not a
    /// proof of the required `Π t x y, Eq (C t) x y` at all) is rejected. Mirrors
    /// `unrespectful_lift_rejected`.
    #[test]
    fn rec_unrespectful_rejected() {
        let env = trunc_env();
        let u = Level::of_nat(1);
        let trunc_ty = trunc_app(u.clone(), cn("Nat"));
        let c = Term::lam(trunc_ty.clone(), cn("Nat"));
        // isProp is just `0 : Nat`, nowhere near the required Π-type.
        let is_prop = lit(0);
        let f = Term::lam(cn("Nat"), Term::app(cn("Nat.succ"), Term::Var(0)));
        let rec = Term::apps(
            Term::cnst(name(TRUNC_REC), vec![u.clone(), u.clone()]),
            [cn("Nat"), c, is_prop, f],
        );
        let chk = Checker::new(&env);
        assert!(chk.infer_closed(&rec).is_err(), "ill-typed isProp must be rejected");
    }

    /// SOUNDNESS (adversarial): `Trunc.rec` does NOT fire on the path constructor `eq` —
    /// only on `tr`. A `rec … (Trunc.eq …)`-shaped scrutinee is ill-typed anyway (`eq`
    /// proves an `Eq`, not a `Trunc A`), so it must be rejected, and no spurious
    /// reduction occurs. Mirrors `lift_does_not_fire_on_path`.
    #[test]
    fn rec_does_not_fire_on_path() {
        let env = trunc_env();
        let u = Level::of_nat(1);
        let v = Level::of_nat(0);
        let trunc_ty = trunc_app(u.clone(), cn("Nat"));
        let c = Term::lam(trunc_ty.clone(), eq_app(u.clone(), cn("Nat"), lit(0), lit(0)));
        let is_prop = Term::lam(
            trunc_ty,
            Term::lam(
                eq_app(u.clone(), cn("Nat"), lit(0), lit(0)),
                Term::lam(
                    eq_app(u.clone(), cn("Nat"), lit(0), lit(0)),
                    Term::apps(
                        Term::cnst(name("Eq.refl"), vec![v.clone()]),
                        [eq_app(u.clone(), cn("Nat"), lit(0), lit(0)), Term::Var(1)],
                    ),
                ),
            ),
        );
        let f = Term::lam(
            cn("Nat"),
            Term::apps(Term::cnst(name("Eq.refl"), vec![u.clone()]), [cn("Nat"), lit(0)]),
        );
        // Scrutinee is the PATH `Trunc.eq Nat (tr 3) (tr 5) : Eq …`, not a `Trunc Nat`.
        let path = Term::apps(
            Term::cnst(name(TRUNC_EQ), vec![u.clone()]),
            [cn("Nat"), tr_app(u.clone(), cn("Nat"), lit(3)), tr_app(u.clone(), cn("Nat"), lit(5))],
        );
        let rec = Term::apps(
            Term::cnst(name(TRUNC_REC), vec![u.clone(), v]),
            [cn("Nat"), c, is_prop, f, path],
        );
        let chk = Checker::new(&env);
        assert!(chk.infer_closed(&rec).is_err(), "rec on a path scrutinee must be rejected");
    }

    /// SOUNDNESS (adversarial): `Trunc.rec` cannot be used to derive `False`. Eliminating
    /// into the constant motive `C := λ_. False` (`False := Π (X:Prop). X`) requires an
    /// `f : Π a, False` in the empty context — no such closed term exists — so the partial
    /// application never type-checks; `Trunc.rec` grants no extra proof-strength. Mirrors
    /// `rec_cannot_derive_false` in `quotient.rs`.
    #[test]
    fn rec_cannot_derive_false() {
        let env = trunc_env();
        let u = Level::of_nat(1);
        let zero = Level::of_nat(0);
        let trunc_ty = trunc_app(u.clone(), cn("Nat"));
        let false_ty = Term::pi(Term::prop(), Term::Var(0)); // Π (X:Prop). X
        // C := λ (_:Trunc Nat). False   (False IS a Prop, so `isProp` can be honestly
        // supplied via proof irrelevance — the block is entirely on `f`, below).
        let c = Term::lam(trunc_ty.clone(), false_ty.clone());
        // isProp := λ t x y. Eq.refl False x   : Eq False x y — valid via proof
        // irrelevance (x, y both proofs of the Prop `False`).
        let is_prop = Term::lam(
            trunc_ty,
            Term::lam(
                false_ty.clone(),
                Term::lam(
                    false_ty.clone(),
                    Term::apps(Term::cnst(name("Eq.refl"), vec![zero]), [false_ty, Term::Var(1)]),
                ),
            ),
        );
        // We do NOT have a real `f : Π a, False`; a bogus placeholder (`0 : Nat`) cannot
        // check against `Π a:Nat, C (tr a)` = `Nat → False`.
        let bogus_f = lit(0);
        let rec = Term::apps(
            Term::cnst(name(TRUNC_REC), vec![u.clone(), u]),
            [cn("Nat"), c, is_prop, bogus_f],
        );
        let chk = Checker::new(&env);
        assert!(chk.infer_closed(&rec).is_err(), "must not be able to derive False via Trunc.rec");
    }
}
