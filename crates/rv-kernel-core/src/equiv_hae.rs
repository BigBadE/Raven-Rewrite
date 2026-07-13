//! **Half-adjoint equivalences** (HoTT book Definition 4.2.1): `IsHAE A B` — a
//! bi-invertible map (`f`/`g`/`sec`/`ret`, exactly `crate::equiv::Equiv`'s shape)
//! *plus* the triangle-identity coherence field
//!
//! ```text
//!   tau : Π (a:A). Path (Path B (f (g (f a))) (f a)) (ap f (ret a)) (sec (f a))
//! ```
//!
//! i.e. a *2-dimensional* path (a path between two parallel 1-paths, both of type
//! `Path B (f (g (f a))) (f a)`) witnessing that the two routes from `f a` back to
//! `f (g (f a))` — "apply `f` to the retraction" and "take the section at `f a`" —
//! agree. This is the coherence datum a `Glue`-Kan correction term needs (see
//! `crate::contr`'s module doc, "Why this exists"): `crate::contr::IsContr`/
//! `IsEquiv` supplies the *other* standard coherent-equivalence notion
//! (contractible fibers, Definition 4.4.1); this module supplies the half-adjoint
//! one, per that module's own "Deferred: half-adjoint coherence" section, which
//! this module fulfills.
//!
//! ## What is landed here vs. deferred
//!
//! * **Landed, fully kernel-checked**: the `IsHAE` record shape itself (so its
//!   field types — in particular `tau`'s exact 2-path type — are on record for a
//!   later Glue-Kan consumer to target), its projections, and `idHAE : Π A. IsHAE
//!   A A` — the identity map's half-adjoint coherence datum. Per HoTT book Example
//!   4.2.2's degenerate case, `id`'s `sec`/`ret` are both `refl`-based (`λx. ⟨_⟩x`),
//!   so `ap id (ret a)` and `sec (f a)` **both** reduce (β/ι on the constant `id`,
//!   then interval-β unwinding the two nested `refl`s) to `refl a` *on the nose*;
//!   `tau a := refl (refl a) : Path (Path A a a) (refl a) (refl a)` therefore
//!   checks against the goal type purely by conversion, no `hcomp`/hand-built
//!   square needed. This is exactly the task's own stated "easy" fallback.
//!
//! * **Deferred**: `biInvToHAE : Equiv A B → IsHAE A B` — upgrading an *arbitrary*
//!   bi-invertible `Equiv` (whose `sec`/`ret` carry no coherence between them, see
//!   `crate::equiv`'s module doc) to a half-adjoint one. The standard construction
//!   (HoTT book proof of Theorem 4.2.3, via Lemma 2.4.3's "whiskering" of `sec` by
//!   a homotopy built from `ret`) genuinely needs a 2-dimensional square filled by
//!   `hcomp`/connections — the same obstruction `crate::contr`'s module doc already
//!   flags for its own `Fiber`-contraction: `id`'s `sec`=`ret`=`refl` collapses the
//!   whole construction to a one-liner (as `idHAE` shows), but a *general*
//!   bi-invertible map's `sec`/`ret` do not reduce to anything, so the adjustment
//!   has to be built explicitly rather than fall out of conversion. Not attempted
//!   in this pass, to keep this module's soundness argument airtight (see
//!   `crate::contr`'s doc for the identical judgment call on its own deferred
//!   piece); a future pass can build it with `hcomp`/`crate::kan`'s box-filling
//!   machinery, consuming exactly the `tau` field type declared here as its target.
//!
//! ## Encoding
//!
//! Same "hand-built single-constructor inductive, no primitive `Σ`" discipline as
//! `crate::equiv::Equiv`/`crate::contr::IsContr`/`Fiber` (see `crate::inductive`'s
//! module doc): `IsHAE` is one more field (`tau`) grafted onto `Equiv`'s exact
//! four-field shape, so this module mirrors `crate::equiv` function-for-function
//! (`field_tys` → [`field_tys_hae`], `mk_case_of` → [`mk_case_of_hae`],
//! `declare_equiv`/`_projections`/`_sec_ret` → [`declare_is_hae`]/
//! [`declare_is_hae_projections`]/[`declare_is_hae_tau`]).
//!
//! ## Soundness
//!
//! `IsHAE`/`IsHAE.mk`/`IsHAE.rec` are installed via [`crate::inductive::declare_raw`]
//! — the same trusted, hand-checked path as `Equiv`/`IsContr`/`Fiber` — so they
//! inherit that path's soundness argument verbatim (see `crate::equiv`'s module doc
//! for the fully spelled-out version). `IsHAE.f`/`.g`/`.sec`/`.ret`/`.tau`/`idHAE`
//! add no new trusted machinery: plain `Decl::Def`s built from `IsHAE.rec` and
//! `crate::cubical::refl`/`ap`, both pre-existing and already-sound. This module's
//! `check_hae_types` (types well-formed) and `check_hae_def_values` (`cfg(test)`:
//! each `Decl::Def`'s *value* really has its *declared* type — `Env::insert` does
//! not verify this on its own) mirror `crate::equiv`'s identically-named checks.

use crate::check::Checker;
use crate::cubical::{ap, refl};
use crate::env::{Constructor, Decl, Env, Inductive, RecRule, Recursor};
use crate::inductive::{declare_raw, RawInductive};
use crate::level::Level;
use crate::term::{name, Term};
use std::collections::HashMap;

/// The five field types `(f_ty, g_ty, sec_ty, ret_ty, tau_ty)` of `IsHAE.mk`,
/// valid under a context where `A` is at `Var(1 + extra)`, `B` is at `Var(extra)`,
/// exactly [`crate::equiv::field_tys`]'s convention, extended with a fifth
/// field. `tau_ty`'s domain/codomain reference `f`/`g`/`sec`/`ret` — all *local* to
/// this same telescope, at fixed relative offsets regardless of `extra` — via the
/// `ap`/`Path` combinators, so (per `crate::equiv::field_tys`'s doc) `extra` must be
/// threaded through the index arithmetic directly rather than lifted after the
/// fact.
fn field_tys_hae(extra: usize) -> (Term, Term, Term, Term, Term) {
    let a0 = 1 + extra; // A, right before f is bound
    let b0 = extra; // B, right before f is bound
    let f_ty = Term::arrow(Term::Var(a0), Term::Var(b0)); // A→B
    let (a1, b1) = (a0 + 1, b0 + 1); // ctx [...,A,B,f]
    let g_ty = Term::arrow(Term::Var(b1), Term::Var(a1)); // B→A
    let (a2, b2) = (a1 + 1, b1 + 1); // ctx [...,A,B,f,g]: f=1,g=0
    let (_a3, b3) = (a2 + 1, b2 + 1); // ctx [...,A,B,f,g,b]: f=2,g=1,b=0
    let sec_ty = Term::pi(
        Term::Var(b2), // B
        // Path B (f (g b)) b
        Term::path(Term::Var(b3), Term::app(Term::Var(2), Term::app(Term::Var(1), Term::Var(0))), Term::Var(0)),
    );
    let a4 = a0 + 3; // ctx [...,A,B,f,g,sec]: f=2,g=1,sec=0
    let a5 = a4 + 1; // ctx [...,A,B,f,g,sec,a]: f=3,g=2,sec=1,a=0
    let ret_ty = Term::pi(
        Term::Var(a4), // A
        // Path A (g (f a)) a
        Term::path(Term::Var(a5), Term::app(Term::Var(2), Term::app(Term::Var(3), Term::Var(0))), Term::Var(0)),
    );

    // tau_ty, evaluated pre-'a' under ctx [...,A,B,f,g,sec,ret]: ret=0,sec=1,g=2,
    // f=3, B=extra+4, A=extra+5 (one more binder — `ret` — than `a4`'s ctx).
    let b_pre_a = b0 + 4;
    let a_pre_a = a0 + 4;
    // inside tau's own Pi (bind `a`): everything above shifts by 1, plus `a=0`.
    let f_in = Term::Var(4);
    let g_in = Term::Var(3);
    let sec_in = Term::Var(2);
    let ret_in = Term::Var(1);
    let b_in = Term::Var(b_pre_a + 1);
    let a_var = Term::Var(0);
    let f_a = Term::app(f_in.clone(), a_var.clone());
    let g_f_a = Term::app(g_in, f_a.clone());
    let f_g_f_a = Term::app(f_in.clone(), g_f_a);
    // inner_ty := Path B (f (g (f a))) (f a) — the shared type both sides of `tau`
    // (a Path *in* this type) must inhabit.
    let inner_ty = Term::path(b_in, f_g_f_a, f_a.clone());
    // p := ap f (ret a) : Path B (f (g (f a))) (f a)
    let p = ap(&f_in, &Term::app(ret_in, a_var.clone()));
    // q := sec (f a) : Path B (f (g (f a))) (f a)
    let q = Term::app(sec_in, f_a);
    let tau_body = Term::path(inner_ty, p, q);
    let tau_ty = Term::pi(Term::Var(a_pre_a), tau_body);

    (f_ty, g_ty, sec_ty, ret_ty, tau_ty)
}

/// `λ (f:A→B) (g:B→A) (sec:…) (ret:…) (tau:…). body`, using
/// [`field_tys_hae`]`(0)`'s domains — `body` lives under all five binders
/// (`f=Var(4)`, `g=Var(3)`, `sec=Var(2)`, `ret=Var(1)`, `tau=Var(0)`). Mirrors
/// `crate::equiv::mk_case_of`.
fn mk_case_of_hae(body: Term) -> Term {
    let (f_ty, g_ty, sec_ty, ret_ty, tau_ty) = field_tys_hae(0);
    Term::lam(f_ty, Term::lam(g_ty, Term::lam(sec_ty, Term::lam(ret_ty, Term::lam(tau_ty, body)))))
}

/// Declare `IsHAE.{u} : Π (A B : Sort u), Sort u` with the single constructor
/// `IsHAE.mk` (fields `f g sec ret tau`, see the module doc) and its recursor
/// `IsHAE.rec`. Hand-built, mirroring [`crate::equiv::declare_equiv`] with one
/// extra field.
pub fn declare_is_hae(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let a_sort = || Term::Sort(u());
    let haec = |a: Term, b: Term| Term::apps(Term::cnst(name("IsHAE"), vec![u()]), [a, b]);
    let mk = |args: [Term; 7]| Term::apps(Term::cnst(name("IsHAE.mk"), vec![u()]), args);

    // IsHAE : Π (A B : Sort u), Sort u
    let ind_ty = Term::pi(a_sort(), Term::pi(a_sort(), a_sort()));
    let inductive = Inductive {
        num_levels: 1,
        ty: ind_ty,
        num_params: 2,
        num_indices: 0,
        ctors: vec![name("IsHAE.mk")],
        recursor: name("IsHAE.rec"),
        group: vec![name("IsHAE")],
    };

    // IsHAE.mk : Π (A B:Sort u) (f:A→B) (g:B→A) (sec:…) (ret:…) (tau:…), IsHAE A B
    let (f_ty, g_ty, sec_ty, ret_ty, tau_ty) = field_tys_hae(0);
    let mk_body = haec(Term::Var(6), Term::Var(5)); // ctx [A,B,f,g,sec,ret,tau]
    let mk_ty = Term::pi(
        a_sort(),
        Term::pi(
            a_sort(),
            Term::pi(f_ty, Term::pi(g_ty, Term::pi(sec_ty, Term::pi(ret_ty, Term::pi(tau_ty, mk_body))))),
        ),
    );
    let ctor_mk = Constructor { num_levels: 1, ty: mk_ty, ind: name("IsHAE"), index: 0, num_fields: 5 };

    // IsHAE.rec.{u,v} : Π (A B:Sort u)
    //                     (motive : IsHAE A B → Sort v)
    //                     (mk_case : Π (f:..)(g:..)(sec:..)(ret:..)(tau:..),
    //                                  motive (IsHAE.mk A B f g sec ret tau))
    //                     (e : IsHAE A B), motive e
    let v = Level::param(1);
    let motive_ty = Term::arrow(haec(Term::Var(1), Term::Var(0)), Term::Sort(v)); // ctx [A,B]
    let (f_ty2, g_ty2, sec_ty2, ret_ty2, tau_ty2) = field_tys_hae(1);
    // ctx [A,B,motive,f,g,sec,ret,tau]: motive (IsHAE.mk A B f g sec ret tau)
    let mk_result = Term::app(
        Term::Var(5),
        mk([Term::Var(7), Term::Var(6), Term::Var(4), Term::Var(3), Term::Var(2), Term::Var(1), Term::Var(0)]),
    );
    let mk_case_ty = Term::pi(
        f_ty2,
        Term::pi(g_ty2, Term::pi(sec_ty2, Term::pi(ret_ty2, Term::pi(tau_ty2, mk_result)))),
    );
    let e_ty = haec(Term::Var(3), Term::Var(2)); // ctx [A,B,motive,mk_case]
    let result = Term::app(Term::Var(2), Term::Var(0)); // ctx [A,B,motive,mk_case,e]: motive e
    let rec_ty = Term::pi(
        a_sort(),
        Term::pi(a_sort(), Term::pi(motive_ty, Term::pi(mk_case_ty, Term::pi(e_ty, result)))),
    );

    // ι-rule: applied to [A,B,motive,mk_case,f,g,sec,ret,tau] ↦ mk_case f g sec ret tau.
    let rule_mk = RecRule {
        ctor: name("IsHAE.mk"),
        num_fields: 5,
        rhs: {
            let mut t = Term::apps(
                Term::Var(5),
                [Term::Var(4), Term::Var(3), Term::Var(2), Term::Var(1), Term::Var(0)],
            );
            for _ in 0..9 {
                t = Term::lam(Term::prop(), t);
            }
            t
        },
    };
    let mut rules = HashMap::new();
    rules.insert(name("IsHAE.mk"), rule_mk);

    let recursor = Recursor {
        num_levels: 2,
        ty: rec_ty,
        ind: name("IsHAE"),
        num_params: 2,
        num_motives: 1,
        num_indices: 0,
        num_minors: 1,
        rules,
    };

    declare_raw(
        env,
        RawInductive {
            ind_name: name("IsHAE"),
            inductive,
            ctors: vec![(name("IsHAE.mk"), ctor_mk)],
            rec_name: name("IsHAE.rec"),
            recursor,
        },
    )?;

    declare_is_hae_projections(env)?;
    declare_id_hae(env)?;
    Ok(())
}

/// `IsHAE.f`/`IsHAE.g`, each a `Decl::Def` built via `IsHAE.rec` with a
/// non-dependent motive picking out the corresponding constructor field — the
/// standard "record projection through the recursor" encoding, mirroring
/// `crate::equiv::declare_equiv_projections`.
fn declare_is_hae_projections(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let a_sort = || Term::Sort(u());
    let hae_ty = |a: Term, b: Term| Term::apps(Term::cnst(name("IsHAE"), vec![u()]), [a, b]);
    let hae_rec = |motive: Term, mk_case: Term, e: Term, a: Term, b: Term| {
        Term::apps(Term::cnst(name("IsHAE.rec"), vec![u(), u()]), [a, b, motive, mk_case, e])
    };

    // IsHAE.f : Π (A B : Sort u) (e : IsHAE A B), A → B
    {
        let motive = Term::lam(hae_ty(Term::Var(1), Term::Var(0)), Term::arrow(Term::Var(2), Term::Var(1)));
        let mk_case = mk_case_of_hae(Term::Var(4)); // ctx [A,B]: f
        let e = Term::Var(0); // ctx [A,B,e]
        let body = hae_rec(motive.lift(1, 0), mk_case.lift(1, 0), e, Term::Var(2), Term::Var(1));
        let value = Term::lam(a_sort(), Term::lam(a_sort(), Term::lam(hae_ty(Term::Var(1), Term::Var(0)), body)));
        let ty = Term::pi(
            a_sort(),
            Term::pi(a_sort(), Term::pi(hae_ty(Term::Var(1), Term::Var(0)), Term::arrow(Term::Var(2), Term::Var(1)))),
        );
        env.insert(name("IsHAE.f"), Decl::Def { num_levels: 1, ty, value })?;
    }
    // IsHAE.g : Π (A B : Sort u) (e : IsHAE A B), B → A
    {
        let motive = Term::lam(hae_ty(Term::Var(1), Term::Var(0)), Term::arrow(Term::Var(1), Term::Var(2)));
        let mk_case = mk_case_of_hae(Term::Var(3)); // ctx [A,B]: g
        let e = Term::Var(0);
        let body = hae_rec(motive.lift(1, 0), mk_case.lift(1, 0), e, Term::Var(2), Term::Var(1));
        let value = Term::lam(a_sort(), Term::lam(a_sort(), Term::lam(hae_ty(Term::Var(1), Term::Var(0)), body)));
        let ty = Term::pi(
            a_sort(),
            Term::pi(a_sort(), Term::pi(hae_ty(Term::Var(1), Term::Var(0)), Term::arrow(Term::Var(1), Term::Var(2)))),
        );
        env.insert(name("IsHAE.g"), Decl::Def { num_levels: 1, ty, value })?;
    }
    declare_is_hae_sec_ret(env)?;
    declare_is_hae_tau(env)?;
    Ok(())
}

/// `IsHAE.sec`/`IsHAE.ret`, built via `IsHAE.rec` with an `e`-*dependent* motive
/// stated in terms of the already-installed `IsHAE.f`/`IsHAE.g` — exactly
/// `crate::equiv::declare_equiv_sec_ret`, one field-count higher.
fn declare_is_hae_sec_ret(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let a_sort = || Term::Sort(u());
    let hae_ty = |a: Term, b: Term| Term::apps(Term::cnst(name("IsHAE"), vec![u()]), [a, b]);
    let hae_rec = |motive: Term, mk_case: Term, e: Term, a: Term, b: Term| {
        Term::apps(Term::cnst(name("IsHAE.rec"), vec![u(), u()]), [a, b, motive, mk_case, e])
    };
    let hf = |a: Term, b: Term, e: Term| Term::apps(Term::cnst(name("IsHAE.f"), vec![u()]), [a, b, e]);
    let hg = |a: Term, b: Term, e: Term| Term::apps(Term::cnst(name("IsHAE.g"), vec![u()]), [a, b, e]);

    // IsHAE.sec : Π (A B : Sort u) (e : IsHAE A B) (b : B),
    //               Path B (IsHAE.f A B e (IsHAE.g A B e b)) b
    {
        let stmt = Term::pi(
            Term::Var(1), // B, ctx [A,B,e]
            // ctx [A,B,e,b]: A=3,B=2,e=1,b=0
            Term::path(
                Term::Var(2),
                Term::app(hf(Term::Var(3), Term::Var(2), Term::Var(1)), Term::app(hg(Term::Var(3), Term::Var(2), Term::Var(1)), Term::Var(0))),
                Term::Var(0),
            ),
        );
        let motive = Term::lam(hae_ty(Term::Var(1), Term::Var(0)), stmt.clone());
        let mk_case = mk_case_of_hae(Term::Var(2)); // ctx [A,B]: sec
        let e = Term::Var(0);
        let body = hae_rec(motive.lift(1, 0), mk_case.lift(1, 0), e, Term::Var(2), Term::Var(1));
        let value = Term::lam(a_sort(), Term::lam(a_sort(), Term::lam(hae_ty(Term::Var(1), Term::Var(0)), body)));
        let ty = Term::pi(a_sort(), Term::pi(a_sort(), Term::pi(hae_ty(Term::Var(1), Term::Var(0)), stmt)));
        env.insert(name("IsHAE.sec"), Decl::Def { num_levels: 1, ty, value })?;
    }
    // IsHAE.ret : Π (A B : Sort u) (e : IsHAE A B) (a : A),
    //               Path A (IsHAE.g A B e (IsHAE.f A B e a)) a
    {
        let stmt = Term::pi(
            Term::Var(2), // A, ctx [A,B,e]
            // ctx [A,B,e,a]: A=3,B=2,e=1,a=0
            Term::path(
                Term::Var(3),
                Term::app(hg(Term::Var(3), Term::Var(2), Term::Var(1)), Term::app(hf(Term::Var(3), Term::Var(2), Term::Var(1)), Term::Var(0))),
                Term::Var(0),
            ),
        );
        let motive = Term::lam(hae_ty(Term::Var(1), Term::Var(0)), stmt.clone());
        let mk_case = mk_case_of_hae(Term::Var(1)); // ctx [A,B]: ret
        let e = Term::Var(0);
        let body = hae_rec(motive.lift(1, 0), mk_case.lift(1, 0), e, Term::Var(2), Term::Var(1));
        let value = Term::lam(a_sort(), Term::lam(a_sort(), Term::lam(hae_ty(Term::Var(1), Term::Var(0)), body)));
        let ty = Term::pi(a_sort(), Term::pi(a_sort(), Term::pi(hae_ty(Term::Var(1), Term::Var(0)), stmt)));
        env.insert(name("IsHAE.ret"), Decl::Def { num_levels: 1, ty, value })?;
    }
    Ok(())
}

/// `IsHAE.tau : Π (A B:Sort u) (e:IsHAE A B) (a:A), Path (Path B (f (g (f a))) (f
/// a)) (ap f (ret a)) (sec (f a))` — the triangle-identity projection, `e`-
/// dependent (like `sec`/`ret`) but *2-dimensional*: its statement is a `Path`
/// whose own type is itself a `Path B _ _`, not a `Path` in `A`/`B` directly. `f`,
/// `g`, `sec`, `ret` here are `IsHAE.f/.g/.sec/.ret A B e` (the already-installed
/// projections of the abstract `e`), matching this module's `field_tys_hae`'s
/// `tau_ty` shape up to unfolding those projections on the literal constructor —
/// checked concretely by `check_hae_def_values`/`hae_types_wellformed` below.
fn declare_is_hae_tau(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let a_sort = || Term::Sort(u());
    let hae_ty = |a: Term, b: Term| Term::apps(Term::cnst(name("IsHAE"), vec![u()]), [a, b]);
    let hae_rec = |motive: Term, mk_case: Term, e: Term, a: Term, b: Term| {
        Term::apps(Term::cnst(name("IsHAE.rec"), vec![u(), u()]), [a, b, motive, mk_case, e])
    };
    let hf = |a: Term, b: Term, e: Term| Term::apps(Term::cnst(name("IsHAE.f"), vec![u()]), [a, b, e]);
    let hg = |a: Term, b: Term, e: Term| Term::apps(Term::cnst(name("IsHAE.g"), vec![u()]), [a, b, e]);
    let hsec = |a: Term, b: Term, e: Term| Term::apps(Term::cnst(name("IsHAE.sec"), vec![u()]), [a, b, e]);
    let hret = |a: Term, b: Term, e: Term| Term::apps(Term::cnst(name("IsHAE.ret"), vec![u()]), [a, b, e]);

    // stmt, ctx [A,B,e] (A=2,B=1,e=0): Π (a:A). Path (Path B ..) (ap f (ret a)) (sec (f a))
    let stmt = {
        // ctx [A,B,e,a]: A=3,B=2,e=1,a=0
        let f_call = hf(Term::Var(3), Term::Var(2), Term::Var(1));
        let g_call = hg(Term::Var(3), Term::Var(2), Term::Var(1));
        let sec_call = hsec(Term::Var(3), Term::Var(2), Term::Var(1));
        let ret_call = hret(Term::Var(3), Term::Var(2), Term::Var(1));
        let f_a = Term::app(f_call.clone(), Term::Var(0));
        let g_f_a = Term::app(g_call, f_a.clone());
        let f_g_f_a = Term::app(f_call.clone(), g_f_a);
        let inner_ty = Term::path(Term::Var(2), f_g_f_a, f_a.clone());
        let p = ap(&f_call, &Term::app(ret_call, Term::Var(0)));
        let q = Term::app(sec_call, f_a);
        let tau_body = Term::path(inner_ty, p, q);
        Term::pi(Term::Var(2), tau_body) // A, ctx [A,B,e]
    };
    let motive = Term::lam(hae_ty(Term::Var(1), Term::Var(0)), stmt.clone()); // ctx [A,B]
    let mk_case = mk_case_of_hae(Term::Var(0)); // ctx [A,B]: tau
    let e = Term::Var(0);
    let body = hae_rec(motive.lift(1, 0), mk_case.lift(1, 0), e, Term::Var(2), Term::Var(1));
    let value = Term::lam(a_sort(), Term::lam(a_sort(), Term::lam(hae_ty(Term::Var(1), Term::Var(0)), body)));
    let ty = Term::pi(a_sort(), Term::pi(a_sort(), Term::pi(hae_ty(Term::Var(1), Term::Var(0)), stmt)));
    env.insert(name("IsHAE.tau"), Decl::Def { num_levels: 1, ty, value })
}

/// `idHAE.{u} : Π (A : Sort u), IsHAE A A` — the identity map, half-adjoint. `sec`/
/// `ret` are both `λx. ⟨_⟩x` (exactly `crate::equiv::declare_id_equiv`'s
/// `refl_fn`); `tau a := refl (refl a)` — see the module doc's "Landed" bullet for
/// why this checks purely by conversion (no `hcomp` needed): with `f = g = id`,
/// `ap f (ret a)` and `sec (f a)` both reduce (β on `id`, then interval-β
/// unwinding two nested `refl`s) to `refl a` on the nose, so the goal 2-path type
/// collapses to `Path (Path A a a) (refl a) (refl a)`, which `refl (refl a)`
/// inhabits definitionally.
fn declare_id_hae(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let a_sort = || Term::Sort(u());
    let hae_ty = |a: Term, b: Term| Term::apps(Term::cnst(name("IsHAE"), vec![u()]), [a, b]);
    let mk = |args: [Term; 7]| Term::apps(Term::cnst(name("IsHAE.mk"), vec![u()]), args);

    // ctx [A]: id = λx:A. x
    let id_fn = Term::lam(Term::Var(0), Term::Var(0));
    // ctx [A]: sec/ret = λx:A. ⟨_⟩ x (see `crate::equiv::declare_id_equiv`'s doc for
    // the `Var(1)` explanation: inside the `PLam`, a fresh interval binder is
    // pushed, so `x` is one level further out than the fresh binder's own `Var(0)`).
    let refl_fn = Term::lam(Term::Var(0), Term::plam(Term::Var(1)));
    // ctx [A]: tau = λ(a:A). refl (refl a)
    let tau_fn = Term::lam(Term::Var(0), refl(&refl(&Term::Var(0))));
    let value = Term::lam(
        a_sort(),
        mk([Term::Var(0), Term::Var(0), id_fn.clone(), id_fn, refl_fn.clone(), refl_fn, tau_fn]),
    );
    let ty = Term::pi(a_sort(), hae_ty(Term::Var(0), Term::Var(0)));
    env.insert(name("idHAE"), Decl::Def { num_levels: 1, ty, value })
}

/// Type-check every `IsHAE`-related declaration's stated *type* (well-formedness
/// sanity pass, mirroring `crate::equiv::check_equiv_types`).
pub fn check_hae_types(env: &Env) -> Result<(), String> {
    let chk = Checker::new(env);
    for n in [
        "IsHAE", "IsHAE.mk", "IsHAE.rec", "IsHAE.f", "IsHAE.g", "IsHAE.sec", "IsHAE.ret", "IsHAE.tau", "idHAE",
    ] {
        let decl = env.get(n).ok_or_else(|| format!("missing '{n}'"))?;
        let mut ctx = crate::check::LocalCtx::new();
        chk.infer(&mut ctx, decl.ty()).map_err(|e| format!("'{n}': {e}"))?;
    }
    Ok(())
}

/// Check that every `Decl::Def` this module installs has a *value* matching its
/// *declared type* (`Env::insert` does not verify this on its own — see the module
/// doc's `Soundness` section). `cfg(test)`-only, mirroring
/// `crate::equiv::check_equiv_def_values`.
#[cfg(test)]
fn check_hae_def_values(env: &Env) -> Result<(), String> {
    let chk = Checker::new(env);
    for n in ["IsHAE.f", "IsHAE.g", "IsHAE.sec", "IsHAE.ret", "IsHAE.tau", "idHAE"] {
        let Some(Decl::Def { ty, value, .. }) = env.get(n) else {
            return Err(format!("'{n}' missing or not a Def"));
        };
        let mut ctx = crate::check::LocalCtx::new();
        chk.check(&mut ctx, value, ty).map_err(|e| format!("'{n}': value does not match its type: {e}"))?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inductive::declare_nat;
    use crate::reduce::Reducer;

    fn hae_env() -> Env {
        let mut env = Env::new();
        declare_is_hae(&mut env).unwrap();
        env
    }

    #[test]
    fn hae_types_wellformed() {
        let env = hae_env();
        check_hae_types(&env).unwrap();
    }

    /// The soundness-critical check `check_hae_types` alone does *not* give: every
    /// installed `Decl::Def`'s *value* really has its *declared* type — in
    /// particular, that `idHAE`'s `tau` field really does check at the
    /// **2-dimensional** `tau` type (a `Path` between two `Path`s), not something
    /// weaker.
    #[test]
    fn hae_def_values_match_their_types() {
        let env = hae_env();
        check_hae_def_values(&env).unwrap();
    }

    #[test]
    fn id_hae_applies_to_nat() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_is_hae(&mut env).unwrap();
        let chk = Checker::new(&env);
        let nat = Term::cnst(name("Nat"), vec![]);
        let id_nat = Term::app(Term::cnst(name("idHAE"), vec![Level::of_nat(1)]), nat.clone());
        let ty = chk.infer_closed(&id_nat).expect("idHAE Nat should type-check");
        let expected = Term::apps(Term::cnst(name("IsHAE"), vec![Level::of_nat(1)]), [nat.clone(), nat]);
        let r = Reducer::new(&env);
        assert!(r.is_def_eq(&ty, &expected), "idHAE Nat has type {ty:?}, expected {expected:?}");
    }

    /// `IsHAE.f (idHAE A) ≡ λx. x` (ι/β) — the projection genuinely computes.
    #[test]
    fn id_hae_f_reduces_to_identity() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_is_hae(&mut env).unwrap();
        let r = Reducer::new(&env);
        let nat = Term::cnst(name("Nat"), vec![]);
        let id_hae_nat = Term::app(Term::cnst(name("idHAE"), vec![Level::of_nat(1)]), nat.clone());
        let f_of_id = Term::apps(Term::cnst(name("IsHAE.f"), vec![Level::of_nat(1)]), [nat.clone(), nat.clone(), id_hae_nat]);
        let id_fn = Term::lam(nat, Term::Var(0));
        assert!(r.is_def_eq(&f_of_id, &id_fn));
    }

    /// `IsHAE.tau`'s *inferred* type, instantiated at `Nat`/`idHAE`, is exactly the
    /// stated 2-path shape `Π a. Path (Path Nat _ _) _ _` — i.e. `tau`'s codomain
    /// is a `Path` whose *own* type argument is itself a `Path`, not a plain `Path
    /// Nat _ _`. Guards against the failure mode the task calls out explicitly: a
    /// wrong (too-shallow) 2-path type silently accepted.
    #[test]
    fn tau_type_is_genuinely_two_dimensional() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_is_hae(&mut env).unwrap();
        let decl = env.get("IsHAE.tau").unwrap();
        // Peel the four `Pi`s (A, B, e, a) to reach the codomain.
        let mut t = decl.ty().clone();
        for _ in 0..4 {
            match t {
                Term::Pi(_, _, cod) => t = (*cod).clone(),
                other => panic!("expected Pi, got {other:?}"),
            }
        }
        match &t {
            // `Term::path`'s family is the (interval-constant) type itself, lifted
            // past the fresh interval binder — so checking the family directly
            // (rather than looking under a `PLam`) is the right shape here. It must
            // itself be a `PathP`/`Path` (not a bare `Var`/application into `B`),
            // confirming `tau`'s codomain is genuinely a *path between paths*.
            Term::PathP(family, _, _) => assert!(
                matches!(family.as_ref(), Term::PathP(..)),
                "tau's Path-type argument is not itself a Path: {family:?}"
            ),
            other => panic!("expected tau's codomain to be a PathP/Path, got {other:?}"),
        }
    }

    /// Adversarial: a bogus term (a bare `λx.x`) must not check against `IsHAE Nat
    /// Nat`.
    #[test]
    fn ill_formed_term_is_not_an_hae() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_is_hae(&mut env).unwrap();
        let chk = Checker::new(&env);
        let nat = Term::cnst(name("Nat"), vec![]);
        let bogus = Term::lam(nat.clone(), Term::Var(0));
        let expected = Term::apps(Term::cnst(name("IsHAE"), vec![Level::of_nat(1)]), [nat.clone(), nat]);
        let mut ctx = crate::check::LocalCtx::new();
        assert!(chk.check(&mut ctx, &bogus, &expected).is_err());
    }

    /// Adversarial: `idHAE`'s `tau` proof must not check at a *different* (wrong)
    /// pairing of endpoints — e.g. swapping which side `ap f (ret a)`/`sec (f a)`
    /// land on would be a distinct, non-defeq goal in general; here we sanity-check
    /// that a totally unrelated term (`refl (refl a)` is fine, but a non-reflexive
    /// 1-path standing in for `tau`) is rejected.
    #[test]
    fn wrong_term_does_not_satisfy_tau_type() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_is_hae(&mut env).unwrap();
        let chk = Checker::new(&env);
        let nat = Term::cnst(name("Nat"), vec![]);
        let id_hae_nat = Term::app(Term::cnst(name("idHAE"), vec![Level::of_nat(1)]), nat.clone());
        // The real tau type at a fixed `a`.
        let tau_ty_fn = Term::apps(
            Term::cnst(name("IsHAE.tau"), vec![Level::of_nat(1)]),
            [nat.clone(), nat.clone(), id_hae_nat],
        );
        let a0 = Term::cnst(name("Nat.zero"), vec![]);
        let goal = crate::check::Checker::new(&env)
            .infer_closed(&Term::app(tau_ty_fn.clone(), a0.clone()))
            .unwrap_or(Term::app(tau_ty_fn, a0.clone()));
        // A bogus 1-dimensional term (just `refl a0`, one dimension too shallow)
        // must not check against the genuinely 2-dimensional goal.
        let bogus = refl(&a0);
        let mut ctx = crate::check::LocalCtx::new();
        assert!(chk.check(&mut ctx, &bogus, &goal).is_err());
    }
}
