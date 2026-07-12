//! **Step 1 of univalence**: the equivalence type `Equiv A B` (`A ≃ B`) and the
//! identity equivalence `idEquiv`.
//!
//! ## Why bi-invertible, not half-adjoint
//!
//! This kernel has no `Σ`-type (see `crate::inductive`'s module doc — structured
//! data goes through inductives/records instead), so `Equiv A B` is a
//! **hand-built single-constructor inductive** (exactly the `declare_nat`/
//! `declare_eq` pattern in [`crate::inductive`]), with fields
//!
//! ```text
//!   f   : A → B
//!   g   : B → A
//!   sec : Π (b : B). Path B (f (g b)) b
//!   ret : Π (a : A). Path A (g (f a)) a
//! ```
//!
//! i.e. a **bi-invertible map**: `f` has both a section and a retraction, but they
//! need not be the *same* function and carry no coherence between `sec`/`ret`. This
//! is strictly weaker than the usual "half-adjoint equivalence" (which additionally
//! requires `sec`/`ret` to cohere and is what makes `isEquiv` a genuine proposition),
//! but per CCHM (Cohen–Coquand–Huber–Mörtberg, *Cubical Type Theory*, §5) it is
//! exactly what `Glue`'s `⊤`-strictness needs: `glue`/`unglue` only ever *use* `f`
//! and `g` computationally, and `sec`/`ret` only for the propositional coherence
//! that `unglue ∘ glue ≡ id` — no `isContr`-style contractibility of the fiber is
//! needed for that. Upgrading to half-adjoint (needed for `ua`/full univalence, not
//! this pass — see `crate::term::Term::Glue`'s doc) is explicitly deferred.
//!
//! ## Soundness
//!
//! `Equiv`/`Equiv.mk`/`Equiv.rec` are installed via [`crate::inductive::declare_raw`]
//! — the same trusted, hand-checked path as `Nat`/`Eq` — so they inherit that path's
//! soundness argument verbatim: the recursor's ι-rule computes exactly the term the
//! recursor's own declared return type already promises, checked concretely by this
//! module's tests (`check_equiv_types` below type-checks every declared *type*, and
//! `id_equiv_*` tests separately check that each `Decl::Def`'s *value* actually has
//! its stated type — `Env::insert` itself does not verify `value : ty`, so that
//! second check is this module's own responsibility, not inherited for free). No new
//! reduction or typing rule is added to the trusted core beyond the ordinary
//! inductive/recursor machinery already proven sound in `crate::inductive`/
//! `crate::check`/`crate::reduce`.
//!
//! `idEquiv` and the field projections (`Equiv.f`/`Equiv.g`/`Equiv.sec`/`Equiv.ret`)
//! are plain `Decl::Def`s built from `Equiv.rec` with a (possibly `e`-dependent)
//! motive — the standard "record projection via recursor" encoding — so they too add
//! no new trusted machinery.

use crate::check::Checker;
use crate::env::{Constructor, Decl, Env, Inductive, RecRule, Recursor};
use crate::inductive::{declare_raw, RawInductive};
use crate::level::Level;
use crate::term::{name, Term};
use std::collections::HashMap;

/// The four field types `(f_ty, g_ty, sec_ty, ret_ty)` of `Equiv.mk`, valid under a
/// context where `A` is at `Var(1 + extra)`, `B` is at `Var(extra)`, and nothing
/// *else* sits between `B` and where `f` is about to be bound (`extra` counts only
/// binders **before** `A`/`B` — e.g. `extra = 1` for `Equiv.rec`'s own
/// `mk_case_ty`, which has one extra `motive` binder between `B` and `f`). This
/// exact four-field shape recurs repeatedly in this module (the constructor's own
/// telescope at `extra = 0`, `Equiv.rec`'s `mk_case_ty` at `extra = 1`, and
/// `Equiv.f`/`Equiv.g`/`Equiv.sec`/`Equiv.ret`'s own `mk_case` argument via
/// [`mk_case_of`]), so it is factored out once here rather than re-derived by hand
/// each time — the single most error-prone part of hand-building a multi-field
/// record (see this module's `Soundness` doc: an index slip here would make the
/// affected declaration fail to type-check, caught immediately by this module's
/// tests, not silently accepted, since [`Checker::check`]/`is_def_eq` are exact).
///
/// **Not** implemented as `field_tys(0).lift(extra, 0)` on the four pieces
/// individually: `sec_ty`/`ret_ty` reference `f`/`g`, which are *local* to this
/// same telescope (bound fresh, at a fixed relative offset, regardless of
/// `extra`) — lifting each piece in isolation with `cutoff = 0` would incorrectly
/// shift those local references too, since outside the enclosing `f`/`g` binders
/// (present in the real telescope, absent when a piece is extracted standalone)
/// nothing marks them as "already bound". `extra` is instead threaded through the
/// index arithmetic directly, shifting only the genuinely-outer `A`/`B`.
fn field_tys(extra: usize) -> (Term, Term, Term, Term) {
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
    (f_ty, g_ty, sec_ty, ret_ty)
}

/// `λ (f:A→B) (g:B→A) (sec:…) (ret:…). body`, using [`field_tys`]`(0)`'s
/// domains — `body` lives under all four binders (`f=Var(3)`, `g=Var(2)`,
/// `sec=Var(1)`, `ret=Var(0)`). Unlike [`field_tys`]'s individual pieces, the
/// *whole* result here is safe to `.lift(k, 0)` as one nested term: `Term::lift`
/// bumps its cutoff at each `Lam` it descends through, so a lift of the complete
/// `mk_case_of(..)` value correctly shifts only the outer `A`/`B` references while
/// leaving the internal `f`/`g`/`sec`/`ret` back-references (which sit *below* the
/// bumped cutoff at every point they occur) untouched — the opposite of
/// [`field_tys`]'s doc, which is precisely why that one takes `extra` as a
/// parameter instead of being lifted after the fact.
fn mk_case_of(body: Term) -> Term {
    let (f_ty, g_ty, sec_ty, ret_ty) = field_tys(0);
    Term::lam(f_ty, Term::lam(g_ty, Term::lam(sec_ty, Term::lam(ret_ty, body))))
}

/// Declare `Equiv.{u} : Π (A B : Sort u), Sort u` with the single constructor
/// `Equiv.mk` (fields `f g sec ret`, see the module doc) and its recursor
/// `Equiv.rec`. Hand-built, mirroring [`crate::inductive::declare_eq`].
pub fn declare_equiv(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let a_sort = || Term::Sort(u());
    let equivc = |a: Term, b: Term| Term::apps(Term::cnst(name("Equiv"), vec![u()]), [a, b]);
    let mk = |args: [Term; 6]| Term::apps(Term::cnst(name("Equiv.mk"), vec![u()]), args);

    // Equiv : Π (A B : Sort u), Sort u
    let ind_ty = Term::pi(a_sort(), Term::pi(a_sort(), a_sort()));
    let inductive = Inductive {
        num_levels: 1,
        ty: ind_ty,
        num_params: 2,
        num_indices: 0,
        ctors: vec![name("Equiv.mk")],
        recursor: name("Equiv.rec"),
        group: vec![name("Equiv")],
    };

    // Equiv.mk : Π (A B : Sort u) (f : A→B) (g : B→A)
    //              (sec : Π (b:B). Path B (f (g b)) b)
    //              (ret : Π (a:A). Path A (g (f a)) a), Equiv A B
    let (f_ty, g_ty, sec_ty, ret_ty) = field_tys(0);
    let mk_body = equivc(Term::Var(5), Term::Var(4)); // ctx [A,B,f,g,sec,ret]
    let mk_ty = Term::pi(
        a_sort(),
        Term::pi(a_sort(), Term::pi(f_ty, Term::pi(g_ty, Term::pi(sec_ty, Term::pi(ret_ty, mk_body))))),
    );
    let ctor_mk = Constructor { num_levels: 1, ty: mk_ty, ind: name("Equiv"), index: 0, num_fields: 4 };

    // Equiv.rec.{u,v} : Π (A B : Sort u)
    //                     (motive : Equiv A B → Sort v)
    //                     (mk_case : Π (f:A→B)(g:B→A)(sec:…)(ret:…),
    //                                  motive (Equiv.mk A B f g sec ret))
    //                     (e : Equiv A B), motive e
    let v = Level::param(1);
    let motive_ty = Term::arrow(equivc(Term::Var(1), Term::Var(0)), Term::Sort(v)); // ctx [A,B]
    // `mk_case_ty`'s field domains sit under ctx [A,B,motive] — one extra binder
    // (`motive`) between `B` and `f` — so `extra = 1` (see `field_tys`'s doc for
    // why this is *not* `field_tys(0)` lifted after the fact).
    let (f_ty2, g_ty2, sec_ty2, ret_ty2) = field_tys(1);
    // ctx [A,B,motive,f,g,sec,ret]: motive (Equiv.mk A B f g sec ret)
    let mk_result = Term::app(
        Term::Var(4),
        mk([Term::Var(6), Term::Var(5), Term::Var(3), Term::Var(2), Term::Var(1), Term::Var(0)]),
    );
    let mk_case_ty = Term::pi(
        f_ty2,
        Term::pi(g_ty2, Term::pi(sec_ty2, Term::pi(ret_ty2, mk_result))),
    );
    let e_ty = equivc(Term::Var(3), Term::Var(2)); // ctx [A,B,motive,mk_case]
    let result = Term::app(Term::Var(2), Term::Var(0)); // ctx [A,B,motive,mk_case,e]: motive e
    let rec_ty = Term::pi(
        a_sort(),
        Term::pi(a_sort(), Term::pi(motive_ty, Term::pi(mk_case_ty, Term::pi(e_ty, result)))),
    );

    // ι-rule: applied to [A,B,motive,mk_case,f,g,sec,ret] ↦ mk_case f g sec ret.
    let rule_mk = RecRule {
        ctor: name("Equiv.mk"),
        num_fields: 4,
        rhs: {
            let mut t = Term::apps(Term::Var(4), [Term::Var(3), Term::Var(2), Term::Var(1), Term::Var(0)]);
            for _ in 0..8 {
                t = Term::lam(Term::prop(), t);
            }
            t
        },
    };
    let mut rules = HashMap::new();
    rules.insert(name("Equiv.mk"), rule_mk);

    let recursor = Recursor {
        num_levels: 2,
        ty: rec_ty,
        ind: name("Equiv"),
        num_params: 2,
        num_motives: 1,
        num_indices: 0,
        num_minors: 1,
        rules,
    };

    declare_raw(
        env,
        RawInductive {
            ind_name: name("Equiv"),
            inductive,
            ctors: vec![(name("Equiv.mk"), ctor_mk)],
            rec_name: name("Equiv.rec"),
            recursor,
        },
    )?;

    declare_equiv_projections(env)?;
    declare_id_equiv(env)?;
    Ok(())
}

/// `Equiv.f`/`Equiv.g`, each a `Decl::Def` built via `Equiv.rec` with a
/// non-dependent motive (`λ_:Equiv A B. A→B` / `B→A`) and `mk_case` picking out the
/// corresponding constructor field — the standard "record projection through the
/// recursor" encoding.
fn declare_equiv_projections(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let a_sort = || Term::Sort(u());
    let equiv_ty = |a: Term, b: Term| Term::apps(Term::cnst(name("Equiv"), vec![u()]), [a, b]);
    let equiv_rec = |motive: Term, mk_case: Term, e: Term, a: Term, b: Term| {
        Term::apps(Term::cnst(name("Equiv.rec"), vec![u(), u()]), [a, b, motive, mk_case, e])
    };

    // Equiv.f : Π (A B : Sort u) (e : Equiv A B), A → B
    {
        // ctx [A,B]: motive = λ_:Equiv A B. A→B
        let motive = Term::lam(equiv_ty(Term::Var(1), Term::Var(0)), Term::arrow(Term::Var(2), Term::Var(1)));
        // ctx [A,B]: mk_case = λf λg λsec λret. f
        let mk_case = mk_case_of(Term::Var(3));
        // both `motive`/`mk_case` are built under ctx [A,B]; placed under ctx
        // [A,B,e] here (one extra binder), so lift by 1 (see `field_tys0`'s doc).
        let e = Term::Var(0); // ctx [A,B,e]
        let body = equiv_rec(motive.lift(1, 0), mk_case.lift(1, 0), e, Term::Var(2), Term::Var(1));
        let value = Term::lam(a_sort(), Term::lam(a_sort(), Term::lam(equiv_ty(Term::Var(1), Term::Var(0)), body)));
        let ty = Term::pi(
            a_sort(),
            Term::pi(
                a_sort(),
                Term::pi(equiv_ty(Term::Var(1), Term::Var(0)), Term::arrow(Term::Var(2), Term::Var(1))),
            ),
        );
        env.insert(name("Equiv.f"), Decl::Def { num_levels: 1, ty, value })?;
    }
    // Equiv.g : Π (A B : Sort u) (e : Equiv A B), B → A
    {
        let motive = Term::lam(equiv_ty(Term::Var(1), Term::Var(0)), Term::arrow(Term::Var(1), Term::Var(2)));
        let mk_case = mk_case_of(Term::Var(2));
        let e = Term::Var(0);
        let body = equiv_rec(motive.lift(1, 0), mk_case.lift(1, 0), e, Term::Var(2), Term::Var(1));
        let value = Term::lam(a_sort(), Term::lam(a_sort(), Term::lam(equiv_ty(Term::Var(1), Term::Var(0)), body)));
        let ty = Term::pi(
            a_sort(),
            Term::pi(
                a_sort(),
                Term::pi(equiv_ty(Term::Var(1), Term::Var(0)), Term::arrow(Term::Var(1), Term::Var(2))),
            ),
        );
        env.insert(name("Equiv.g"), Decl::Def { num_levels: 1, ty, value })?;
    }
    declare_equiv_sec_ret(env)?;
    Ok(())
}

/// `Equiv.sec`/`Equiv.ret`, built via `Equiv.rec` with an `e`-*dependent* motive
/// (unlike `Equiv.f`/`Equiv.g`'s constant one) that states the coherence in terms
/// of the *already-installed* `Equiv.f`/`Equiv.g` projections of the abstract `e`.
/// `mk_case` supplies the constructor's own `sec`/`ret` field, which — at the
/// literal constructor `Equiv.mk A B f g sec ret` — has exactly the motive's
/// instantiated type up to the ι-rule unfolding `Equiv.f`/`Equiv.g` of that
/// literal `Equiv.mk` application back to `f`/`g` (checked by this module's
/// `equiv_sec_and_ret_types_wellformed` test).
fn declare_equiv_sec_ret(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let a_sort = || Term::Sort(u());
    let equiv_ty = |a: Term, b: Term| Term::apps(Term::cnst(name("Equiv"), vec![u()]), [a, b]);
    let equiv_rec = |motive: Term, mk_case: Term, e: Term, a: Term, b: Term| {
        Term::apps(Term::cnst(name("Equiv.rec"), vec![u(), u()]), [a, b, motive, mk_case, e])
    };
    let ef = |a: Term, b: Term, e: Term| Term::apps(Term::cnst(name("Equiv.f"), vec![u()]), [a, b, e]);
    let eg = |a: Term, b: Term, e: Term| Term::apps(Term::cnst(name("Equiv.g"), vec![u()]), [a, b, e]);

    // Equiv.sec : Π (A B : Sort u) (e : Equiv A B) (b : B),
    //               Path B (Equiv.f A B e (Equiv.g A B e b)) b
    {
        // `stmt`, valid under ctx [A,B,e] (A=Var(2),B=Var(1),e=Var(0)):
        //   Π (b:B). Path B (Equiv.f A B e (Equiv.g A B e b)) b
        let stmt = Term::pi(
            Term::Var(1), // B
            // ctx [A,B,e,b]: A=3,B=2,e=1,b=0
            Term::path(
                Term::Var(2),
                Term::app(ef(Term::Var(3), Term::Var(2), Term::Var(1)), Term::app(eg(Term::Var(3), Term::Var(2), Term::Var(1)), Term::Var(0))),
                Term::Var(0),
            ),
        );
        // motive = λ (e:Equiv A B). stmt, ctx [A,B]
        let motive = Term::lam(equiv_ty(Term::Var(1), Term::Var(0)), stmt.clone());
        // mk_case = λf λg λsec λret. sec  (ctx [A,B]: f=3,g=2,sec=1,ret=0)
        let mk_case = mk_case_of(Term::Var(1));
        let e = Term::Var(0); // ctx [A,B,e]
        let body = equiv_rec(motive.lift(1, 0), mk_case.lift(1, 0), e, Term::Var(2), Term::Var(1));
        let value = Term::lam(a_sort(), Term::lam(a_sort(), Term::lam(equiv_ty(Term::Var(1), Term::Var(0)), body)));
        let ty = Term::pi(a_sort(), Term::pi(a_sort(), Term::pi(equiv_ty(Term::Var(1), Term::Var(0)), stmt)));
        env.insert(name("Equiv.sec"), Decl::Def { num_levels: 1, ty, value })?;
    }
    // Equiv.ret : Π (A B : Sort u) (e : Equiv A B) (a : A),
    //               Path A (Equiv.g A B e (Equiv.f A B e a)) a
    {
        // `stmt`, valid under ctx [A,B,e] (A=Var(2),B=Var(1),e=Var(0)):
        //   Π (a:A). Path A (Equiv.g A B e (Equiv.f A B e a)) a
        let stmt = Term::pi(
            Term::Var(2), // A
            // ctx [A,B,e,a]: A=3,B=2,e=1,a=0
            Term::path(
                Term::Var(3),
                Term::app(eg(Term::Var(3), Term::Var(2), Term::Var(1)), Term::app(ef(Term::Var(3), Term::Var(2), Term::Var(1)), Term::Var(0))),
                Term::Var(0),
            ),
        );
        let motive = Term::lam(equiv_ty(Term::Var(1), Term::Var(0)), stmt.clone());
        // mk_case = λf λg λsec λret. ret  (ctx [A,B]: f=3,g=2,sec=1,ret=0)
        let mk_case = mk_case_of(Term::Var(0));
        let e = Term::Var(0);
        let body = equiv_rec(motive.lift(1, 0), mk_case.lift(1, 0), e, Term::Var(2), Term::Var(1));
        let value = Term::lam(a_sort(), Term::lam(a_sort(), Term::lam(equiv_ty(Term::Var(1), Term::Var(0)), body)));
        let ty = Term::pi(a_sort(), Term::pi(a_sort(), Term::pi(equiv_ty(Term::Var(1), Term::Var(0)), stmt)));
        env.insert(name("Equiv.ret"), Decl::Def { num_levels: 1, ty, value })?;
    }
    Ok(())
}

/// `idEquiv.{u} : Π (A : Sort u), Equiv A A` — the identity map, with `refl`
/// coherences (`sec`/`ret` are both `λx. ⟨_⟩ x`, i.e. `Term::plam(Var(0))`, which
/// checks against `Path A ((λx.x)((λx.x) x)) x` by β-reducing the endpoint to `x`).
fn declare_id_equiv(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let a_sort = || Term::Sort(u());
    let equiv_ty = |a: Term, b: Term| Term::apps(Term::cnst(name("Equiv"), vec![u()]), [a, b]);
    let mk = |args: [Term; 6]| Term::apps(Term::cnst(name("Equiv.mk"), vec![u()]), args);

    // ctx [A]: id = λx:A. x
    let id_fn = Term::lam(Term::Var(0), Term::Var(0));
    // ctx [A]: sec/ret = λx:A. ⟨_⟩ x. Inside the `PLam`, a fresh interval binder is
    // pushed (`Var(0)` there is the interval variable itself, of type `I` — *not*
    // `x`), so `x` must be referred to as `Var(1)`, one level further out.
    let refl_fn = Term::lam(Term::Var(0), Term::plam(Term::Var(1)));
    let value = Term::lam(
        a_sort(),
        mk([Term::Var(0), Term::Var(0), id_fn.clone(), id_fn, refl_fn.clone(), refl_fn]),
    );
    let ty = Term::pi(a_sort(), equiv_ty(Term::Var(0), Term::Var(0)));
    env.insert(name("idEquiv"), Decl::Def { num_levels: 1, ty, value })
}

/// Type-check every `Equiv`-related declaration's stated *type* (a well-formedness
/// sanity pass, mirroring [`crate::inductive::check_env_types`] — this does **not**
/// check that a `Decl::Def`'s *value* has its declared type; see this module's
/// tests for that separate, stronger check).
pub fn check_equiv_types(env: &Env) -> Result<(), String> {
    let chk = Checker::new(env);
    for n in ["Equiv", "Equiv.mk", "Equiv.rec", "Equiv.f", "Equiv.g", "Equiv.sec", "Equiv.ret", "idEquiv"] {
        let decl = env.get(n).ok_or_else(|| format!("missing '{n}'"))?;
        let mut ctx = crate::check::LocalCtx::new();
        chk.infer(&mut ctx, decl.ty()).map_err(|e| format!("'{n}': {e}"))?;
    }
    Ok(())
}

/// Check that every `Decl::Def` this module installs has a *value* matching its
/// *declared type* — `Env::insert` does not verify this on its own (see the module
/// doc's `Soundness` section), so this closes that gap explicitly. `cfg(test)`-only:
/// this is a one-off sanity check exercised by `equiv_def_values_match_their_types`
/// below, not part of the module's public API.
#[cfg(test)]
fn check_equiv_def_values(env: &Env) -> Result<(), String> {
    let chk = Checker::new(env);
    for n in ["Equiv.f", "Equiv.g", "Equiv.sec", "Equiv.ret", "idEquiv"] {
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

    fn equiv_env() -> Env {
        let mut env = Env::new();
        declare_equiv(&mut env).unwrap();
        env
    }

    #[test]
    fn equiv_types_wellformed() {
        let env = equiv_env();
        check_equiv_types(&env).unwrap();
    }

    /// The soundness-critical check `check_equiv_types` alone does *not* give:
    /// every installed `Decl::Def`'s *value* really has its *declared* type.
    #[test]
    fn equiv_def_values_match_their_types() {
        let env = equiv_env();
        check_equiv_def_values(&env).unwrap();
    }

    #[test]
    fn id_equiv_applies_to_nat() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_equiv(&mut env).unwrap();
        let chk = Checker::new(&env);
        let nat = Term::cnst(name("Nat"), vec![]);
        let id_nat = Term::app(Term::cnst(name("idEquiv"), vec![Level::of_nat(1)]), nat.clone());
        let ty = chk.infer_closed(&id_nat).expect("idEquiv Nat should type-check");
        let expected = Term::apps(Term::cnst(name("Equiv"), vec![Level::of_nat(1)]), [nat.clone(), nat]);
        let r = Reducer::new(&env);
        assert!(r.is_def_eq(&ty, &expected));
    }

    /// `Equiv.f (idEquiv A) ≡ λx. x` (ι/β) — the projection genuinely computes, not
    /// just type-checks.
    #[test]
    fn id_equiv_f_reduces_to_identity() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_equiv(&mut env).unwrap();
        let r = Reducer::new(&env);
        let nat = Term::cnst(name("Nat"), vec![]);
        let id_equiv_nat = Term::app(Term::cnst(name("idEquiv"), vec![Level::of_nat(1)]), nat.clone());
        let f_of_id = Term::apps(
            Term::cnst(name("Equiv.f"), vec![Level::of_nat(1)]),
            [nat.clone(), nat.clone(), id_equiv_nat],
        );
        let id_fn = Term::lam(nat, Term::Var(0));
        assert!(r.is_def_eq(&f_of_id, &id_fn));
    }

    /// Adversarial: a term that is *not* an `Equiv A B` (a bare `λx.x` applied to
    /// nothing sensible) must not check against `Equiv Nat Nat`.
    #[test]
    fn ill_formed_term_is_not_an_equiv() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_equiv(&mut env).unwrap();
        let chk = Checker::new(&env);
        let nat = Term::cnst(name("Nat"), vec![]);
        let bogus = Term::lam(nat.clone(), Term::Var(0)); // : Nat -> Nat, not Equiv Nat Nat
        let expected = Term::apps(Term::cnst(name("Equiv"), vec![Level::of_nat(1)]), [nat.clone(), nat]);
        let mut ctx = crate::check::LocalCtx::new();
        assert!(chk.check(&mut ctx, &bogus, &expected).is_err());
    }
}
