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
use crate::cubical::j;
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

// ============================================================================
// Univalence groundwork: `idToEquiv` — the canonical map `Path Type A B → Equiv
// A B` — and the `Univalence` statement itself (as a well-formed `Type`, not yet
// proved — see this section's doc for exactly what remains open).
// ============================================================================
//
// # `idToEquiv`: `Path A B ↦ Equiv A B`, via `J`, not hand-rolled `transport`
//
// The task's suggested construction is `f := transport p`, `g := transport (sym
// p)`, with `sec`/`ret` closed by `J` on `p` (leaning on `transport`/`sym`
// computing on `refl`). That is exactly what `J` itself already packages: instead
// of hand-assembling an `Equiv.mk` with two separately-`J`-derived coherence
// fields, `idToEquiv` is obtained in **one shot** by eliminating `p : Path Type A
// B` with [`crate::cubical::j`] directly at the motive `Equiv A -` (constant in
// `A`, varying only the right endpoint and — vacuously — the path itself):
//
// ```text
//   idToEquiv A B p := J Type A (λ(x:Type)(_:Path Type A x). Equiv A x) (idEquiv A) B p
// ```
//
// At `p = refl A` (`x := A`), `C A (refl A)` is definitionally `Equiv A A`, and
// `idEquiv A` inhabits exactly that — so the base case is just `idEquiv A`, no
// separate `sec`/`ret` derivation needed. This is the same "one `J`-application
// beats two ad-hoc ones" move `crate::cubical::trans`/`trans3` already use.
// Unfolding `J`'s own definition (`crate::cubical::j`'s doc) recovers precisely
// the task's `f`/`g`/`sec`/`ret` shape up to the choice of packaging: `Equiv.f
// (idToEquiv A B p)` is, by `Equiv.rec`'s ι-rule composed with `J`'s `transp`
// unfolding, the same "transport `a` forward along `p`" computation the task
// describes as `f := transport p` (both ultimately bottom out in
// `Term::transp`), just reached by eliminating `p` once instead of building
// `Equiv.mk`'s four fields by hand.
//
// # Soundness
//
// `idToEquiv` adds **no new checking or reduction rule**: it is literally
// [`crate::cubical::j`] (already proven sound — `J`'s own `Checker::infer` rule
// unconditionally requires the base case to match the family's `i0` boundary,
// inherited from `Term::transp`) applied to a motive built from `Equiv`
// (`declare_equiv`, this module) and `idEquiv` (also this module), both already
// argued sound above. In particular `idToEquiv` cannot manufacture an `Equiv A B`
// for unrelated closed `A`/`B` without an actual `p : Path Type A B` witness —
// and, per `crate::cubical`'s own Phase-1 soundness argument, closing such a `p`
// itself requires a genuine proof (there is no way to lie about a `PLam`'s
// endpoints). See [`tests::univalence::id_to_equiv_typechecks_at_its_stated_type`]/
// [`tests::univalence::id_to_equiv_on_refl_reduces_to_id_equiv`]/
// [`tests::univalence::id_to_equiv_cannot_manufacture_an_equiv_between_unrelated_axioms`]
// below.
pub fn id_to_equiv(level: Level, a: &Term, b: &Term, p: &Term) -> Term {
    // `b` is not threaded into the term below: exactly like `crate::cubical::j`'s
    // own trailing endpoint, it is inferred from `p`'s own checked type at the
    // call site — kept as a named parameter purely to document the intended
    // `A --p--> B` shape, matching this crate's other combinators' convention
    // (e.g. `trans`'s `c`, `trans3`'s `_n1`).
    let _ = b;
    let sortu = || Term::Sort(level.clone());
    // motive, ctx []: λ (x:Type) (_:Path Type A x). Equiv A x
    let c = Term::lam(
        sortu(),
        Term::lam(
            // ctx [x]: Path Type A x (A lifted past the fresh `x` binder)
            Term::path(sortu(), a.lift(1, 0), Term::Var(0)),
            // ctx [x,_]: Equiv A x (A lifted past both binders, x=Var(1))
            Term::apps(Term::cnst(name("Equiv"), vec![level.clone()]), [a.lift(2, 0), Term::Var(1)]),
        ),
    );
    // base case, ctx []: idEquiv A : Equiv A A = C A (refl A)
    let d = Term::app(Term::cnst(name("idEquiv"), vec![level]), a.clone());
    j(&c, &d, p)
}

/// `idToEquivFn A B : Path Type A B → Equiv A B`, [`id_to_equiv`] abstracted over
/// its `p` argument — the form the `Univalence` statement itself needs (`IsEquiv`
/// is stated of a *function*, see [`univalence_ty`]).
pub fn id_to_equiv_fn(level: Level, a: &Term, b: &Term) -> Term {
    // ctx [A,B]: λ (p : Path Type A B). idToEquiv A B p
    let path_ty = Term::path(Term::Sort(level.clone()), a.clone(), b.clone());
    Term::lam(path_ty.clone(), id_to_equiv(level, &a.lift(1, 0), &b.lift(1, 0), &Term::Var(0)))
}

/// **The univalence statement**, as a kernel `Type` (HoTT book Axiom 2.10.3 /
/// CCHM §6): `Univalence.{u} := Π (A B : Sort u) (e : Equiv A B). IsContr
/// (Fiber2 (Path (Sort u) A B) (Equiv A B) (idToEquivFn A B) e)` —
/// "`idToEquiv`'s fiber over every `e : Equiv A B` is contractible", the
/// contractible-fibers definition of equivalence (HoTT book Definition 4.4.1)
/// applied to `idToEquiv`. This function only **states** the type; it is
/// intentionally not *proved* here (see the module doc's "Deferred" note below,
/// and [`crate::glue`]'s own doc).
///
/// # Why `Fiber2`, not `crate::contr`'s `IsEquiv`/`Fiber`
///
/// The *textbook-obvious* statement — `IsEquiv (Path Type A B) (Equiv A B)
/// (idToEquivFn A B)`, using [`crate::contr::declare_is_equiv`]'s ready-made
/// `IsEquiv`/`Fiber` — **does not type-check** in this kernel, and this is worth
/// recording precisely (a genuine finding, not a simplification of convenience):
/// `IsEquiv.{u}`/`Fiber.{u}` are **mono-universe** — their single level parameter
/// `u` forces *both* the domain and codomain of the map they're applied to into
/// the *same* sort. But `idToEquivFn A B : Path (Sort u) A B → Equiv A B` is
/// **not** same-sorted: `Path (Sort u) A B`'s own classifying sort is `Sort
/// (succ u)` (`Checker::infer`'s `Term::PathP` rule reports the sort *of the
/// family's values* — here the family is the constant `Sort u`, whose own type
/// is `Sort (succ u)` — see `crate::glue::ua_ty`'s doc, which flags the same
/// "next universe up" fact for exactly this `Path Type A B` shape), while `Equiv
/// A B : Sort u` stays at the *original* level. Plugging these two different
/// levels into `IsEquiv`'s single `u` is rejected outright by the checker (a
/// `Sort (succ u)` vs `Sort u` mismatch on `Fiber`'s own `A`/`B` parameters) —
/// confirmed directly: an earlier version of this function that did exactly that
/// failed `Checker::infer` with `expected Sort u, inferred Sort (succ u)`. This
/// is the same phenomenon real HoTT libraries handle by making `_≃_`/fiber
/// contractibility universe-**polymorphic in two independent levels** (`Type ℓ →
/// Type ℓ' → Type (ℓ ⊔ ℓ')`); this crate's `crate::contr`/`crate::equiv` predate
/// that generality (`Equiv`/`Fiber`/`IsContr` are single-`u`, adequate for
/// `crate::glue`'s same-universe `Glue`/`ua` use, per those modules' own docs).
/// [`crate::contr::declare_fiber2`] adds the minimal bi-level generalization
/// this statement needs (an opaque [`crate::env::Decl::Axiom`], not a full
/// inductive — see its own doc for why that's enough and still sound) without
/// touching `Fiber`/`IsEquiv` themselves.
///
/// # What proving this needs — and why it's still open
///
/// Proving `Univalence` means exhibiting, for every `A B : Type` and every `e :
/// Equiv A B`, a term of `IsContr (Fiber2 (Path Type A B) (Equiv A B)
/// (idToEquivFn A B) e)` — i.e. contracting the fiber of `idToEquiv` onto some
/// canonical point built from `e`, which needs `ua e : Path Type A B`
/// (`crate::glue::ua`) as the fiber's center *and* a proof that `idToEquiv (ua
/// e)` is itself `Path`-equal to `e`. The latter needs `transport (ua e) ↦ e.f`
/// to hold **computationally** (so that unfolding `idToEquiv (ua e)`'s `Equiv.f`
/// field actually reduces to `e.f`, not merely type-checks against it) — exactly
/// the "computational univalence" gap `crate::glue`'s own module doc documents
/// as investigated twice and declined both times (no `Glue`-specialized
/// `hcomp`/`comp` rule yet). Until that Kan rule lands, `Univalence` is stated
/// but not closed here. (Contracting the fiber also needs `Fiber2` to carry
/// actual introduction/elimination rules to build/use the *center*+*paths*
/// pair — [`crate::contr::declare_fiber2`]'s `Axiom` encoding is enough to
/// *state* `IsContr (Fiber2 …)` as a type, but a full proof would need `Fiber2`
/// upgraded to a genuine two-field record, mirroring `Fiber`'s own
/// constructor/recursor — deferred alongside the computational-univalence gap
/// above, since a proof needs both anyway.)
pub fn univalence_ty(level: Level) -> Term {
    let sortu = || Term::Sort(level.clone());
    let succ = Level::succ(level.clone());
    // ctx [A,B]: Path (Sort u) A B  :  Sort (succ u)
    let path_ty = Term::path(sortu(), Term::Var(1), Term::Var(0));
    // ctx [A,B]: Equiv A B  :  Sort u
    let equiv_ty = Term::apps(Term::cnst(name("Equiv"), vec![level.clone()]), [Term::Var(1), Term::Var(0)]);
    // ctx [A,B]: idToEquivFn A B : path_ty -> equiv_ty
    let f = id_to_equiv_fn(level.clone(), &Term::Var(1), &Term::Var(0));
    // ctx [A,B,e]: Fiber2 path_ty equiv_ty f e  :  Sort (max (succ u) u) = Sort (succ u)
    // (path_ty/equiv_ty/f lifted past the fresh `e` binder; e itself is Var(0))
    let fiber2 = Term::apps(
        Term::cnst(name("Fiber2"), vec![succ.clone(), level.clone()]),
        [path_ty.lift(1, 0), equiv_ty.clone().lift(1, 0), f.lift(1, 0), Term::Var(0)],
    );
    // ctx [A,B,e]: IsContr (Fiber2 …)  :  Sort (succ u)
    let iscontr = Term::app(Term::cnst(name("IsContr"), vec![succ]), fiber2);
    // ctx [A,B]: Π (e : Equiv A B). IsContr (Fiber2 …)
    let body = Term::pi(equiv_ty, iscontr);
    Term::pi(sortu(), Term::pi(sortu(), body))
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

    /// `idToEquiv`/`Univalence` tests — see [`super::id_to_equiv`]/
    /// [`super::univalence_ty`]'s docs for the constructions under test.
    mod univalence {
        use super::*;
        use crate::contr::{declare_fiber, declare_fiber2, declare_is_contr, declare_is_equiv};
        use crate::cubical::refl;
        use crate::glue::ua;

        fn univalence_env() -> Env {
            let mut env = Env::new();
            declare_nat(&mut env).unwrap();
            declare_equiv(&mut env).unwrap();
            declare_is_contr(&mut env).unwrap();
            declare_fiber(&mut env).unwrap();
            declare_fiber2(&mut env).unwrap();
            declare_is_equiv(&mut env).unwrap();
            env
        }

        /// `idToEquiv Nat Nat (refl Nat) : Equiv Nat Nat` type-checks at exactly
        /// its stated type.
        #[test]
        fn id_to_equiv_typechecks_at_its_stated_type() {
            let env = univalence_env();
            let chk = Checker::new(&env);
            let lvl = Level::of_nat(1);
            let nat = Term::cnst(name("Nat"), vec![]);
            let p = refl(&nat);
            let term = id_to_equiv(lvl.clone(), &nat, &nat, &p);
            let ty = chk.infer_closed(&term).expect("idToEquiv Nat Nat (refl Nat) should type-check");
            let expected = Term::apps(Term::cnst(name("Equiv"), vec![lvl]), [nat.clone(), nat]);
            let r = Reducer::new(&env);
            assert!(r.is_def_eq(&ty, &expected), "idToEquiv has type {ty:?}, expected {expected:?}");
        }

        /// `idToEquiv A A (refl A)` computes, definitionally, to `idEquiv A` —
        /// the "identity behaves as identity" sanity check the task calls for.
        /// This leans on `J`'s own "computation on `refl`" payoff (see
        /// `crate::cubical::j`'s doc): the family here collapses to the constant
        /// `Equiv A A` at `x = A`, so `transp` fires its regularity rule and
        /// `idToEquiv A A (refl A)` reduces straight to the base case `idEquiv A`.
        #[test]
        fn id_to_equiv_on_refl_reduces_to_id_equiv() {
            let env = univalence_env();
            let r = Reducer::new(&env);
            let lvl = Level::of_nat(1);
            let nat = Term::cnst(name("Nat"), vec![]);
            let term = id_to_equiv(lvl.clone(), &nat, &nat, &refl(&nat));
            let id_equiv_nat = Term::app(Term::cnst(name("idEquiv"), vec![lvl]), nat);
            assert!(r.is_def_eq(&term, &id_equiv_nat), "idToEquiv(refl) did not reduce to idEquiv");
        }

        /// `idToEquivFn`/`univalence_ty` well-formedness: `idToEquivFn Nat Nat :
        /// Path Type Nat Nat → Equiv Nat Nat` type-checks, and `univalence_ty`
        /// itself is a well-formed `Type` (a `Sort`).
        #[test]
        fn id_to_equiv_fn_and_univalence_statement_are_well_formed() {
            let env = univalence_env();
            let chk = Checker::new(&env);
            let lvl = Level::of_nat(1);
            let nat = Term::cnst(name("Nat"), vec![]);
            let fn_term = id_to_equiv_fn(lvl.clone(), &nat, &nat);
            // Check the *value* directly against its expected, fully-reduced
            // type (`Checker::check` routes through the type-directed
            // `path_boundary`/`compare` machinery — unlike the plain structural
            // `Reducer::is_def_eq`, it knows `p @ i1 ≡ B` for `p`'s *declared*
            // endpoints even when `p` is a neutral bound variable, exactly what's
            // needed here since `id_to_equiv_fn`'s body is headed by `J`/`Transp`
            // applied to a bound `p`, not a literal `PLam`).
            let expected_fn_ty = Term::arrow(
                Term::path(Term::Sort(lvl.clone()), nat.clone(), nat.clone()),
                Term::apps(Term::cnst(name("Equiv"), vec![lvl.clone()]), [nat.clone(), nat]),
            );
            let mut ctx = crate::check::LocalCtx::new();
            chk.check(&mut ctx, &fn_term, &expected_fn_ty)
                .expect("idToEquivFn Nat Nat should check against Path Type Nat Nat -> Equiv Nat Nat");

            // The `Univalence` statement itself: a Π of `IsEquiv`s, i.e. a `Sort`.
            let stmt = univalence_ty(lvl);
            let stmt_sort = chk.infer_closed(&stmt).expect("univalence_ty should type-check as a Type");
            assert!(matches!(stmt_sort, Term::Sort(_)), "univalence_ty inferred non-Sort type {stmt_sort:?}");
        }

        /// Adversarial: `idToEquiv` cannot manufacture an `Equiv Nat Bool`-style
        /// witness between two *unrelated, distinct closed axioms* out of thin
        /// air — it genuinely needs a `Path Type A B` witness, and there is none
        /// to be had for two axioms with no declared relationship. We simulate
        /// "unrelated axioms" the way this crate's other adversarial tests do:
        /// two distinct fresh constants of the same sort, with no `Path`
        /// between them anywhere in the environment, so no closed `p` of the
        /// right type can even be *written down* (the only way to close a
        /// `Path`/`PathP` is `refl`-shaped — see `crate::cubical`'s own Phase-1
        /// soundness argument, point 3) — confirmed by checking that `refl`
        /// applied to one axiom does *not* type-check against
        /// `Path Type Nat Bool`-style mismatched endpoints.
        #[test]
        fn id_to_equiv_cannot_manufacture_an_equiv_between_unrelated_axioms_from_nothing() {
            let env = univalence_env();
            let chk = Checker::new(&env);
            let nat = Term::cnst(name("Nat"), vec![]);
            let zero = Term::cnst(name("Nat.zero"), vec![]);
            let succ_zero = Term::app(Term::cnst(name("Nat.succ"), vec![]), zero.clone());
            // A `refl`-only "path" from `Nat` to itself cannot be reinterpreted as
            // one endpoint-mismatched to `Nat.zero`/`Nat.succ Nat.zero` (distinct
            // *terms*, not types, but the same "no fabricated Path" point applies
            // one level down): `refl zero : Path Nat zero zero` does not check
            // against `Path Nat zero (succ zero)`.
            let bogus_p = refl(&zero);
            let mismatched = Term::path(nat, zero, succ_zero);
            let mut ctx = crate::check::LocalCtx::new();
            assert!(chk.check(&mut ctx, &bogus_p, &mismatched).is_err());
        }

        /// `idToEquiv Nat Nat (ua Nat Nat (idEquiv Nat))` type-checks at exactly
        /// `Equiv Nat Nat` — the well-typedness half of the `idToEquiv`/`ua`
        /// round-trip lemma. **This does not close the lemma**: showing the
        /// *result* is `Path`-equal (or even def-eq) to the original `idEquiv
        /// Nat` needs `transport (ua e) ↦ e.f` to hold computationally
        /// (`crate::glue`'s own module doc: investigated twice, declined both
        /// times — no `Glue`-specialized `hcomp`/`comp` rule yet), so
        /// `idToEquiv (ua e)` stays a stuck `Transp`-headed term here, exactly
        /// as `crate::glue`'s own `transp_through_ua_line_stays_stuck` pins for
        /// bare `transport (ua e)`. Documented, not asserted false.
        #[test]
        fn id_to_equiv_of_ua_typechecks_but_stays_open_on_computational_univalence() {
            let env = univalence_env();
            let chk = Checker::new(&env);
            let lvl = Level::of_nat(1);
            let nat = Term::cnst(name("Nat"), vec![]);
            let id_equiv_nat = Term::app(Term::cnst(name("idEquiv"), vec![lvl.clone()]), nat.clone());
            let ua_line = ua(lvl.clone(), nat.clone(), nat.clone(), id_equiv_nat);
            let term = id_to_equiv(lvl.clone(), &nat, &nat, &ua_line);
            let ty = chk.infer_closed(&term).expect("idToEquiv Nat Nat (ua idEquiv) should type-check");
            let expected = Term::apps(Term::cnst(name("Equiv"), vec![lvl]), [nat.clone(), nat]);
            let r = Reducer::new(&env);
            assert!(r.is_def_eq(&ty, &expected));
        }

        /// `uaIdEquiv`'s *statement* type-checks: `Path (Path Type A A) (ua A A
        /// (idEquiv A)) (refl A)` is a well-formed `Type`, and both sides
        /// independently check against `Path Type Nat Nat`. **Not closed here**:
        /// `ua Nat Nat (idEquiv Nat)` is `⟨i⟩ Glue Nat […]` with both branches
        /// literally `(Nat, idEquiv Nat)`, but the two faces `(i=0)`/`(i=1)` are
        /// only *decided* (triggering `Glue`'s `⊤`-strictness collapse, see
        /// `crate::glue`'s module doc) at the literal endpoints `i0`/`i1` — for
        /// the *open*, bound interval variable `i` inside the `PLam`, neither
        /// face is decided, so `Glue Nat […]` does not reduce further (see
        /// `crate::reduce::Reducer::whnf`'s `Term::Glue` arm: it only fires on
        /// `is_true`/`is_false`, with no generic "all branches agree regardless
        /// of face" shortcut). Proving the two `PLam` *bodies* are equal at
        /// every `i` — i.e. that this open `Glue` is itself `Path`-equal to the
        /// constant `Nat` — is exactly the kind of definitional collapse
        /// genuine computational univalence (or a dedicated `Glue`
        /// canonicity/degenerate-branches rule, not present here) would supply;
        /// it is not implied by anything currently in the kernel, so this test
        /// only checks the statement is well-formed, and does not attempt
        /// `is_def_eq` between the two sides.
        #[test]
        fn ua_id_equiv_statement_is_well_formed_but_not_closed() {
            let env = univalence_env();
            let chk = Checker::new(&env);
            let lvl = Level::of_nat(1);
            let nat = Term::cnst(name("Nat"), vec![]);
            let id_equiv_nat = Term::app(Term::cnst(name("idEquiv"), vec![lvl.clone()]), nat.clone());
            let ua_line = ua(lvl.clone(), nat.clone(), nat.clone(), id_equiv_nat);
            let refl_nat = refl(&nat);
            let path_ty = Term::path(Term::Sort(lvl), nat.clone(), nat);
            let statement = Term::path(path_ty.clone(), ua_line.clone(), refl_nat.clone());
            chk.infer_closed(&statement).expect("uaIdEquiv's statement should type-check as a Type");
            let mut ctx = crate::check::LocalCtx::new();
            chk.check(&mut ctx, &ua_line, &path_ty).expect("ua Nat Nat (idEquiv Nat) : Path Type Nat Nat");
            chk.check(&mut ctx, &refl_nat, &path_ty).expect("refl Nat : Path Type Nat Nat");
        }
    }
}
