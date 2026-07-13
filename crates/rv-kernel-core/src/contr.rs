//! **Coherent equivalence notions, part 1**: `IsContr A` (contractibility),
//! `Fiber f b` (the homotopy fiber), and `IsEquiv f` (the contractible-fibers
//! definition of equivalence — HoTT book §4.2/§4.4), plus `idIsEquiv`: the
//! identity map has contractible fibers.
//!
//! ## Why this exists
//!
//! `crate::equiv`'s `Equiv A B` is **bi-invertible** (`f`,`g`,`sec`,`ret` with *no*
//! coherence between `sec`/`ret`) — exactly what `Glue`'s computational content
//! needs, per that module's doc, but strictly weaker than the usual equivalence
//! notions used to state *univalence* itself and to supply `Glue`'s Kan
//! correction term (see `crate::kan`'s Phase 3.12–3.14 diagnosis, cited in this
//! crate's worklog: the Glue Kan correction needs the equivalence's *coherence*
//! data, which bi-invertible maps don't carry). This module builds the
//! **contractible-fibers** notion (HoTT book Definition 4.4.1); `crate::equiv_hae`
//! (a sibling module) builds the **half-adjoint** notion (Definition 4.2.1) and
//! the bridges between the three.
//!
//! ## Encoding: single-constructor inductive records, no `Σ`
//!
//! This kernel has no primitive `Σ`-type (see `crate::inductive`'s module doc), so
//! `IsContr`/`Fiber` are hand-built single-constructor inductives, exactly the
//! `Nat`/`Eq`/`Equiv` pattern in `crate::inductive`/`crate::equiv`:
//!
//! ```text
//!   IsContr A          := record { center : A, paths : Π(x:A). Path A center x }
//!   Fiber A B f b       := record { a : A, p : Path B (f a) b }
//!   IsEquiv A B f       := Π (b:B). IsContr (Fiber A B f b)          -- a Π, not a new inductive
//! ```
//!
//! `IsEquiv` itself needs no new inductive: it's literally a `Π`-type built from
//! the two records above, installed as a plain `Decl::Def` whose *value* is a
//! `Sort`-classified type (a "type synonym", the same encoding `crate::equiv`
//! uses for its projections, just one level up: a `Decl::Def` computing a `Sort`
//! instead of a term).
//!
//! ## `idIsEquiv`: the punchline construction
//!
//! `idIsEquiv A : IsEquiv A A (id A)` must produce, for every `b : A`, an
//! `IsContr (Fiber A A (id A) b)`. The center is the obvious `(b, refl b)`
//! (`Fiber.mk A A id b b (refl b)`); the hard part is `paths : Π w. Path (Fiber …)
//! center w`. This is built by eliminating `w` with `Fiber.rec` into the motive
//! `M(w) := Path (Fiber …) center w`, reducing the `Fiber.mk a p`-case to a
//! **based path induction** via [`crate::cubical::j`]:
//!
//! * `sym : Path A x y → Path A y x` is added here (`⟨i⟩ p @ (~i)`, the interval-
//!   reversal analogue of `crate::cubical::ap`/`funext` — a one-line definitional
//!   fact, no new checking/reduction rule) so that `p : Path A a b` (Fiber's field,
//!   with `f = id`) can be flipped to `sym p : Path A b a`, matching
//!   [`crate::cubical::j`]'s basepoint-`b` convention.
//! * The motive fed to `j` is `C(x, q : Path A b x) := Path (Fiber …) center
//!   (Fiber.mk … x (sym q))`, with `d := refl center : C b (refl b)` — this
//!   type-checks because `sym (refl b)` reduces (interval β on a constant `PLam`
//!   body, regardless of the substituted endpoint) to `refl b` on the nose, so
//!   `C b (refl b)` is definitionally `Path (Fiber …) center center`.
//! * Applying `j C d (sym p)` at `x := a` gives `C a (sym p) = Path (Fiber …)
//!   center (Fiber.mk … a (sym (sym p)))`. `sym (sym p) ≡ p` definitionally
//!   (`crate::cubical::interval_eq`'s De Morgan normalization collapses `~~i` to
//!   `i` inside the nested `PApp`/`PLam`, which every conversion check in this
//!   kernel already routes through — see `crate::cubical`'s module doc), so this
//!   term checks, by conversion, against the goal `Path (Fiber …) center
//!   (Fiber.mk … a p)`.
//!
//! No new primitive, checking rule, or reduction rule is added anywhere in this
//! construction: it is `Fiber.rec` (an ordinary hand-built recursor, §"Soundness"
//! below) applied to a term built entirely from [`crate::cubical::j`]/`refl`/the
//! one-line `sym` above, all pre-existing, already-sound machinery.
//!
//! ## Deferred: half-adjoint coherence
//!
//! Per the task's own explicit fallback, the half-adjoint equivalence's coherence
//! field `τ` (the triangle identity, a *2-dimensional* path) is **not** attempted
//! in this pass — seeing it through correctly would need a genuine 2-path
//! construction (composing/filling squares) well beyond the one-line `sym`/`j`
//! combinators used above, and the risk of a subtly-wrong 2-path is exactly the
//! kind of mistake this module's adversarial-testing discipline exists to catch
//! *before* landing, not after. `crate::equiv_hae` instead declares the *shape*
//! of `IsHAE` (so its field types are on record for the eventual Glue-Kan
//! consumer) and documents the τ gap explicitly; see that module's doc.
//!
//! ## Soundness
//!
//! `IsContr`/`IsContr.mk`/`IsContr.rec` and `Fiber`/`Fiber.mk`/`Fiber.rec` are
//! installed via [`crate::inductive::declare_raw`] — the same trusted,
//! hand-checked path as `Nat`/`Eq`/`Equiv` — so they inherit that path's
//! soundness argument verbatim (see `crate::equiv`'s module doc for the fully
//! spelled-out version: the ι-rule computes exactly what the recursor's own
//! declared return type promises, checked concretely by this module's
//! `check_*_def_values` tests, since `Env::insert` does not verify `value : ty`
//! on its own). `IsEquiv`/`idIsEquiv`/the field projections add no new trusted
//! machinery: they are plain `Decl::Def`s built from the recursors and from
//! `crate::cubical::j`/`refl`/`sym`, all pre-existing and already argued sound.

use crate::check::Checker;
use crate::cubical::{j, refl, trans};
use crate::env::{Constructor, Decl, Env, Inductive, RecRule, Recursor};
use crate::inductive::{declare_raw, RawInductive};
use crate::level::Level;
use crate::term::{name, Term};
use std::collections::HashMap;

/// `sym p : Path A y x`, given `p : Path A x y` — interval reversal `⟨i⟩ p @
/// (~i)`. The mirror image of [`crate::cubical::ap`]/`funext`: a purely
/// definitional fact once `Path`/`PApp`/`INeg` exist (see this module's doc for
/// why `~~i ≡ i` matters downstream), no new checking or reduction rule.
pub fn sym(p: &Term) -> Term {
    Term::plam(Term::papp(p.lift(1, 0), Term::ineg(Term::Var(0))))
}

/// The two field types `(center_ty, paths_ty)` of `IsContr.mk`, valid under a
/// context where `A` sits at `Var(extra)` (mirrors `crate::equiv::field_tys`'s
/// `extra`-parameterization — see that function's doc for why lifting the pieces
/// individually after the fact would be wrong).
fn contr_field_tys(extra: usize) -> (Term, Term) {
    let center_ty = Term::Var(extra); // A
    let a1 = extra + 1; // ctx [...,A,center]: A at a1
    let paths_ty = Term::pi(
        Term::Var(a1), // A
        // ctx [...,A,center,x]: A=a1+1, center=1, x=0
        Term::path(Term::Var(a1 + 1), Term::Var(1), Term::Var(0)),
    );
    (center_ty, paths_ty)
}

/// `λ (center:A) (paths:…). body`, using [`contr_field_tys`]`(0)`'s domains
/// (`center=Var(1)`, `paths=Var(0)` under `body`).
fn mk_case_of_contr(body: Term) -> Term {
    let (center_ty, paths_ty) = contr_field_tys(0);
    Term::lam(center_ty, Term::lam(paths_ty, body))
}

/// Declare `IsContr.{u} : Π (A : Sort u), Sort u` with constructor `IsContr.mk`
/// (fields `center`, `paths`, see the module doc) and recursor `IsContr.rec`.
/// Hand-built, mirroring `crate::equiv::declare_equiv`.
pub fn declare_is_contr(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let a_sort = || Term::Sort(u());
    let iscontr = |a: Term| Term::app(Term::cnst(name("IsContr"), vec![u()]), a);
    let mk = |args: [Term; 3]| Term::apps(Term::cnst(name("IsContr.mk"), vec![u()]), args);

    // IsContr : Π (A : Sort u), Sort u
    let ind_ty = Term::pi(a_sort(), a_sort());
    let inductive = Inductive {
        num_levels: 1,
        ty: ind_ty,
        num_params: 1,
        num_indices: 0,
        ctors: vec![name("IsContr.mk")],
        recursor: name("IsContr.rec"),
        group: vec![name("IsContr")],
    };

    // IsContr.mk : Π (A:Sort u) (center:A) (paths: Π(x:A). Path A center x), IsContr A
    let (center_ty, paths_ty) = contr_field_tys(0);
    let mk_body = iscontr(Term::Var(2)); // ctx [A,center,paths]
    let mk_ty = Term::pi(a_sort(), Term::pi(center_ty, Term::pi(paths_ty, mk_body)));
    let ctor_mk = Constructor { num_levels: 1, ty: mk_ty, ind: name("IsContr"), index: 0, num_fields: 2 };

    // IsContr.rec.{u,v} : Π (A:Sort u)
    //                       (motive : IsContr A → Sort v)
    //                       (mk_case : Π (center:A)(paths:…), motive (IsContr.mk A center paths))
    //                       (c : IsContr A), motive c
    let v = Level::param(1);
    let motive_ty = Term::arrow(iscontr(Term::Var(0)), Term::Sort(v)); // ctx [A]
    let (center_ty2, paths_ty2) = contr_field_tys(1); // ctx [A,motive]
    // ctx [A,motive,center,paths]: motive=Var(2)
    let mk_result = Term::app(Term::Var(2), mk([Term::Var(3), Term::Var(1), Term::Var(0)]));
    let mk_case_ty = Term::pi(center_ty2, Term::pi(paths_ty2, mk_result));
    let c_ty = iscontr(Term::Var(2)); // ctx [A,motive,mk_case]
    let result = Term::app(Term::Var(2), Term::Var(0)); // ctx [A,motive,mk_case,c]: motive c
    let rec_ty = Term::pi(a_sort(), Term::pi(motive_ty, Term::pi(mk_case_ty, Term::pi(c_ty, result))));

    // ι-rule: applied to [A,motive,mk_case,center,paths] ↦ mk_case center paths.
    let rule_mk = RecRule {
        ctor: name("IsContr.mk"),
        num_fields: 2,
        rhs: {
            let mut t = Term::apps(Term::Var(2), [Term::Var(1), Term::Var(0)]);
            for _ in 0..5 {
                t = Term::lam(Term::prop(), t);
            }
            t
        },
    };
    let mut rules = HashMap::new();
    rules.insert(name("IsContr.mk"), rule_mk);

    let recursor = Recursor {
        num_levels: 2,
        ty: rec_ty,
        ind: name("IsContr"),
        num_params: 1,
        num_motives: 1,
        num_indices: 0,
        num_minors: 1,
        rules,
    };

    declare_raw(
        env,
        RawInductive {
            ind_name: name("IsContr"),
            inductive,
            ctors: vec![(name("IsContr.mk"), ctor_mk)],
            rec_name: name("IsContr.rec"),
            recursor,
        },
    )?;

    declare_is_contr_projections(env)
}

/// `IsContr.center`/`IsContr.paths`, the standard "record projection via
/// recursor" encoding (mirrors `crate::equiv::declare_equiv_projections`/
/// `declare_equiv_sec_ret`: `center` uses a constant motive like `Equiv.f`/`g`,
/// `paths` uses an `c`-dependent motive stated via the already-installed
/// `IsContr.center`, like `Equiv.sec`/`ret`).
fn declare_is_contr_projections(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let a_sort = || Term::Sort(u());
    let iscontr = |a: Term| Term::app(Term::cnst(name("IsContr"), vec![u()]), a);
    let rec = |motive: Term, mk_case: Term, c: Term, a: Term| {
        Term::apps(Term::cnst(name("IsContr.rec"), vec![u(), u()]), [a, motive, mk_case, c])
    };

    // IsContr.center : Π (A:Sort u) (c:IsContr A), A
    {
        let motive = Term::lam(iscontr(Term::Var(0)), Term::Var(1)); // ctx [A]: A
        let mk_case = mk_case_of_contr(Term::Var(1)); // ctx [A]: center
        let c = Term::Var(0); // ctx [A,c]
        let body = rec(motive.lift(1, 0), mk_case.lift(1, 0), c, Term::Var(1));
        let value = Term::lam(a_sort(), Term::lam(iscontr(Term::Var(0)), body));
        let ty = Term::pi(a_sort(), Term::pi(iscontr(Term::Var(0)), Term::Var(1)));
        env.insert(name("IsContr.center"), Decl::Def { num_levels: 1, ty, value })?;
    }
    // IsContr.paths : Π (A:Sort u) (c:IsContr A) (x:A), Path A (IsContr.center A c) x
    {
        let center = |a: Term, c: Term| Term::apps(Term::cnst(name("IsContr.center"), vec![u()]), [a, c]);
        // stmt, ctx [A,c] (A=1,c=0): Π (x:A). Path A (IsContr.center A c) x
        let stmt = Term::pi(
            Term::Var(1),
            // ctx [A,c,x]: A=2,c=1,x=0
            Term::path(Term::Var(2), center(Term::Var(2), Term::Var(1)), Term::Var(0)),
        );
        let motive = Term::lam(iscontr(Term::Var(0)), stmt.clone()); // ctx [A]
        let mk_case = mk_case_of_contr(Term::Var(0)); // ctx [A]: paths
        let c = Term::Var(0);
        let body = rec(motive.lift(1, 0), mk_case.lift(1, 0), c, Term::Var(1));
        let value = Term::lam(a_sort(), Term::lam(iscontr(Term::Var(0)), body));
        let ty = Term::pi(a_sort(), Term::pi(iscontr(Term::Var(0)), stmt));
        env.insert(name("IsContr.paths"), Decl::Def { num_levels: 1, ty, value })?;
    }
    Ok(())
}

/// The two field types `(a_ty, p_ty)` of `Fiber.mk`, valid under a context with
/// `[..., A, B, f, b]` immediately preceding where `a` is about to be bound and
/// `extra` extra binders before `A` (mirrors `crate::equiv::field_tys`'s
/// `extra`-parameterization, one level up in arity: four fixed params `A B f b`
/// instead of two).
fn fiber_field_tys(extra: usize) -> (Term, Term) {
    let a_ty = Term::Var(3 + extra); // A
    // after binding `a`, everything else shifts by 1
    let p_ty = Term::path(
        Term::Var(3 + extra),                           // B
        Term::app(Term::Var(2 + extra), Term::Var(0)),  // f a
        Term::Var(1 + extra),                           // b
    );
    (a_ty, p_ty)
}

/// `λ (a:A) (p:…). body`, using [`fiber_field_tys`]`(0)`'s domains (`a=Var(1)`,
/// `p=Var(0)` under `body`).
fn mk_case_of_fiber(body: Term) -> Term {
    let (a_ty, p_ty) = fiber_field_tys(0);
    Term::lam(a_ty, Term::lam(p_ty, body))
}

/// Declare `Fiber.{u} : Π (A B : Sort u) (f : A→B) (b : B), Sort u` — the
/// homotopy fiber of `f` over `b` (HoTT book Definition 4.2.4) — with
/// constructor `Fiber.mk` (fields `a`, `p`, see the module doc) and recursor
/// `Fiber.rec`. Hand-built, mirroring `crate::equiv::declare_equiv`.
pub fn declare_fiber(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let a_sort = || Term::Sort(u());
    let fiberc = |args: [Term; 4]| Term::apps(Term::cnst(name("Fiber"), vec![u()]), args);
    let mk = |args: [Term; 6]| Term::apps(Term::cnst(name("Fiber.mk"), vec![u()]), args);

    // Fiber : Π (A B : Sort u) (f : A→B) (b : B), Sort u
    let ind_ty = Term::pi(
        a_sort(),
        Term::pi(
            a_sort(),
            Term::pi(Term::arrow(Term::Var(1), Term::Var(0)), Term::pi(Term::Var(1), a_sort())),
        ),
    );
    let inductive = Inductive {
        num_levels: 1,
        ty: ind_ty,
        num_params: 4,
        num_indices: 0,
        ctors: vec![name("Fiber.mk")],
        recursor: name("Fiber.rec"),
        group: vec![name("Fiber")],
    };

    // Fiber.mk : Π (A B:Sort u) (f:A→B) (b:B) (a:A) (p:Path B (f a) b), Fiber A B f b
    let (a_ty, p_ty) = fiber_field_tys(0);
    let mk_body = fiberc([Term::Var(5), Term::Var(4), Term::Var(3), Term::Var(2)]); // ctx [A,B,f,b,a,p]
    let mk_ty = Term::pi(
        a_sort(),
        Term::pi(
            a_sort(),
            Term::pi(
                Term::arrow(Term::Var(1), Term::Var(0)),
                Term::pi(Term::Var(1), Term::pi(a_ty, Term::pi(p_ty, mk_body))),
            ),
        ),
    );
    let ctor_mk = Constructor { num_levels: 1, ty: mk_ty, ind: name("Fiber"), index: 0, num_fields: 2 };

    // Fiber.rec.{u,v} : Π (A B:Sort u) (f:A→B) (b:B)
    //                     (motive : Fiber A B f b → Sort v)
    //                     (mk_case : Π (a:A)(p:…), motive (Fiber.mk A B f b a p))
    //                     (w : Fiber A B f b), motive w
    let v = Level::param(1);
    // ctx [A,B,f,b]: motive : Fiber A B f b → Sort v
    let motive_ty = Term::arrow(fiberc([Term::Var(3), Term::Var(2), Term::Var(1), Term::Var(0)]), Term::Sort(v));
    let (a_ty2, p_ty2) = fiber_field_tys(1); // ctx [A,B,f,b,motive]
    // ctx [A,B,f,b,motive,a,p]: motive=Var(2)
    let mk_result = Term::app(
        Term::Var(2),
        mk([Term::Var(6), Term::Var(5), Term::Var(4), Term::Var(3), Term::Var(1), Term::Var(0)]),
    );
    let mk_case_ty = Term::pi(a_ty2, Term::pi(p_ty2, mk_result));
    // ctx [A,B,f,b,motive,mk_case]: w_ty
    let w_ty = fiberc([Term::Var(5), Term::Var(4), Term::Var(3), Term::Var(2)]);
    // ctx [A,B,f,b,motive,mk_case,w]: motive w
    let result = Term::app(Term::Var(2), Term::Var(0));
    let rec_ty = Term::pi(
        a_sort(),
        Term::pi(
            a_sort(),
            Term::pi(
                Term::arrow(Term::Var(1), Term::Var(0)),
                Term::pi(Term::Var(1), Term::pi(motive_ty, Term::pi(mk_case_ty, Term::pi(w_ty, result)))),
            ),
        ),
    );

    // ι-rule: applied to [A,B,f,b,motive,mk_case,a,p] ↦ mk_case a p.
    let rule_mk = RecRule {
        ctor: name("Fiber.mk"),
        num_fields: 2,
        rhs: {
            let mut t = Term::apps(Term::Var(2), [Term::Var(1), Term::Var(0)]);
            for _ in 0..8 {
                t = Term::lam(Term::prop(), t);
            }
            t
        },
    };
    let mut rules = HashMap::new();
    rules.insert(name("Fiber.mk"), rule_mk);

    let recursor = Recursor {
        num_levels: 2,
        ty: rec_ty,
        ind: name("Fiber"),
        num_params: 4,
        num_motives: 1,
        num_indices: 0,
        num_minors: 1,
        rules,
    };

    declare_raw(
        env,
        RawInductive {
            ind_name: name("Fiber"),
            inductive,
            ctors: vec![(name("Fiber.mk"), ctor_mk)],
            rec_name: name("Fiber.rec"),
            recursor,
        },
    )?;

    declare_fiber_projections(env)
}

/// `Fiber.a`/`Fiber.p`, the standard "record projection via recursor" encoding
/// (mirrors `crate::equiv::declare_equiv_projections`/`declare_equiv_sec_ret`).
fn declare_fiber_projections(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let a_sort = || Term::Sort(u());
    let fiberc = |args: [Term; 4]| Term::apps(Term::cnst(name("Fiber"), vec![u()]), args);
    let rec = |motive: Term, mk_case: Term, w: Term, args: [Term; 4]| {
        Term::apps(Term::cnst(name("Fiber.rec"), vec![u(), u()]), [args[0].clone(), args[1].clone(), args[2].clone(), args[3].clone(), motive, mk_case, w])
    };

    // Fiber.a : Π (A B:Sort u) (f:A→B) (b:B) (w:Fiber A B f b), A
    {
        // ctx [A,B,f,b]: motive = λ_:Fiber A B f b. A
        let motive = Term::lam(fiberc([Term::Var(3), Term::Var(2), Term::Var(1), Term::Var(0)]), Term::Var(4));
        let mk_case = mk_case_of_fiber(Term::Var(1)); // ctx [A,B,f,b]: a
        let w = Term::Var(0); // ctx [A,B,f,b,w]
        let args = [Term::Var(4), Term::Var(3), Term::Var(2), Term::Var(1)];
        let body = rec(motive.lift(1, 0), mk_case.lift(1, 0), w, args);
        let w_dom = fiberc([Term::Var(3), Term::Var(2), Term::Var(1), Term::Var(0)]); // ctx [A,B,f,b]
        let value = Term::lam(
            a_sort(),
            Term::lam(
                a_sort(),
                Term::lam(
                    Term::arrow(Term::Var(1), Term::Var(0)),
                    Term::lam(Term::Var(1), Term::lam(w_dom.clone(), body)),
                ),
            ),
        );
        let ty = Term::pi(
            a_sort(),
            Term::pi(
                a_sort(),
                Term::pi(
                    Term::arrow(Term::Var(1), Term::Var(0)),
                    Term::pi(Term::Var(1), Term::pi(w_dom, Term::Var(4))),
                ),
            ),
        );
        env.insert(name("Fiber.a"), Decl::Def { num_levels: 1, ty, value })?;
    }
    // Fiber.p : Π (A B:Sort u) (f:A→B) (b:B) (w:Fiber A B f b), Path B (f (Fiber.a A B f b w)) b
    {
        let fa = |a: Term, b: Term, f: Term, b2: Term, w: Term| {
            Term::apps(Term::cnst(name("Fiber.a"), vec![u()]), [a, b, f, b2, w])
        };
        // stmt, ctx [A,B,f,b,w] (A=4,B=3,f=2,b=1,w=0):
        //   Path B (f (Fiber.a A B f b w)) b
        let stmt = Term::path(
            Term::Var(3),
            Term::app(Term::Var(2), fa(Term::Var(4), Term::Var(3), Term::Var(2), Term::Var(1), Term::Var(0))),
            Term::Var(1),
        );
        // ctx [A,B,f,b]: motive = λw. stmt
        let motive = Term::lam(fiberc([Term::Var(3), Term::Var(2), Term::Var(1), Term::Var(0)]), stmt.clone());
        let mk_case = mk_case_of_fiber(Term::Var(0)); // ctx [A,B,f,b]: p
        let w = Term::Var(0);
        let args = [Term::Var(4), Term::Var(3), Term::Var(2), Term::Var(1)];
        let body = rec(motive.lift(1, 0), mk_case.lift(1, 0), w, args);
        let w_dom = fiberc([Term::Var(3), Term::Var(2), Term::Var(1), Term::Var(0)]); // ctx [A,B,f,b]
        let value = Term::lam(
            a_sort(),
            Term::lam(
                a_sort(),
                Term::lam(
                    Term::arrow(Term::Var(1), Term::Var(0)),
                    Term::lam(Term::Var(1), Term::lam(w_dom.clone(), body)),
                ),
            ),
        );
        let ty = Term::pi(
            a_sort(),
            Term::pi(
                a_sort(),
                Term::pi(
                    Term::arrow(Term::Var(1), Term::Var(0)),
                    Term::pi(Term::Var(1), Term::pi(w_dom, stmt)),
                ),
            ),
        );
        env.insert(name("Fiber.p"), Decl::Def { num_levels: 1, ty, value })?;
    }
    Ok(())
}

/// `Fiber2.{u,v} : Π (A:Sort u) (B:Sort v) (f:A→B) (b:B), Sort (max u v)` — a
/// **bi-level** generalization of [`Fiber`]/`declare_fiber` above, needed for
/// `crate::equiv::univalence_ty` (see that function's doc): stating "`idToEquiv`
/// is an equivalence" needs the fiber of a map `idToEquivFn A B : Path Type A B →
/// Equiv A B` whose domain (`Path Type A B`, a path *between elements of the
/// universe*) lives one universe **above** its codomain (`Equiv A B`) — see
/// `crate::cubical`'s/`Checker::infer`'s `Term::PathP` rule: `PathP`'s own sort is
/// the sort *classifying the family's values*, and here the family's values are
/// literally `Sort level` itself, one level above `level`. `Fiber`/`IsContr`
/// (this module, above) are deliberately **mono-universe** (`Fiber.{u}`'s single
/// `u` forces *both* its `A` and `B` parameters into the *same* sort) — exactly
/// right for `crate::glue`'s `Equiv`-only use, but too weak for a fiber whose two
/// endpoints genuinely live a universe apart. Rather than generalizing `Fiber`
/// itself (used throughout `crate::contr`/`crate::glue`/`crate::kan` at a single,
/// load-bearing level — out of scope to touch here), [`declare_fiber2`] adds a
/// **parallel**, independently-leveled type former, declared as an opaque
/// [`Decl::Axiom`] (a bare `Π`-classified constant, *not* a full inductive with
/// its own constructor/recursor): `crate::equiv::univalence_ty` only needs
/// `Fiber2`/[`IsContr`] to *state* univalence (`IsContr (Fiber2 …)` as a
/// well-formed `Type`), not to eliminate/compute with a `Fiber2` value — no
/// recursor is needed for that, and an axiom adds no new equation or reduction
/// rule (so it cannot be used, by itself, to derive `False` — see this module's
/// `Soundness` doc for the general shape of that argument, which applies
/// verbatim: an uninhabited-unless-genuinely-proved `Axiom`-classified type is
/// exactly as inert as `Term::I`/an unproved `Path` boundary).
pub fn declare_fiber2(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let v = || Level::param(1);
    // Π (A:Sort u) (B:Sort v) (f:A→B) (b:B), Sort (max u v)
    let ty = Term::pi(
        Term::Sort(u()),
        Term::pi(
            Term::Sort(v()), // ctx [A]
            Term::pi(
                Term::arrow(Term::Var(1), Term::Var(0)), // ctx [A,B]: A→B
                Term::pi(Term::Var(1), Term::Sort(Level::max(u(), v()))), // ctx [A,B,f]: B → Sort(max u v)
            ),
        ),
    );
    env.insert(name("Fiber2"), Decl::Axiom { num_levels: 2, ty })
}

/// `IsEquiv.{u} : Π (A B:Sort u) (f:A→B), Sort u := λ A B f. Π(b:B). IsContr
/// (Fiber A B f b)` — the contractible-fibers definition of equivalence (HoTT
/// book Definition 4.4.1). A plain `Decl::Def` computing a `Sort`, no new
/// inductive (see the module doc).
pub fn declare_is_equiv(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let a_sort = || Term::Sort(u());
    let fiberc = |args: [Term; 4]| Term::apps(Term::cnst(name("Fiber"), vec![u()]), args);
    let iscontr = |a: Term| Term::app(Term::cnst(name("IsContr"), vec![u()]), a);

    // ctx [A,B,f]: Π (b:B). IsContr (Fiber A B f b)   (A=2,B=1,f=0)
    let body = Term::pi(
        Term::Var(1), // B
        // ctx [A,B,f,b]: A=3,B=2,f=1,b=0
        iscontr(fiberc([Term::Var(3), Term::Var(2), Term::Var(1), Term::Var(0)])),
    );
    let value = Term::lam(a_sort(), Term::lam(a_sort(), Term::lam(Term::arrow(Term::Var(1), Term::Var(0)), body)));
    let ty = Term::pi(a_sort(), Term::pi(a_sort(), Term::pi(Term::arrow(Term::Var(1), Term::Var(0)), a_sort())));
    env.insert(name("IsEquiv"), Decl::Def { num_levels: 1, ty, value })?;

    declare_id_is_equiv(env)
}

/// `idIsEquiv.{u} : Π (A:Sort u). IsEquiv A A (id A)` — the identity map has
/// contractible fibers (HoTT book Example 4.2.5 / Theorem 4.4.2's degenerate
/// case). See the module doc's "the punchline construction" section for the
/// full derivation of the `paths` field via [`crate::cubical::j`].
fn declare_id_is_equiv(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let a_sort = || Term::Sort(u());

    // Build everything with fully explicit indices instead of ad-hoc closures
    // (this construction is intricate enough that indirection just obscures the
    // bookkeeping — see the inline comments at each step).
    let mk_fiber = |args: [Term; 4]| Term::apps(Term::cnst(name("Fiber"), vec![u()]), args);
    let mk_fiber_mk = |args: [Term; 6]| Term::apps(Term::cnst(name("Fiber.mk"), vec![u()]), args);
    let mk_iscontr = |a: Term| Term::app(Term::cnst(name("IsContr"), vec![u()]), a);
    let mk_iscontr_mk = |args: [Term; 3]| Term::apps(Term::cnst(name("IsContr.mk"), vec![u()]), args);
    let fiber_rec = |args: [Term; 7]| Term::apps(Term::cnst(name("Fiber.rec"), vec![u(), u()]), args);

    // ctx [A,b]: A=1, b=0; id_fn = λx:A. x
    // fiber_type(x) [ctx A,b, plus `x` bound over A at Var(0) meaning A=2,b=1]:
    //   Fiber A A (id A) b
    // We build the whole `paths` proof under ctx [A,b], then wrap.

    // id_fn under ctx [A,b]: A at Var(1)
    let idf_ab = Term::lam(Term::Var(1), Term::Var(0));
    // Fiber A A (id A) b, ctx [A,b]
    let fiber_b = mk_fiber([Term::Var(1), Term::Var(1), idf_ab.clone(), Term::Var(0)]);
    // center := Fiber.mk A A (id A) b b (refl b), ctx [A,b]
    let center = mk_fiber_mk([Term::Var(1), Term::Var(1), idf_ab.clone(), Term::Var(0), Term::Var(0), refl(&Term::Var(0))]);

    // Build `paths : Π (w : Fiber A A (id A) b). Path (Fiber A A (id A) b) center w`
    // via Fiber.rec with mk_case := λ(a:A)(p:Path A a b). j(C,d,sym p), where
    //   C := λ(x:A)(q:Path A b x). Path (Fiber A A (id A) b) center (Fiber.mk A A (id A) b x (sym q))
    //   d := refl center
    // C/d/center are built under ctx [A,b]; the `mk_case` lambda adds two more
    // binders (a,p) on top, so C/d (and `fiber_b`/`center` used inside them) need
    // lifting by 2 wherever they cross into the `a,p`-bound scope.

    // C, under ctx [A,b] — `crate::cubical::j`'s motive is a *function*
    // `λ(x:A)(q:Path A b x). Sort v` (applied via `App`/`App` inside `j`, see its
    // body), **not** a `Pi`-type, so this must be `Term::lam`/`Term::lam`, not
    // `Term::pi`/`Term::pi` (the two share the same binder-domain shape, but a
    // `Pi` here would make `j`'s `App(App(c, ..), ..)` ill-typed):
    //   λ(x:A). λ(q:Path A b x). Path (Fiber A A id b) center (Fiber.mk A A id b x (sym q))
    let c_term = {
        // bind x: ctx [A,b,x]: A=2,b=1,x=0
        let a_at_x = Term::Var(2);
        let b_at_x = Term::Var(1);
        Term::lam(
            Term::Var(1), // A (ctx [A,b])
            Term::lam(
                // Path A b x, ctx [A,b,x]: A=2,b=1,x=0
                Term::path(a_at_x.clone(), b_at_x.clone(), Term::Var(0)),
                {
                    // ctx [A,b,x,q]: A=3,b=2,x=1,q=0
                    let fiber_here = mk_fiber([Term::Var(3), Term::Var(3), Term::lam(Term::Var(3), Term::Var(0)), Term::Var(2)]);
                    let center_here = mk_fiber_mk([
                        Term::Var(3),
                        Term::Var(3),
                        Term::lam(Term::Var(3), Term::Var(0)),
                        Term::Var(2),
                        Term::Var(2),
                        refl(&Term::Var(2)),
                    ]);
                    let sym_q = sym(&Term::Var(0));
                    let mk_at_x = mk_fiber_mk([
                        Term::Var(3),
                        Term::Var(3),
                        Term::lam(Term::Var(3), Term::Var(0)),
                        Term::Var(2),
                        Term::Var(1),
                        sym_q,
                    ]);
                    Term::path(fiber_here, center_here, mk_at_x)
                },
            ),
        )
    };
    // d := refl center, ctx [A,b]
    let d_term = refl(&center);

    // mk_case := λ(a:A)(p:Path A a b). j(C,d,sym p) — but j/C/d must be expressed
    // relative to ctx [A,b,a,p] (a,p are the two new binders); C/d were built
    // under ctx [A,b], so lift them by 2.
    let mk_case = {
        // a_ty, p_ty at extra=1 shift relative to Fiber's own field_tys style: here
        // it's simpler, `a:A` (A=Var(1) under ctx[A,b]) and `p:Path A a b`.
        let a_ty = Term::Var(1); // A, ctx [A,b]
        let a1 = 2usize; // ctx [A,b,a]: A=2,b=1,a=0
        let p_ty = Term::path(Term::Var(a1), Term::Var(0), Term::Var(a1 - 1)); // Path A a b
        // ctx [A,b,a,p]: A=3,b=2,a=1,p=0
        let sym_p = sym(&Term::Var(0));
        let j_term = j(&c_term.lift(2, 0), &d_term.lift(2, 0), &sym_p);
        Term::lam(a_ty, Term::lam(p_ty, j_term))
    };

    // paths := λ(w : Fiber A A id b). Fiber.rec A A id b (λw. Path (Fiber…) center w) mk_case w
    let paths_fn = {
        // ctx [A,b,w]: A=2,b=1,w=0
        let motive_paths_w = Term::lam(fiber_b.clone().lift(1, 0), {
            Term::path(fiber_b.clone().lift(2, 0), center.lift(2, 0), Term::Var(0))
        });
        let body = fiber_rec([
            Term::Var(2),                 // A
            Term::Var(2),                 // A
            idf_ab.lift(1, 0),            // id A
            Term::Var(1),                 // b
            motive_paths_w,
            mk_case.lift(1, 0),
            Term::Var(0),                 // w
        ]);
        Term::lam(fiber_b.clone(), body)
    };

    // IsContr.mk (Fiber A A id b) center paths_fn, ctx [A,b]
    let contr_b = mk_iscontr_mk([fiber_b.clone(), center.clone(), paths_fn]);
    let _ = mk_iscontr;

    // idIsEquiv := λA. λb. contr_b   :  Π A. Π (b:A). IsContr (Fiber A A id A b)
    let value = Term::lam(a_sort(), Term::lam(Term::Var(0), contr_b));
    // ty := Π A. IsEquiv A A (id A)
    let is_equiv = |a1: Term, a2: Term, f: Term| Term::apps(Term::cnst(name("IsEquiv"), vec![u()]), [a1, a2, f]);
    let ty = Term::pi(a_sort(), is_equiv(Term::Var(0), Term::Var(0), Term::lam(Term::Var(0), Term::Var(0))));

    env.insert(name("idIsEquiv"), Decl::Def { num_levels: 1, ty, value })
}

// ============================================================================
// h-levels: `isProp`/`isSet`/`isGroupoid`, and `isContrToIsProp` (HoTT book
// §3.1/§3.11 and Definition 3.1.1/3.1.2 more generally, chapter 3 "Sets and
// logic").
// ============================================================================
//
// The h-level hierarchy classifies types by how much "higher path structure"
// they carry, starting from contractibility (h-level 0):
//
// ```text
//   isProp  A := Π (x y : A). Path A x y                       -- h-level 1
//   isSet   A := Π (x y : A). isProp (Path A x y)               -- h-level 2
//   isGroupoid A := Π (x y : A). isSet (Path A x y)             -- h-level 3
// ```
//
// (HoTT book Definition 3.1.1 states `isProp`/`isSet` exactly this way — "any
// two elements are equal" and "any two elements' equality proofs are
// equal", respectively; `isGroupoid` extends the same pattern one level up,
// as the book's §7.1 "h-level" discussion generalizes.) Each is installed as
// a plain `Decl::Def` computing a `Sort`, exactly [`declare_is_equiv`]'s
// "type synonym" encoding one level up: `isProp`/`isSet`/`isGroupoid` are
// themselves *type-valued functions* (`Π (A:Sort u). Sort u`), not new
// inductives — no constructor/recursor is needed since nothing eliminates an
// `isProp A` value here, only *terms of* that Π-type are ever built (by
// [`isContrToIsProp`] below, and by user code).
//
// `isContrToIsProp` (HoTT book Lemma 3.11.3, "conctractible types are
// propositions") is the first payoff: given `c : IsContr A`, ANY two `x y :
// A` are connected by a path built from `c`'s own center-connecting paths,
// **without needing `trans_assoc`** — both `x` and `y` are joined to the
// *same* midpoint (`c`'s `center`), so the construction is a single `trans`
// application, not a nested/associated one:
//
// ```text
//   isContrToIsProp A c x y := trans A x y (sym (c.paths x)) (c.paths y)
//                            :  Path A x y
// ```
//
// (`c.paths x : Path A center x`, so `sym (c.paths x) : Path A x center`;
// `c.paths y : Path A center y`; `trans`'s own signature — see
// `crate::cubical::trans`'s doc — infers the shared midpoint `center` from
// the two paths' checked types and produces `Path A x y` directly.) This is
// nothing but [`sym`] (this module) and [`crate::cubical::trans`] (already
// proven sound — see that function's own doc) composed once: no new
// checking or reduction rule, so it inherits both of their soundness
// arguments verbatim.
//
// # `isPropToIsSet`: BLOCKED on `trans_assoc`
//
// The next classical step, "propositions are sets" (HoTT book Lemma 3.3.4),
// is **not** attempted as a closed kernel term in this pass. Its standard
// proof, for `f : isProp A` and `x y : A`, fixes `g := λy. f x y : Π y. Path
// A x y` and shows any `p : Path A x y` equals `trans (sym (g x)) (g y)` via
// `apd g p : transport^{λz. Path A x z}_p (g x) = g y`. Unwinding
// `transport` along that family (HoTT book Lemma 2.11.2) gives `trans (g x)
// p = g y`, i.e. a *2-dimensional* equation between paths-of-paths; peeling
// it back to `p` itself needs
//
// ```text
//   p  ≡  trans (sym (g x)) (trans (g x) p)          [left-inverse law, CLOSED
//                                                       here: crate::cubical::
//                                                       trans_inv_left]
//      ≡  trans (trans (sym (g x)) (g x)) p           [REASSOCIATION —
//                                                       trans_assoc, OPEN]
//      ≡  trans (refl x) p  ≡  p                      [left-unit law, CLOSED
//                                                       here: trans_left_unit]
// ```
//
// The middle step is *exactly* `crate::cubical::trans_assoc`, which this
// crate's own module doc documents as open (see `cubical.rs`'s "Phase 4.6"
// section and its `#[ignore]`d `trans_assoc_closes` test): it *type-checks
// as a term* but its stated Path-between-Paths goal does not close under
// `k.infer`/`def_eq` yet (an `nbe.rs` gap in comparing `ap`-of-a-`Transp`-
// subject inside a beta-redex, explicitly flagged as off-limits for this
// pass). Since `isPropToIsSet`'s only known proof route funnels through
// exactly that reassociation, it is intentionally **not attempted** here —
// forcing a proof through the open gap risks landing an unsound or
// non-type-checking term, which this module's own soundness discipline
// (`check_contr_def_values`, adversarial tests) exists to prevent. `isProp`/
// `isSet`/`isGroupoid` (the *statements*) and `isContrToIsProp` are landed
// below as genuine, closed, kernel-checked progress; `isPropToIsSet` and the
// further h-level tower (`isPropIsContr`, `isContr → isSet`, etc. — task
// items 4/5) are left as documented future work gated on `trans_assoc`.

/// `isProp.{u} : Π (A:Sort u). Sort u := λA. Π(x y:A). Path A x y` — "any two
/// elements of `A` are equal" (HoTT book Definition 3.1.1, first half;
/// h-level 1). A `Decl::Def` computing a `Sort`, the same "type synonym"
/// encoding [`declare_is_equiv`] uses.
pub fn declare_is_prop(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    // ctx [A,x,y] (A=2,x=1,y=0): Path A x y
    let body = Term::path(Term::Var(2), Term::Var(1), Term::Var(0));
    // ctx [A,x] (A=1,x=0): Π(y:A). Path A x y — y's domain is A = Var(1) here.
    let inner = Term::pi(Term::Var(1), body);
    // ctx [A] (A=0): Π(x:A). Π(y:A). Path A x y — x's domain is A = Var(0) here.
    let value = Term::lam(Term::Sort(u()), Term::pi(Term::Var(0), inner));
    let ty = Term::pi(Term::Sort(u()), Term::Sort(u()));
    env.insert(name("isProp"), Decl::Def { num_levels: 1, ty, value })
}

/// `isSet.{u} : Π (A:Sort u). Sort u := λA. Π(x y:A). isProp (Path A x y)` —
/// "any two equality proofs of `A` are equal" (HoTT book Definition 3.1.1,
/// second half; h-level 2). Requires [`declare_is_prop`] to already be
/// installed (`isProp` is a free constant in `isSet`'s value).
pub fn declare_is_set(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let is_prop = |t: Term| Term::app(Term::cnst(name("isProp"), vec![u()]), t);
    // ctx [A,x,y] (A=2,x=1,y=0): isProp (Path A x y)
    let body = is_prop(Term::path(Term::Var(2), Term::Var(1), Term::Var(0)));
    let inner = Term::pi(Term::Var(1), body); // ctx [A,x]: y's domain is A = Var(1)
    let value = Term::lam(Term::Sort(u()), Term::pi(Term::Var(0), inner)); // ctx [A]
    let ty = Term::pi(Term::Sort(u()), Term::Sort(u()));
    env.insert(name("isSet"), Decl::Def { num_levels: 1, ty, value })
}

/// `isGroupoid.{u} : Π (A:Sort u). Sort u := λA. Π(x y:A). isSet (Path A x
/// y)` — h-level 3, the same pattern one level up. Requires
/// [`declare_is_set`] to already be installed.
pub fn declare_is_groupoid(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let is_set = |t: Term| Term::app(Term::cnst(name("isSet"), vec![u()]), t);
    let body = is_set(Term::path(Term::Var(2), Term::Var(1), Term::Var(0))); // ctx [A,x,y]
    let inner = Term::pi(Term::Var(1), body); // ctx [A,x]: y's domain is A = Var(1)
    let value = Term::lam(Term::Sort(u()), Term::pi(Term::Var(0), inner)); // ctx [A]
    let ty = Term::pi(Term::Sort(u()), Term::Sort(u()));
    env.insert(name("isGroupoid"), Decl::Def { num_levels: 1, ty, value })
}

/// `isContrToIsProp.{u} : Π (A:Sort u). IsContr A → isProp A` — a
/// contractible type is a proposition (HoTT book Lemma 3.11.3). See this
/// section's module doc for the single-`trans` construction (no
/// `trans_assoc` needed: both `x` and `y` are connected through the *same*
/// midpoint, `c`'s own `center`). Requires [`declare_is_contr`] and
/// [`declare_is_prop`] to already be installed.
pub fn declare_is_contr_to_is_prop(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let iscontr = |a: Term| Term::app(Term::cnst(name("IsContr"), vec![u()]), a);
    let is_prop = |a: Term| Term::app(Term::cnst(name("isProp"), vec![u()]), a);
    let paths = |a: Term, c: Term, x: Term| {
        Term::apps(Term::cnst(name("IsContr.paths"), vec![u()]), [a, c, x])
    };

    // ty := Π (A:Sort u). IsContr A → isProp A
    let ty = Term::pi(
        Term::Sort(u()),
        // ctx [A] (A=0): IsContr A → isProp A
        Term::arrow(iscontr(Term::Var(0)), is_prop(Term::Var(0))),
    );

    // value := λA. λc. λx. λy. trans A x y (sym (paths A c x)) (paths A c y)
    // ctx [A,c,x,y]: A=3,c=2,x=1,y=0
    let a_t = Term::Var(3);
    let c_t = Term::Var(2);
    let x_t = Term::Var(1);
    let y_t = Term::Var(0);
    let paths_x = paths(a_t.clone(), c_t.clone(), x_t.clone());
    let paths_y = paths(a_t.clone(), c_t.clone(), y_t.clone());
    let body = trans(&a_t, &x_t, &y_t, &sym(&paths_x), &paths_y);

    // ctx [A,c,x]: y's domain is A, shifted to Var(2) at that binder.
    let lam_y = Term::lam(Term::Var(2), body);
    // ctx [A,c]: x's domain is A, shifted to Var(1) at that binder.
    let lam_x = Term::lam(Term::Var(1), lam_y);
    // ctx [A]: c's domain is IsContr A, A = Var(0) at that binder.
    let lam_c = Term::lam(iscontr(Term::Var(0)), lam_x);
    let value = Term::lam(Term::Sort(u()), lam_c);

    env.insert(name("isContrToIsProp"), Decl::Def { num_levels: 1, ty, value })
}

/// Type-check every declaration's stated *type* (well-formedness sanity pass,
/// mirroring `crate::equiv::check_equiv_types`).
pub fn check_contr_types(env: &Env) -> Result<(), String> {
    let chk = Checker::new(env);
    for n in [
        "IsContr", "IsContr.mk", "IsContr.rec", "IsContr.center", "IsContr.paths",
        "Fiber", "Fiber.mk", "Fiber.rec", "Fiber.a", "Fiber.p",
        "Fiber2",
        "IsEquiv", "idIsEquiv",
        "isProp", "isSet", "isGroupoid", "isContrToIsProp",
    ] {
        let decl = env.get(n).ok_or_else(|| format!("missing '{n}'"))?;
        let mut ctx = crate::check::LocalCtx::new();
        chk.infer(&mut ctx, decl.ty()).map_err(|e| format!("'{n}': {e}"))?;
    }
    Ok(())
}

/// Check every `Decl::Def` this module installs has a *value* matching its
/// *declared type* (`Env::insert` does not verify this on its own — see this
/// module's `Soundness` doc). `cfg(test)`-only, mirroring
/// `crate::equiv::check_equiv_def_values`.
#[cfg(test)]
fn check_contr_def_values(env: &Env) -> Result<(), String> {
    let chk = Checker::new(env);
    for n in [
        "IsContr.center", "IsContr.paths", "Fiber.a", "Fiber.p", "IsEquiv", "idIsEquiv",
        "isProp", "isSet", "isGroupoid", "isContrToIsProp",
    ] {
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

    fn contr_env() -> Env {
        let mut env = Env::new();
        declare_is_contr(&mut env).unwrap();
        declare_fiber(&mut env).unwrap();
        declare_fiber2(&mut env).unwrap();
        declare_is_equiv(&mut env).unwrap();
        declare_is_prop(&mut env).unwrap();
        declare_is_set(&mut env).unwrap();
        declare_is_groupoid(&mut env).unwrap();
        declare_is_contr_to_is_prop(&mut env).unwrap();
        env
    }

    #[test]
    fn contr_types_wellformed() {
        let env = contr_env();
        check_contr_types(&env).unwrap();
    }

    #[test]
    fn contr_def_values_match_their_types() {
        let env = contr_env();
        check_contr_def_values(&env).unwrap();
    }

    /// `idIsEquiv Nat : IsEquiv Nat Nat (id Nat)` type-checks and its inferred
    /// type matches the expected `IsEquiv` instance up to conversion.
    #[test]
    fn id_is_equiv_applies_to_nat() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_is_contr(&mut env).unwrap();
        declare_fiber(&mut env).unwrap();
        declare_is_equiv(&mut env).unwrap();
        let chk = Checker::new(&env);
        let nat = Term::cnst(name("Nat"), vec![]);
        let id_nat = Term::app(Term::cnst(name("idIsEquiv"), vec![Level::of_nat(1)]), nat.clone());
        let ty = chk.infer_closed(&id_nat).expect("idIsEquiv Nat should type-check");
        let id_fn = Term::lam(nat.clone(), Term::Var(0));
        let expected = Term::apps(Term::cnst(name("IsEquiv"), vec![Level::of_nat(1)]), [nat.clone(), nat, id_fn]);
        let r = Reducer::new(&env);
        assert!(r.is_def_eq(&ty, &expected), "idIsEquiv Nat has type {ty:?}, expected {expected:?}");
    }

    /// `Fiber2 A B f b : Sort (max u v)` at genuinely different `u`/`v` (a `Prop`
    /// domain, `Sort 1` codomain) — confirms `declare_fiber2` really is
    /// bi-level-polymorphic, unlike mono-level `Fiber`.
    #[test]
    fn fiber2_typechecks_at_two_different_levels() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_fiber2(&mut env).unwrap();
        let chk = Checker::new(&env);
        // `A = Nat : Sort(1)` (`u=1`) and `B = Sort(1) : Sort(2)` (`v=2`, "Type
        // 1", one universe above `Nat`'s own) — genuinely different levels.
        let nat = Term::cnst(name("Nat"), vec![]); // : Sort(1) (u=1)
        let type1 = Term::Sort(Level::of_nat(1)); // "Type 1" : Sort(2) (v=2)
        let f = Term::lam(nat.clone(), nat.clone()); // : Nat → Type 1, constantly `Nat`
        let b = nat.clone(); // : Type 1
        let fiber2 = Term::apps(
            Term::cnst(name("Fiber2"), vec![Level::of_nat(1), Level::of_nat(2)]),
            [nat, type1, f, b],
        );
        let ty = chk.infer_closed(&fiber2).expect("Fiber2 at mixed levels should type-check");
        let r = Reducer::new(&env);
        assert!(r.is_def_eq(&ty, &Term::Sort(Level::max(Level::of_nat(1), Level::of_nat(2)))));
    }

    /// `sym (refl a) ≡ refl a` — the definitional fact `idIsEquiv`'s construction
    /// leans on for `d : C b (refl b)` to type-check.
    #[test]
    fn sym_of_refl_is_refl() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        let r = Reducer::new(&env);
        let z = Term::cnst(name("Nat.zero"), vec![]);
        assert!(r.is_def_eq(&sym(&refl(&z)), &refl(&z)));
    }

    /// `sym (sym p) ≡ p` — the definitional fact that closes `idIsEquiv`'s `j`
    /// application back down to the exact goal type.
    #[test]
    fn sym_sym_is_identity() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        let r = Reducer::new(&env);
        let z = Term::cnst(name("Nat.zero"), vec![]);
        let p = refl(&z); // any Path witness works for this purely-interval fact
        assert!(r.is_def_eq(&sym(&sym(&p)), &p));
    }

    /// Adversarial: a bogus term (a bare `λx.x`) must not check against
    /// `IsContr Nat`.
    #[test]
    fn ill_formed_term_is_not_contractible() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_is_contr(&mut env).unwrap();
        let chk = Checker::new(&env);
        let nat = Term::cnst(name("Nat"), vec![]);
        let bogus = Term::lam(nat.clone(), Term::Var(0));
        let expected = Term::app(Term::cnst(name("IsContr"), vec![Level::of_nat(1)]), nat);
        let mut ctx = crate::check::LocalCtx::new();
        assert!(chk.check(&mut ctx, &bogus, &expected).is_err());
    }

    /// `isContrToIsProp Nat idIsEquiv-derived-contractibility` is not directly
    /// available (no closed `IsContr Nat` witness in this corpus), but the
    /// *type* `isContrToIsProp Nat : IsContr Nat → isProp Nat` must itself
    /// type-check and match the expected instance up to conversion.
    #[test]
    fn is_contr_to_is_prop_applies_to_nat() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        let env = {
            let mut env = env;
            declare_is_contr(&mut env).unwrap();
            declare_is_prop(&mut env).unwrap();
            declare_is_contr_to_is_prop(&mut env).unwrap();
            env
        };
        let chk = Checker::new(&env);
        let nat = Term::cnst(name("Nat"), vec![]);
        let applied = Term::app(Term::cnst(name("isContrToIsProp"), vec![Level::of_nat(1)]), nat.clone());
        let ty = chk.infer_closed(&applied).expect("isContrToIsProp Nat should type-check");
        let iscontr_nat = Term::app(Term::cnst(name("IsContr"), vec![Level::of_nat(1)]), nat.clone());
        let isprop_nat = Term::app(Term::cnst(name("isProp"), vec![Level::of_nat(1)]), nat);
        let expected = Term::arrow(iscontr_nat, isprop_nat);
        let r = Reducer::new(&env);
        assert!(r.is_def_eq(&ty, &expected), "isContrToIsProp Nat has type {ty:?}, expected {expected:?}");
    }

    /// `isContrToIsProp` applied fully to a genuine `c : IsContr A` witness
    /// (built directly via `IsContr.mk` from a reflexivity-only contraction,
    /// the simplest nontrivial contractible-type shape: `A := Nat`'s
    /// singleton-at-a-point is not literally contractible, so we use an
    /// *opaque* axiom-postulated `c` instead — the point of this test is
    /// that the fully-applied term type-checks at the exact goal `Path A x
    /// y`, not that `Nat` itself is contractible) produces a well-typed
    /// `Path A x y` witness.
    #[test]
    fn is_contr_to_is_prop_produces_a_path_from_an_opaque_witness() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_is_contr(&mut env).unwrap();
        declare_is_prop(&mut env).unwrap();
        declare_is_contr_to_is_prop(&mut env).unwrap();
        let nat = Term::cnst(name("Nat"), vec![]);
        let iscontr_nat = Term::app(Term::cnst(name("IsContr"), vec![Level::of_nat(1)]), nat.clone());
        env.insert(name("c_ax"), Decl::Axiom { num_levels: 0, ty: iscontr_nat }).unwrap();
        let x = Term::cnst(name("Nat.zero"), vec![]);
        let y = Term::app(Term::cnst(name("Nat.succ"), vec![]), x.clone());
        let c = Term::cnst(name("c_ax"), vec![]);
        let applied = Term::apps(
            Term::cnst(name("isContrToIsProp"), vec![Level::of_nat(1)]),
            [nat.clone(), c, x.clone(), y.clone()],
        );
        let chk = Checker::new(&env);
        let ty = chk.infer_closed(&applied).expect("isContrToIsProp Nat c x y should type-check");
        let expected = Term::path(nat, x, y);
        let r = Reducer::new(&env);
        assert!(r.is_def_eq(&ty, &expected), "isContrToIsProp Nat c x y has type {ty:?}, expected {expected:?}");
    }

    /// `isSet`/`isGroupoid`'s definitions type-check and their stated shapes
    /// (`Π A. Sort u`) match at a concrete instantiation.
    #[test]
    fn is_set_and_is_groupoid_apply_to_nat() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_is_prop(&mut env).unwrap();
        declare_is_set(&mut env).unwrap();
        declare_is_groupoid(&mut env).unwrap();
        let chk = Checker::new(&env);
        let nat = Term::cnst(name("Nat"), vec![]);
        let is_set_nat = Term::app(Term::cnst(name("isSet"), vec![Level::of_nat(1)]), nat.clone());
        let is_gpd_nat = Term::app(Term::cnst(name("isGroupoid"), vec![Level::of_nat(1)]), nat);
        chk.infer_closed(&is_set_nat).expect("isSet Nat should type-check");
        chk.infer_closed(&is_gpd_nat).expect("isGroupoid Nat should type-check");
    }

    /// Adversarial: a bogus term must not check against `Fiber A B f b` either.
    #[test]
    fn ill_formed_term_is_not_a_fiber() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_fiber(&mut env).unwrap();
        let chk = Checker::new(&env);
        let nat = Term::cnst(name("Nat"), vec![]);
        let id_fn = Term::lam(nat.clone(), Term::Var(0));
        let bogus = Term::lam(nat.clone(), Term::Var(0));
        let expected = Term::apps(
            Term::cnst(name("Fiber"), vec![Level::of_nat(1)]),
            [nat.clone(), nat.clone(), id_fn, nat.clone()],
        );
        let _ = nat;
        let mut ctx = crate::check::LocalCtx::new();
        assert!(chk.check(&mut ctx, &bogus, &expected).is_err());
    }
}
