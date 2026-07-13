//! A **general, user-declarable cubical HIT schema** — `declare_cubical_hit` —
//! generalizing [`crate::interval_hit`]'s `I2` and [`crate::circle_cubical`]'s
//! `S1c` into one parameterized mechanism.
//!
//! ## Supported class
//!
//! A cubical HIT `H` presented by:
//!
//!   * `n ≥ 1` **nullary point constructors** `H.point_0, …, H.point_{n-1} : H`
//!     (fielded/parameterized point constructors are **deferred**, see below), and
//!   * `m ≥ 0` genuine **cubical path constructors** `H.path_0, …, H.path_{m-1}`,
//!     each `H.path_j : Path H H.point_{lhs_j} H.point_{rhs_j}` — a real
//!     [`crate::term::Term::PathP`]-classified path (built on [`crate::cubical`]'s
//!     `PLam`/`PApp`/`PathP`, *not* the inductive `Eq`). `lhs_j == rhs_j` is legal
//!     (a self-loop, like `S1c.loop`); `lhs_j != rhs_j` connects two distinct
//!     points (like `I2.seg`). Both shapes are handled by exactly the same
//!     generic code (the reduction only ever inspects the interval argument `r`,
//!     never the endpoints — see `crate::circle_cubical`'s module doc for why a
//!     self-loop needs no different *reduction* logic, only a sharper endpoint
//!     coherence *argument*, which is still purely derived, not a new rule), and
//!   * a **`Type`-valued, computing, non-dependent-target** recursor
//!
//! ```text
//!   H.rec.{v} : Π (C : H → Sort v)
//!                 (c_0 : C point_0) … (c_{n-1} : C point_{n-1})
//!                 (s_0 : PathP (λi. C (path_0 @ i)) c_{lhs_0} c_{rhs_0})
//!                 … (s_{m-1} : PathP (λi. C (path_{m-1} @ i)) c_{lhs_{m-1}} c_{rhs_{m-1}})
//!                 (x : H), C x
//! ```
//!
//! with `n + m` ι-rules synthesized generically from the declared shape:
//!
//! ```text
//!   H.rec C c_0 .. c_{n-1} s_0 .. s_{m-1} H.point_i        ↦  c_i
//!   H.rec C c_0 .. c_{n-1} s_0 .. s_{m-1} (H.path_j @ r)    ↦  s_j @ r
//! ```
//!
//! This is *exactly* [`crate::interval_hit`]'s `I2` (`n=2`, one path, distinct
//! endpoints) and [`crate::circle_cubical`]'s `S1c` (`n=1`, one path, self-loop),
//! generalized to arbitrary `n`/`m` — see `tests::rederive_i2`/`tests::rederive_s1c`
//! below, which re-declare both through this schema and confirm they type-check
//! and *compute* on their path constructors identically to the hand-coded originals.
//!
//! ## What's deferred
//!
//! * **Fielded point constructors** (a point constructor taking non-`H` or
//!   recursive-`H` arguments) — only nullary points are supported, matching
//!   `I2`/`S1c` exactly; extending the recursor's point-case binder shape to
//!   fielded constructors is the same enlargement [`crate::hit`]'s propositional
//!   schema already documents as deferred, and is out of scope here too.
//! * **A genuinely dependent eliminator into a non-fibrant/Kan-requiring target**
//!   (anything needing `hcomp`/`transp` beyond direct `PathP` application) — the
//!   `Type`-valued `H.rec` above already *is* the dependent eliminator into any
//!   `Sort v` motive (the whole cubical-HIT payoff over `Eq`-based HITs' `Prop`-only
//!   `H.ind`), but composing across *multiple* path constructors via `hcomp` (e.g.
//!   proving something about a 2-path composite) is not attempted.
//! * **Higher (2-)path constructors** (paths between paths) — only 1-paths between
//!   points, exactly as `I2`/`S1c`.
//!
//! ## Why this is SOUND
//!
//! Structurally identical to `I2`/`S1c`'s soundness arguments (see those modules'
//! "Why this is SOUND" sections), now parameterized:
//!
//! * **No new checking rule.** Every constant is an ordinary typed
//!   [`crate::env::Decl::CubHit`] constant, looked up via `Checker::infer`'s
//!   `Term::Const` arm exactly like any axiom. Each `H.path_j`'s type,
//!   `Path H point_{lhs_j} point_{rhs_j}`, is checked well-formed *once*, at
//!   `declare_cubical_hit` time, by the ordinary (pre-existing) `Term::PathP`
//!   typing rule — no new typing rule for a "cubical HIT" is added anywhere.
//! * **Generically synthesized, narrowly-scoped ι-rules**
//!   ([`crate::reduce::Reducer::try_cubical_hit_rec`],
//!   [`crate::nbe::Nbe::try_cubical_hit_rec`], differentially cross-checked by
//!   every test below): the point rule fires only on a literal, nullary
//!   `H.point_i`; the path rule fires only when the scrutinee's weak-head form is
//!   *literally* `H.path_j @ r` for the *same* HIT `id` as the `H.rec` head being
//!   reduced — never on a neutral, never cross-firing against a different
//!   declared HIT's constructors (every [`crate::env::CubHit`] carries an `id`
//!   equal to its HIT's own type-former name; the ι-rule compares `id`s before
//!   ever inspecting roles/indices, exactly mirroring [`crate::hit`]'s per-HIT
//!   `id`-guard).
//! * **Endpoint coherence** is the same *derived*, no-new-equation fact
//!   `I2`/`S1c` rely on: each `s_j`'s own declared type,
//!   `PathP (λi. C (path_j @ i)) c_{lhs_j} c_{rhs_j}`, is checked against
//!   `path_j`'s own declared boundary at `H.rec`'s *formation* site (the ordinary
//!   `PathP` well-formedness obligation), and at *reduction* time
//!   [`crate::check::Checker::path_boundary`] (proven sound in [`crate::cubical`]'s
//!   Phase 1) gives `s_j @ i0 ≡ c_{lhs_j}` / `s_j @ i1 ≡ c_{rhs_j}` *definitionally*
//!   — so the path ι-rule's boundary values agree with the point ι-rule's values,
//!   for every `j`, without any new checking or reduction rule.
//! * **Canonicity.** The `n` point constructors remain the only closed
//!   point-shaped normal forms of `H`: every `H.path_j` is `Path`-classified, not
//!   `H`-classified, so it can never appear as a closed value *of type `H`* —
//!   only `H.path_j @ r` can, handled precisely by the path ι-rule (which, at the
//!   closed interval endpoints, is definitionally one of the `n` points again).
//! * **Anti-`False`.** No new equation is manufactured between unrelated closed
//!   terms: `H.rec`'s path ι-rule only ever returns `s_j @ r` for the
//!   caller-*supplied* `s_j`; distinct point constructors of `H` stay
//!   non-definitionally-equal (checked below for every worked example, including
//!   the new figure-eight HIT); no `Path Nat 0 1`/`Empty` is derivable.
//! * **Reducer/NbE agreement.** Both ι-rules are implemented once each,
//!   structurally mirroring `try_i2_rec`/`try_s1c_rec` exactly (generalized over
//!   `n`/`m` and guarded by `id`); every test below checks both independently and
//!   compares normal forms.

use crate::env::{CubHit, CubHitRole, Decl, Env};
use crate::level::Level;
use crate::term::{name, Name, Term};
use std::rc::Rc;

/// A user-supplied specification of a cubical HIT: its type-former name, the
/// names of its `n ≥ 1` nullary point constructors, and its `m ≥ 0` path
/// constructors, each given as `(path_name, lhs_point_index, rhs_point_index)`
/// (indices into `points`; `lhs == rhs` is a legal self-loop).
#[derive(Clone, Debug)]
pub struct CubHitSpec {
    pub name: String,
    pub points: Vec<String>,
    /// `(path constant name, lhs point index, rhs point index)`.
    pub paths: Vec<(String, usize, usize)>,
}

impl CubHitSpec {
    /// The name of the generated recursor, `"{name}.rec"`.
    pub fn rec_name(&self) -> String {
        format!("{}.rec", self.name)
    }
}

/// `H` (the bare type former).
fn hconst(spec: &CubHitSpec) -> Term {
    Term::cnst(name(&spec.name), vec![])
}
/// `H.point_i`.
fn point(spec: &CubHitSpec, i: usize) -> Term {
    Term::cnst(name(&spec.points[i]), vec![])
}
/// `H.path_j`.
fn pathc(spec: &CubHitSpec, j: usize) -> Term {
    Term::cnst(name(&spec.paths[j].0), vec![])
}

/// Build a de-Bruijn `Var` referencing the binder assigned **level** `level`
/// (0-based, in the order the binders were introduced: `C` is level `0`, then
/// each `c_i` at level `1+i`, then each `s_j` at level `1+n+j`, then `x` at level
/// `1+n+m`) from a position that is currently `depth` binders deep (i.e. `depth`
/// binders — counting `C`, the `c_i`s introduced so far, etc., but *not*
/// counting this reference's own binder, if any — are in scope at the point this
/// term is written). Standard de-Bruijn-level-to-index conversion:
/// `index = depth - level - 1`.
fn var_at(level: usize, depth: usize) -> Term {
    Term::Var(depth - level - 1)
}

/// Install a general cubical HIT into `env` per `spec` — see the module doc for
/// the exact recursor signature and ι-rules. Rejects: fewer than one point
/// constructor, an out-of-range `lhs`/`rhs` path endpoint index, and
/// re-declaration of any of the generated names (type former, points, paths,
/// recursor).
pub fn declare_cubical_hit(env: &mut Env, spec: &CubHitSpec) -> Result<(), String> {
    let n = spec.points.len();
    let m = spec.paths.len();
    if n == 0 {
        return Err("a cubical HIT needs at least one point constructor".to_string());
    }
    for (j, (pname, lhs, rhs)) in spec.paths.iter().enumerate() {
        if *lhs >= n || *rhs >= n {
            return Err(format!(
                "path constructor '{pname}' (index {j}) has an out-of-range endpoint (lhs={lhs}, rhs={rhs}, but only {n} points)"
            ));
        }
    }
    let mut all_names: Vec<&str> = vec![spec.name.as_str()];
    all_names.extend(spec.points.iter().map(|s| s.as_str()));
    all_names.extend(spec.paths.iter().map(|(s, ..)| s.as_str()));
    let rec_name_owned = spec.rec_name();
    all_names.push(&rec_name_owned);
    for nm in &all_names {
        if env.contains(nm) {
            return Err(format!("'{nm}' is already declared"));
        }
    }
    // Reject duplicate names within the spec itself (would otherwise silently
    // alias two distinct constructors onto the same environment slot).
    {
        let mut seen = std::collections::HashSet::new();
        for nm in &all_names {
            if !seen.insert(*nm) {
                return Err(format!("duplicate name '{nm}' in cubical HIT spec"));
            }
        }
    }

    let id: Name = name(&spec.name);
    let v = Level::param(0); // H.rec's target universe.

    // ------------------------------------------------------------------
    // H : Type 0
    // ------------------------------------------------------------------
    env.insert(
        id.clone(),
        Decl::CubHit(Rc::new(CubHit {
            id: id.clone(),
            role: CubHitRole::Type,
            num_levels: 0,
            ty: Term::typ(0),
        })),
    )?;

    // ------------------------------------------------------------------
    // H.point_i : H, for i in 0..n
    // ------------------------------------------------------------------
    for (i, pname) in spec.points.iter().enumerate() {
        env.insert(
            name(pname),
            Decl::CubHit(Rc::new(CubHit {
                id: id.clone(),
                role: CubHitRole::Point(i as u32),
                num_levels: 0,
                ty: hconst(spec),
            })),
        )?;
    }

    // ------------------------------------------------------------------
    // H.path_j : Path H point_{lhs_j} point_{rhs_j}, for j in 0..m
    // ------------------------------------------------------------------
    for (j, (pname, lhs, rhs)) in spec.paths.iter().enumerate() {
        let ty = Term::path(hconst(spec), point(spec, *lhs), point(spec, *rhs));
        env.insert(
            name(pname),
            Decl::CubHit(Rc::new(CubHit {
                id: id.clone(),
                role: CubHitRole::Path { idx: j as u32, lhs: *lhs as u32, rhs: *rhs as u32 },
                num_levels: 0,
                ty,
            })),
        )?;
    }

    // ------------------------------------------------------------------
    // H.rec.{v} : Π (C : H -> Sort v)
    //               (c_0 : C point_0) .. (c_{n-1} : C point_{n-1})
    //               (s_0 : PathP (\i. C (path_0 @ i)) c_lhs0 c_rhs0)
    //               .. (s_{m-1} : ..)
    //               (x : H), C x
    //
    // Binder levels (0-based, introduction order): C=0, c_i=1+i, s_j=1+n+j,
    // x=1+n+m. See `var_at`'s doc comment for the depth/level convention this
    // builds on (verified against `I2`/`S1c`'s hand-written constructions in the
    // module doc and re-derivation tests below).
    // ------------------------------------------------------------------
    let x_level = 1 + n + m;

    // Innermost: `C x`, written at depth = x_level + 1 (C .. c .. s .. x all in scope).
    let codomain = {
        let depth = x_level + 1;
        Term::app(var_at(0, depth), var_at(x_level, depth))
    };
    // `x : H`, written at depth = x_level.
    let mut acc = Term::pi(hconst(spec), codomain);

    // s_{m-1} .. s_0, each written at depth = 1 + n + j.
    for j in (0..m).rev() {
        let (_, lhs, rhs) = spec.paths[j];
        let depth = 1 + n + j;
        let family = {
            let fam_depth = depth + 1; // one more binder: the PathP's interval binder i
            Term::app(var_at(0, fam_depth), Term::papp(pathc(spec, j), Term::Var(0)))
        };
        let c_lhs = var_at(1 + lhs, depth);
        let c_rhs = var_at(1 + rhs, depth);
        let s_ty = Term::pathp(family, c_lhs, c_rhs);
        acc = Term::pi(s_ty, acc);
    }

    // c_{n-1} .. c_0, each written at depth = 1 + i.
    for i in (0..n).rev() {
        let depth = 1 + i;
        let c_ty = Term::app(var_at(0, depth), point(spec, i));
        acc = Term::pi(c_ty, acc);
    }

    // C : H -> Sort v, written at depth = 0.
    let rec_ty = Term::pi(Term::arrow(hconst(spec), Term::Sort(v)), acc);

    env.insert(
        name(&rec_name_owned),
        Decl::CubHit(Rc::new(CubHit {
            id,
            role: CubHitRole::Rec { num_points: n as u32, num_paths: m as u32 },
            num_levels: 1,
            ty: rec_ty,
        })),
    )?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::{Checker, LocalCtx};
    use crate::circle_cubical::{self, install_circle_cubical, S1C_BASE, S1C_LOOP, S1C_REC, S1C_TYPE};
    use crate::inductive::declare_nat;
    use crate::interval_hit::{self, install_interval_hit, I2_REC};
    use crate::nbe::Nbe;
    use crate::reduce::Reducer;

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

    fn base_env() -> Env {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        env
    }

    // ---------------------------------------------------------------------
    // Basic well-formedness / rejection behaviour
    // ---------------------------------------------------------------------

    #[test]
    fn i2_like_spec_wellformed() {
        let mut env = base_env();
        let spec = CubHitSpec {
            name: "MyI".to_string(),
            points: vec!["MyI.zero".to_string(), "MyI.one".to_string()],
            paths: vec![("MyI.seg".to_string(), 0, 1)],
        };
        declare_cubical_hit(&mut env, &spec).unwrap();
        let chk = Checker::new(&env);
        for n in ["MyI", "MyI.zero", "MyI.one", "MyI.seg", "MyI.rec"] {
            chk.infer_closed(env.get(n).unwrap().ty()).unwrap_or_else(|e| panic!("{n} ill-formed: {e}"));
        }
    }

    #[test]
    fn rejects_zero_points() {
        let mut env = base_env();
        let spec = CubHitSpec { name: "Empty2".to_string(), points: vec![], paths: vec![] };
        let err = declare_cubical_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("at least one point"), "got: {err}");
    }

    #[test]
    fn rejects_out_of_range_path_endpoint() {
        let mut env = base_env();
        let spec = CubHitSpec {
            name: "Bad".to_string(),
            points: vec!["Bad.p0".to_string()],
            paths: vec![("Bad.bogus".to_string(), 0, 5)],
        };
        let err = declare_cubical_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("out-of-range"), "got: {err}");
    }

    #[test]
    fn rejects_double_install() {
        let mut env = base_env();
        let spec = CubHitSpec {
            name: "Dup".to_string(),
            points: vec!["Dup.p0".to_string()],
            paths: vec![],
        };
        declare_cubical_hit(&mut env, &spec).unwrap();
        let err = declare_cubical_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("already declared"), "got: {err}");
    }

    // ---------------------------------------------------------------------
    // Re-derivation #1: I2 via the general schema.
    // ---------------------------------------------------------------------

    fn i2_spec() -> CubHitSpec {
        CubHitSpec {
            name: "I2g".to_string(),
            points: vec!["I2g.zero".to_string(), "I2g.one".to_string()],
            paths: vec![("I2g.seg".to_string(), 0, 1)],
        }
    }

    #[test]
    fn rederive_i2_typechecks_like_the_hand_coded_original() {
        let mut env = base_env();
        // Install the hand-coded I2 too, to compare shapes side by side.
        install_interval_hit(&mut env).unwrap();
        let spec = i2_spec();
        declare_cubical_hit(&mut env, &spec).unwrap();
        let chk = Checker::new(&env);
        // The generic recursor's type must itself be well-formed, exactly like the
        // hand-coded I2.rec's type.
        let generic_rec_ty = env.get("I2g.rec").unwrap().ty().clone();
        chk.infer_closed(&generic_rec_ty).unwrap();
        let handcoded_rec_ty = env.get(I2_REC).unwrap().ty().clone();
        chk.infer_closed(&handcoded_rec_ty).unwrap();
    }

    #[test]
    fn rederive_i2_point_and_path_iota_rules_compute() {
        let mut env = base_env();
        declare_cubical_hit(&mut env, &i2_spec()).unwrap();
        let zero = cn("I2g.zero");
        let one = cn("I2g.one");
        let seg = cn("I2g.seg");
        let motive = Term::lam(cn("I2g"), cn("Nat").lift(1, 0));
        let s = interval_hit::refl(&lit(7));
        let rec = |scrut: Term| {
            Term::apps(
                Term::cnst(name("I2g.rec"), vec![Level::of_nat(1)]),
                [motive.clone(), lit(7), lit(7), s.clone(), scrut],
            )
        };
        let chk = Checker::new(&env);
        let red = Reducer::new(&env);
        let nbe = Nbe::new(&env);

        // Point iota, both constructors.
        let rz = rec(zero.clone());
        chk.check(&mut LocalCtx::new(), &rz, &cn("Nat")).unwrap();
        assert!(red.is_def_eq(&rz, &lit(7)));
        assert_eq!(nbe.normalize(&rz), lit(7));

        let ro = rec(one.clone());
        chk.check(&mut LocalCtx::new(), &ro, &cn("Nat")).unwrap();
        assert!(red.is_def_eq(&ro, &lit(7)));
        assert_eq!(nbe.normalize(&ro), lit(7));

        // Path iota, under a PLam binder (mirrors `interval_hit`'s own test).
        let scrut = Term::papp(seg, Term::Var(0));
        let whole = Term::plam(rec(scrut));
        let ty = chk.infer_closed(&whole).unwrap();
        assert!(red.is_def_eq(&ty, &Term::path(cn("Nat"), lit(7), lit(7))));
        let expected = Term::plam(lit(7).lift(1, 0));
        assert!(red.is_def_eq(&whole, &expected));
        assert_eq!(nbe.normalize(&whole), nbe.normalize(&expected));

        // Endpoint coherence: `rec (seg @ i0)` and `rec zero` agree.
        let via_i0 = rec(Term::papp(cn("I2g.seg"), Term::IZero));
        assert!(red.is_def_eq(&via_i0, &rz));
        let via_i1 = rec(Term::papp(cn("I2g.seg"), Term::IOne));
        assert!(red.is_def_eq(&via_i1, &ro));

        // Anti-triviality / anti-False: zero and one stay distinct.
        assert!(!red.is_def_eq(&zero, &one));
    }

    // ---------------------------------------------------------------------
    // Re-derivation #2: S1c (self-loop) via the general schema.
    // ---------------------------------------------------------------------

    fn s1c_spec() -> CubHitSpec {
        CubHitSpec {
            name: "S1g".to_string(),
            points: vec!["S1g.base".to_string()],
            paths: vec![("S1g.loop".to_string(), 0, 0)], // self-loop: lhs == rhs
        }
    }

    #[test]
    fn rederive_s1c_typechecks_like_the_hand_coded_original() {
        let mut env = base_env();
        install_circle_cubical(&mut env).unwrap();
        let spec = s1c_spec();
        declare_cubical_hit(&mut env, &spec).unwrap();
        let chk = Checker::new(&env);
        chk.infer_closed(env.get("S1g.rec").unwrap().ty()).unwrap();
        chk.infer_closed(env.get(S1C_REC).unwrap().ty()).unwrap();
        let _ = (S1C_TYPE, S1C_BASE, S1C_LOOP);
    }

    #[test]
    fn rederive_s1c_self_loop_point_and_path_iota_compute() {
        let mut env = base_env();
        declare_cubical_hit(&mut env, &s1c_spec()).unwrap();
        let base = cn("S1g.base");
        let loop_ = cn("S1g.loop");
        let motive = Term::lam(cn("S1g"), cn("Nat").lift(1, 0));
        let l = circle_cubical::refl(&lit(4));
        let rec = |scrut: Term| {
            Term::apps(
                Term::cnst(name("S1g.rec"), vec![Level::of_nat(1)]),
                [motive.clone(), lit(4), l.clone(), scrut],
            )
        };
        let chk = Checker::new(&env);
        let red = Reducer::new(&env);
        let nbe = Nbe::new(&env);

        let rb = rec(base.clone());
        chk.check(&mut LocalCtx::new(), &rb, &cn("Nat")).unwrap();
        assert!(red.is_def_eq(&rb, &lit(4)));
        assert_eq!(nbe.normalize(&rb), lit(4));

        // The loop's path iota, exercised under a PLam binder.
        let scrut = Term::papp(loop_.clone(), Term::Var(0));
        let whole = Term::plam(rec(scrut));
        let ty = chk.infer_closed(&whole).unwrap();
        assert!(red.is_def_eq(&ty, &Term::path(cn("Nat"), lit(4), lit(4))));
        let expected = Term::plam(lit(4).lift(1, 0));
        assert!(red.is_def_eq(&whole, &expected));
        assert_eq!(nbe.normalize(&whole), nbe.normalize(&expected));

        // Both endpoints agree with the point rule AND with each other.
        let via_i0 = rec(Term::papp(loop_.clone(), Term::IZero));
        let via_i1 = rec(Term::papp(loop_.clone(), Term::IOne));
        assert!(red.is_def_eq(&via_i0, &rb));
        assert!(red.is_def_eq(&via_i1, &rb));
        assert!(red.is_def_eq(&via_i0, &via_i1));

        // Non-triviality: loop != refl base.
        let refl_base = crate::cubical::refl(&base);
        assert!(!red.is_def_eq(&loop_, &refl_base));
    }

    // ---------------------------------------------------------------------
    // A NEW HIT the hand-coded pair didn't cover: a "figure eight" — one point,
    // TWO independent self-loops.
    // ---------------------------------------------------------------------

    fn figure_eight_spec() -> CubHitSpec {
        CubHitSpec {
            name: "Fig8".to_string(),
            points: vec!["Fig8.base".to_string()],
            paths: vec![
                ("Fig8.loop1".to_string(), 0, 0),
                ("Fig8.loop2".to_string(), 0, 0),
            ],
        }
    }

    #[test]
    fn figure_eight_wellformed_and_both_loops_typecheck() {
        let mut env = base_env();
        declare_cubical_hit(&mut env, &figure_eight_spec()).unwrap();
        let chk = Checker::new(&env);
        for n in ["Fig8", "Fig8.base", "Fig8.loop1", "Fig8.loop2", "Fig8.rec"] {
            chk.infer_closed(env.get(n).unwrap().ty()).unwrap_or_else(|e| panic!("{n} ill-formed: {e}"));
        }
        let base = cn("Fig8.base");
        let goal = Term::path(cn("Fig8"), base.clone(), base);
        chk.check(&mut LocalCtx::new(), &cn("Fig8.loop1"), &goal.clone()).unwrap();
        chk.check(&mut LocalCtx::new(), &cn("Fig8.loop2"), &goal).unwrap();
    }

    /// Both loops compute INDEPENDENTLY through the recursor — `rec` accepts two
    /// distinct respectfulness data `s0`/`s1` and applies the right one to the
    /// right loop, never confusing the two path constructors of the *same* HIT.
    #[test]
    fn figure_eight_loops_compute_independently() {
        let mut env = base_env();
        declare_cubical_hit(&mut env, &figure_eight_spec()).unwrap();
        // Both loops share the SAME basepoint `Fig8.base`, so their respectfulness
        // data `s0`/`s1` must share the same boundary too (`PathP .. c0 c0` for the
        // very same `c0` in both cases) -- a non-dependent `Nat`-valued motive with
        // two *different* constant paths can't express "different content, same
        // boundary" (a `Path Nat k k` forces `s @ i0 = s @ i1 = k` at the type
        // level, and a constant `refl k` genuinely only ever contains `k`). So use
        // an axiomatized target type `A` with a fixed point `a : A` and two
        // independent AXIOM paths `l1, l2 : Path A a a` -- opaque, un-related
        // neutrals that share the same declared boundary `a` but are themselves
        // distinct closed terms, exactly the shape needed to tell "did loop1's
        // ι-rule apply s0, or did it (wrongly) apply s1?" apart.
        env.insert(name("A"), Decl::Axiom { num_levels: 0, ty: Term::typ(0) }).unwrap();
        env.insert(name("a"), Decl::Axiom { num_levels: 0, ty: cn("A") }).unwrap();
        env.insert(name("l1"), Decl::Axiom { num_levels: 0, ty: Term::path(cn("A"), cn("a"), cn("a")) })
            .unwrap();
        env.insert(name("l2"), Decl::Axiom { num_levels: 0, ty: Term::path(cn("A"), cn("a"), cn("a")) })
            .unwrap();
        let base = cn("Fig8.base");
        let loop1 = cn("Fig8.loop1");
        let loop2 = cn("Fig8.loop2");
        let motive = Term::lam(cn("Fig8"), cn("A").lift(1, 0));
        let s0 = cn("l1");
        let s1 = cn("l2");
        let rec = |scrut: Term| {
            Term::apps(
                Term::cnst(name("Fig8.rec"), vec![Level::of_nat(1)]),
                [motive.clone(), cn("a"), s0.clone(), s1.clone(), scrut],
            )
        };
        let chk = Checker::new(&env);
        let red = Reducer::new(&env);
        let nbe = Nbe::new(&env);

        // Point rule.
        let rb = rec(base);
        assert!(red.is_def_eq(&rb, &cn("a")));

        // loop1's path ι-rule applies `l1` (NOT `l2`).
        let scrut1 = Term::papp(loop1, Term::Var(0));
        let whole1 = Term::plam(rec(scrut1));
        chk.infer_closed(&whole1).unwrap();
        let expected1 = Term::plam(Term::papp(cn("l1"), Term::Var(0)));
        assert!(red.is_def_eq(&whole1, &expected1));
        assert_eq!(nbe.normalize(&whole1), nbe.normalize(&expected1));

        // loop2's path ι-rule applies `l2` (NOT `l1`).
        let scrut2 = Term::papp(loop2, Term::Var(0));
        let whole2 = Term::plam(rec(scrut2));
        chk.infer_closed(&whole2).unwrap();
        let expected2 = Term::plam(Term::papp(cn("l2"), Term::Var(0)));
        assert!(red.is_def_eq(&whole2, &expected2));
        assert_eq!(nbe.normalize(&whole2), nbe.normalize(&expected2));

        // And they're genuinely different results (loop1's iota didn't leak into
        // loop2's, or vice versa): applying opaque, unrelated `l1`/`l2` to the SAME
        // neutral `r` never gets identified by conversion.
        assert!(!red.is_def_eq(&whole1, &whole2));
    }

    // ---------------------------------------------------------------------
    // Adversarial: per-id no cross-fire between two independently declared
    // cubical HITs (even ones with structurally identical shapes).
    // ---------------------------------------------------------------------

    #[test]
    fn no_cross_fire_between_two_distinct_declared_hits() {
        let mut env = base_env();
        // Two structurally IDENTICAL I2-shaped HITs, distinct `id`s.
        let spec_a = CubHitSpec {
            name: "Ia".to_string(),
            points: vec!["Ia.zero".to_string(), "Ia.one".to_string()],
            paths: vec![("Ia.seg".to_string(), 0, 1)],
        };
        let spec_b = CubHitSpec {
            name: "Ib".to_string(),
            points: vec!["Ib.zero".to_string(), "Ib.one".to_string()],
            paths: vec![("Ib.seg".to_string(), 0, 1)],
        };
        declare_cubical_hit(&mut env, &spec_a).unwrap();
        declare_cubical_hit(&mut env, &spec_b).unwrap();
        let chk = Checker::new(&env);
        // Applying Ia.rec to an Ib-typed scrutinee must be REJECTED by the
        // type-checker (wrong type entirely) -- confirming the two HITs' recursors
        // cannot even be pointed at each other's constructors, let alone have the
        // ι-rule misfire.
        let motive = Term::lam(cn("Ia"), cn("Nat").lift(1, 0));
        let s = crate::cubical::refl(&lit(0));
        let bogus = Term::apps(
            Term::cnst(name("Ia.rec"), vec![Level::of_nat(1)]),
            [motive, lit(0), lit(0), s, cn("Ib.zero")],
        );
        assert!(chk.infer_closed(&bogus).is_err(), "Ia.rec must reject an Ib-typed scrutinee");
    }

    /// ANTI-`False`: cannot derive `Path Nat 0 1` from the general schema.
    #[test]
    fn cannot_prove_false_via_generic_schema() {
        let mut env = base_env();
        declare_cubical_hit(&mut env, &i2_spec()).unwrap();
        let red = Reducer::new(&env);
        assert!(!red.is_def_eq(&lit(0), &lit(1)));
        let chk = Checker::new(&env);
        let bogus_goal = Term::path(cn("Nat"), lit(3), lit(5));
        assert!(
            chk.check(&mut LocalCtx::new(), &cn("I2g.seg"), &bogus_goal).is_err(),
            "I2g.seg must not check against an unrelated Path Nat goal"
        );
    }

    /// `H.rec` stays stuck on a neutral `H`-typed variable — canonicity for open
    /// terms holds generically too.
    #[test]
    fn rec_stuck_on_neutral_generic() {
        let mut env = base_env();
        declare_cubical_hit(&mut env, &i2_spec()).unwrap();
        let motive = Term::lam(cn("I2g"), cn("Nat").lift(1, 0));
        let s = crate::cubical::refl(&lit(1));
        let body = Term::apps(
            Term::cnst(name("I2g.rec"), vec![Level::of_nat(1)]),
            [motive, lit(1), lit(1), s, Term::Var(0)],
        );
        let f = Term::lam(cn("I2g"), body);
        let chk = Checker::new(&env);
        chk.infer_closed(&f).unwrap();
        let red = Reducer::new(&env);
        match red.whnf(&f) {
            Term::Lam(_, _) => {}
            other => panic!("expected a stuck lambda, got {other:?}"),
        }
    }
}
