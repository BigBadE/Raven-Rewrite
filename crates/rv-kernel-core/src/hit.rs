//! A **general, user-declarable schema for 1-HITs** (one-dimensional higher-inductive
//! types), generalizing the shared pattern hand-coded three times already in this
//! kernel — [`crate::quotient`]'s `Quot`, [`crate::trunc`]'s `Trunc`, and
//! [`crate::circle`]'s `S¹` — into a single API, [`declare_hit`], that lets a *user*
//! declare their own 1-HIT by naming its point and path constructors.
//!
//! ## The schema
//!
//! A declared HIT `H` is presented by [`HitSpec`]:
//!
//!   * a type former `H : Type 0` (fixed universe, non-parametric — see "Supported
//!     class" below for why),
//!   * `n ≥ 1` **point constructors** `H.p_0, …, H.p_{n-1} : H`, each **nullary** (no
//!     fields, recursive or not),
//!   * `m ≥ 0` **path constructors** `H.e_0, …, H.e_{m-1}`, where `H.e_j : Eq H
//!     H.p_{lhs_j} H.p_{rhs_j}` for point-constructor indices `lhs_j, rhs_j` chosen by
//!     the user — a propositional identification between two (possibly equal, for a
//!     self-loop) point constructors, holding only through the existing [`Eq`]
//!     inductive, never definitionally (no interval/cubical machinery).
//!
//! `declare_hit` synthesizes and installs, generically in `n` and `m`:
//!
//! ```text
//!   H          : Type 0
//!   H.p_i      : H                                              (i = 0..n)
//!   H.e_j      : Eq.{1} H H.p_{lhs_j} H.p_{rhs_j}                (j = 0..m)
//!   H.rec.{v}  : Π (P : Sort v)
//!                  (case_0 : P) … (case_{n-1} : P)
//!                  (resp_0 : Eq.{v} P case_{lhs_0} case_{rhs_0})
//!                  …
//!                  (resp_{m-1} : Eq.{v} P case_{lhs_{m-1}} case_{rhs_{m-1}}),
//!                H → P
//!   H.ind      : Π (β : H → Prop) (h_0 : β H.p_0) … (h_{n-1} : β H.p_{n-1}),
//!                Π (t : H), β t
//! ```
//!
//! with the **`n` point-constructor ι-rules**, added generically to both the trusted
//! [`crate::reduce`] and the fast [`crate::nbe`] (differentially checked in tests):
//!
//! ```text
//!   H.rec.{v} P case_0 … case_{n-1} resp_0 … resp_{m-1} (H.p_i)  ↦  case_i
//! ```
//!
//! This is *exactly* the shape [`crate::circle`] and [`crate::trunc`] each hand-wrote
//! once (point ctor(s) + path ctor(s) + a recursor with one respectfulness premise per
//! path constructor, ι firing only on point constructors) — `declare_hit` synthesizes
//! it for an arbitrary user-chosen `n` and `m`, the way `rv_kernel::generate` synthesizes
//! an ordinary inductive's recursor from its declared constructors.
//!
//! ## Why this is SOUND
//!
//! The soundness argument is structurally identical to [`crate::circle`]'s (itself
//! following [`crate::trunc`]/[`crate::quotient`]), generalized from one point/one path
//! to `n` points/`m` paths:
//!
//! * **Point constructors never become definitionally equal via paths.** Each `H.e_j`
//!   is an axiom-shaped constant of type `Eq H H.p_{lhs_j} H.p_{rhs_j}` with **no**
//!   reduction rule — nothing makes it reduce to `Eq.refl`, and nothing reduces `H.p_i`
//!   because of it. The point constructors remain `n` distinct, stable canonical
//!   values; conversion never merges two of them (adversarial test
//!   `points_stay_distinct`, `path_does_not_reduce_to_refl`).
//! * **The ι-rule fires ONLY on a literal point constructor**, never on a path
//!   constructor or a neutral. [`try_hit_rec`] in `reduce.rs`/`nbe.rs` weak-head
//!   reduces the scrutinee and matches its head against a `HitRole::Point` **of the
//!   same `id`** — a path constructor's type is `Eq H _ _`, not `H`, so it can never
//!   even *appear* as a well-typed `H.rec` scrutinee (adversarial test
//!   `rec_does_not_fire_on_path`); a scrutinee from a *different* declared HIT is
//!   rejected by the `id` guard even though both may share a role tag (adversarial
//!   test `rec_does_not_cross_fire_between_hits`).
//! * **Respectfulness is checked, not trusted.** `resp_j : Eq P case_{lhs_j}
//!   case_{rhs_j}` must type-check *before* `H.rec` can be formed at all; the ι-rule
//!   discards it at reduction time exactly as `Quot.lift`/`Trunc.lift`/`S¹.rec`
//!   discard their `resp`/`lp` — soundness comes from `resp_j` having been checked to
//!   *exist*, never from it being inspected computationally. A mismatched `resp_j`
//!   (wrong `case`s, wrong direction) is rejected by ordinary type-checking
//!   (adversarial test `mismatched_resp_rejected`).
//! * **`H.ind` eliminates only into `Prop`**, with no computation rule; proof
//!   irrelevance makes the missing `ind (H.p_i) ↦ h_i` reduction unobservable and
//!   confines the dependent eliminator to the one universe where respecting every path
//!   constructor is automatic (any two proofs of `β t` are already definitionally
//!   equal). A `Type`-valued dependent eliminator is **not** offered (see below).
//! * **Positivity is enforced by construction**: every point constructor is *nullary*
//!   — there is no field of any kind, so strict positivity is trivially satisfied (no
//!   recursive occurrence exists to be checked). A hypothetical non-nullary point
//!   constructor is simply not expressible through [`HitSpec`] (adversarial test
//!   `spec_rejects_bad_path_index` covers the one other way a spec can be malformed —
//!   an out-of-range path endpoint — which is rejected before any constant is
//!   installed).
//!
//! ## Supported class and restrictions (read this before relying on this module)
//!
//! `declare_hit` supports exactly:
//!
//!   * **non-indexed, non-parametric** HITs: `H : Type 0` only — no `H : Π params,
//!     Type` (a general schema would need to reuse the ordinary inductive-declaration
//!     machinery in [`crate::inductive`]/`rv_kernel::mutual` for a parametric point
//!     layer; layering path constructors and a joint recursor on top of *that* is a
//!     materially larger change, left as future work exactly as [`crate::circle`]
//!     recommends);
//!   * **nullary point constructors only** — no recursive or non-recursive fields.
//!     This is the one restriction beyond what [`crate::circle`] already accepts (`S¹`
//!     has exactly one nullary point constructor, `base`); `declare_hit` generalizes
//!     the *count* of point constructors but not their arity. Fields would require
//!     substituting field variables into the ι-reduct and into path-constructor
//!     endpoints, and would put positivity-checking of point constructors back in
//!     scope for real — both are sound in principle (ordinary inductive constructors
//!     already handle exactly this) but are a materially larger change than the
//!     schema-generalization asked for here;
//!   * **path constructors between two (possibly equal) point constructors** — i.e.
//!     `Eq H H.p_i H.p_j`, not an arbitrary closed term of type `H`, and not a path
//!     between *terms built from* several point constructors applied to arguments
//!     (moot here since point constructors are nullary — every closed first-order term
//!     of type `H` *is* some `H.p_i`, so this already covers "paths between
//!     closed/first-order point terms" in full for this arity-0 class);
//!   * **eliminators**: the non-dependent `H.rec` (into any `Sort v`, one
//!     respectfulness premise per declared path constructor) and the dependent,
//!     `Prop`-only `H.ind` (no premise needed, by proof irrelevance). A dependent,
//!     `Type`-valued eliminator — the genuine HIT induction principle needing a
//!     transport datum `Π (l : Eq (P over e_j) …)` for each path constructor — is
//!     **not** offered, for the same reason [`crate::circle`]/[`crate::trunc`] omit
//!     it: getting the dependent computation/subject-reduction interaction right for
//!     an arbitrary path shape, without an interval, is delicate enough that an
//!     unsound instance would let `False` be derived.
//!
//! This is the class `declare_hit` is documented and tested to support. Anything
//! outside it (indexed/parametric HITs, point constructors with fields, a
//! `Type`-valued dependent eliminator, 2-dimensional path constructors between paths)
//! needs genuine interval/cubical machinery and is out of scope for this non-cubical
//! kernel, exactly as [`crate::circle`]'s "Supported class" section argues.
//!
//! [`crate::circle`]'s `S¹` and [`crate::trunc`]'s `Trunc` are left as their existing
//! hand-coded, independently-tested instances (re-expressing them atop `declare_hit`
//! would only add risk to already-sound, already-tested code for no soundness
//! benefit); this module ships the general mechanism plus two *new* worked examples —
//! the interval `I` (two points, one path) and a three-point cycle `Z₃` (three points,
//! three paths, forming a triangle) — see the tests below.
//!
//! [`Eq`]: crate::inductive::declare_eq

use crate::env::{Decl, Env, Hit, HitRole};
use crate::level::Level;
use crate::term::{name, Name, Term};
use std::rc::Rc;

/// A user's declaration of a 1-HIT: `type_name`'s point and path constructors. See the
/// module docs for the exact supported class.
#[derive(Clone, Debug)]
pub struct HitSpec {
    /// The type former's name, e.g. `"Interval"`.
    pub type_name: String,
    /// Names of the (nullary) point constructors, e.g. `["Interval.i0",
    /// "Interval.i1"]`. Must be non-empty.
    pub point_names: Vec<String>,
    /// Names and endpoints of the path constructors: `(name, lhs_point_index,
    /// rhs_point_index)`, e.g. `[("Interval.seg", 0, 1)]` for `seg : i0 = i1`. Indices
    /// must be valid indices into `point_names`.
    pub path_names: Vec<(String, usize, usize)>,
}

/// `Eq.{lvl} T x y`.
fn eq_app(lvl: Level, t: Term, x: Term, y: Term) -> Term {
    Term::apps(Term::cnst(name("Eq"), vec![lvl]), [t, x, y])
}

/// Declare and install a new 1-HIT into `env` per `spec`. Requires the `Eq` inductive
/// (with `Eq.refl`) to already be installed. Rejects: a malformed spec (no point
/// constructors, or a path endpoint out of range), and re-use of any name the spec
/// would introduce (`type_name`, every point/path name, `type_name.rec`,
/// `type_name.ind`).
pub fn declare_hit(env: &mut Env, spec: &HitSpec) -> Result<(), String> {
    match env.get("Eq") {
        Some(Decl::Inductive(_)) => {}
        _ => return Err(format!("HIT '{}' requires the 'Eq' inductive first", spec.type_name)),
    }
    let n = spec.point_names.len();
    if n == 0 {
        return Err(format!("HIT '{}' needs at least one point constructor", spec.type_name));
    }
    let m = spec.path_names.len();
    for (pname, lhs, rhs) in &spec.path_names {
        if *lhs >= n || *rhs >= n {
            return Err(format!(
                "HIT '{}': path '{pname}' endpoint out of range (have {n} point constructors)",
                spec.type_name
            ));
        }
    }
    let rec_name = format!("{}.rec", spec.type_name);
    let ind_name = format!("{}.ind", spec.type_name);
    let mut all_names: Vec<&str> = vec![spec.type_name.as_str(), rec_name.as_str(), ind_name.as_str()];
    for p in &spec.point_names {
        all_names.push(p.as_str());
    }
    for (pname, ..) in &spec.path_names {
        all_names.push(pname.as_str());
    }
    for (i, nm) in all_names.iter().enumerate() {
        if env.contains(nm) {
            return Err(format!("'{nm}' is already declared"));
        }
        for other in &all_names[..i] {
            if other == nm {
                return Err(format!("HIT '{}': duplicate name '{nm}'", spec.type_name));
            }
        }
    }

    let id: Name = name(&spec.type_name);
    let one = Level::of_nat(1); // `Eq` over an `H : Type 0` value is `Eq.{1} …`.
    let v = Level::param(0); // `H.rec`'s target universe.

    let h_ty = Term::cnst(id.clone(), vec![]);
    let point_term = |i: usize| Term::cnst(name(&spec.point_names[i]), vec![]);

    // ------------------------------------------------------------------
    // H : Type 0
    // ------------------------------------------------------------------
    env.insert(
        id.clone(),
        Decl::Hit(Rc::new(Hit { id: id.clone(), role: HitRole::Type, num_levels: 0, ty: Term::typ(0) })),
    )?;

    // ------------------------------------------------------------------
    // H.p_i : H   (i = 0..n)
    // ------------------------------------------------------------------
    for (i, pname) in spec.point_names.iter().enumerate() {
        env.insert(
            name(pname),
            Decl::Hit(Rc::new(Hit {
                id: id.clone(),
                role: HitRole::Point { index: i as u32 },
                num_levels: 0,
                ty: h_ty.clone(),
            })),
        )?;
    }

    // ------------------------------------------------------------------
    // H.e_j : Eq.{1} H H.p_{lhs_j} H.p_{rhs_j}   (j = 0..m)
    // ------------------------------------------------------------------
    for (pname, lhs, rhs) in &spec.path_names {
        let ty = eq_app(one.clone(), h_ty.clone(), point_term(*lhs), point_term(*rhs));
        env.insert(
            name(pname),
            Decl::Hit(Rc::new(Hit {
                id: id.clone(),
                role: HitRole::Path { lhs: *lhs as u32, rhs: *rhs as u32 },
                num_levels: 0,
                ty,
            })),
        )?;
    }

    // ------------------------------------------------------------------
    // H.rec.{v} : Π (P : Sort v) (case_0 : P) .. (case_{n-1} : P)
    //               (resp_0 : Eq.{v} P case_{lhs_0} case_{rhs_0}) ..
    //               (resp_{m-1} : Eq.{v} P case_{lhs_{m-1}} case_{rhs_{m-1}}),
    //             H → P
    //
    // Binder layout (0-indexed): b_0 = P, b_{1+i} = case_i (i<n),
    // b_{1+n+j} = resp_j (j<m), b_{1+n+m} = t. A reference to binder `src` while
    // writing the type of binder `dst` (src < dst) uses de Bruijn index
    // `dst - 1 - src`; the final target `P` (referenced after all `n+m+2` binders)
    // uses index `n+m+1`.
    // ------------------------------------------------------------------
    let total_before_t = 1 + n + m; // index of the `t` binder
    let rec_target = Term::Var(total_before_t); // n+m+1, see above

    let mut rec_ty = Term::pi(h_ty.clone(), rec_target);
    // Build binders from `t` (innermost, dst = total_before_t) down to `P` (dst = 0),
    // wrapping `rec_ty` one binder further out each step.
    for dst in (0..total_before_t).rev() {
        let binder_ty = if dst == 0 {
            // P : Sort v
            Term::Sort(v.clone())
        } else if dst <= n {
            // case_{dst-1} : P   (P is src = 0)
            Term::Var(dst - 1)
        } else {
            // resp_j : Eq.{v} P case_{lhs_j} case_{rhs_j}, j = dst - 1 - n
            let j = dst - 1 - n;
            let (lhs, rhs) = (spec.path_names[j].1, spec.path_names[j].2);
            let p_idx = dst - 1; // src = 0 (P)
            let case_lhs_idx = dst - 1 - (1 + lhs);
            let case_rhs_idx = dst - 1 - (1 + rhs);
            eq_app(v.clone(), Term::Var(p_idx), Term::Var(case_lhs_idx), Term::Var(case_rhs_idx))
        };
        rec_ty = Term::pi(binder_ty, rec_ty);
    }
    env.insert(
        name(&rec_name),
        Decl::Hit(Rc::new(Hit {
            id: id.clone(),
            role: HitRole::Rec { num_points: n as u32, num_paths: m as u32 },
            num_levels: 1,
            ty: rec_ty,
        })),
    )?;

    // ------------------------------------------------------------------
    // H.ind : Π (β : H → Prop) (h_0 : β H.p_0) .. (h_{n-1} : β H.p_{n-1}),
    //         Π (t : H), β t
    //
    // Binder layout: b_0 = β, b_{1+i} = h_i (i<n), b_{1+n} = t.
    // Target `β t`: context size n+2, β at src 0 -> index n+1, t at src (1+n) -> 0.
    // ------------------------------------------------------------------
    let ind_target = Term::app(Term::Var(n + 1), Term::Var(0));
    let mut ind_ty = Term::pi(h_ty.clone(), ind_target);
    let total_before_t_ind = 1 + n;
    for dst in (0..total_before_t_ind).rev() {
        let binder_ty = if dst == 0 {
            Term::arrow(h_ty.clone(), Term::prop())
        } else {
            // h_{dst-1} : β H.p_{dst-1}   (β is src = 0)
            let beta_idx = dst - 1;
            Term::app(Term::Var(beta_idx), point_term(dst - 1))
        };
        ind_ty = Term::pi(binder_ty, ind_ty);
    }
    env.insert(
        name(&ind_name),
        Decl::Hit(Rc::new(Hit {
            id: id.clone(),
            role: HitRole::Ind { num_points: n as u32 },
            num_levels: 0,
            ty: ind_ty,
        })),
    )?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::{Checker, LocalCtx};
    use crate::inductive::{declare_eq, declare_nat};
    use crate::reduce::Reducer;

    fn base_env() -> Env {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_eq(&mut env).unwrap();
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

    /// Worked example 1: the interval `I`, two points and one path — `i0 : I`, `i1 :
    /// I`, `seg : Eq I i0 i1`. The standard second example of a 1-HIT after the circle
    /// (here as a *user declaration*, not hand-coded).
    fn interval_spec() -> HitSpec {
        HitSpec {
            type_name: "Interval".to_string(),
            point_names: vec!["Interval.i0".to_string(), "Interval.i1".to_string()],
            path_names: vec![("Interval.seg".to_string(), 0, 1)],
        }
    }

    /// Worked example 2: a 3-cycle `Z3` — three points and three paths forming a
    /// triangle (`p0=p1`, `p1=p2`, `p2=p0`), exercising `n=3, m=3` together (multiple
    /// point AND multiple path constructors at once, unlike the interval's `n=2,m=1`).
    fn z3_spec() -> HitSpec {
        HitSpec {
            type_name: "Z3".to_string(),
            point_names: vec!["Z3.p0".to_string(), "Z3.p1".to_string(), "Z3.p2".to_string()],
            path_names: vec![
                ("Z3.e01".to_string(), 0, 1),
                ("Z3.e12".to_string(), 1, 2),
                ("Z3.e20".to_string(), 2, 0),
            ],
        }
    }

    fn interval_env() -> Env {
        let mut env = base_env();
        declare_hit(&mut env, &interval_spec()).unwrap();
        env
    }

    fn z3_env() -> Env {
        let mut env = base_env();
        declare_hit(&mut env, &z3_spec()).unwrap();
        env
    }

    // ---------------------------------------------------------------- well-formedness

    #[test]
    fn interval_constants_wellformed() {
        let env = interval_env();
        let chk = Checker::new(&env);
        for n in ["Interval", "Interval.i0", "Interval.i1", "Interval.seg", "Interval.rec", "Interval.ind"] {
            chk.infer_closed(env.get(n).unwrap().ty()).unwrap_or_else(|e| panic!("{n} ill-formed: {e}"));
        }
    }

    #[test]
    fn z3_constants_wellformed() {
        let env = z3_env();
        let chk = Checker::new(&env);
        for n in [
            "Z3", "Z3.p0", "Z3.p1", "Z3.p2", "Z3.e01", "Z3.e12", "Z3.e20", "Z3.rec", "Z3.ind",
        ] {
            chk.infer_closed(env.get(n).unwrap().ty()).unwrap_or_else(|e| panic!("{n} ill-formed: {e}"));
        }
    }

    #[test]
    fn requires_eq() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        let err = declare_hit(&mut env, &interval_spec()).unwrap_err();
        assert!(err.contains("Eq"), "got: {err}");
    }

    #[test]
    fn rejects_double_declare() {
        let mut env = interval_env();
        let err = declare_hit(&mut env, &interval_spec()).unwrap_err();
        assert!(err.contains("already declared"), "got: {err}");
    }

    #[test]
    fn spec_rejects_empty_points() {
        let mut env = base_env();
        let spec = HitSpec { type_name: "Bad".to_string(), point_names: vec![], path_names: vec![] };
        let err = declare_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("at least one point"), "got: {err}");
    }

    #[test]
    fn spec_rejects_bad_path_index() {
        let mut env = base_env();
        let spec = HitSpec {
            type_name: "Bad".to_string(),
            point_names: vec!["Bad.p0".to_string()],
            path_names: vec![("Bad.e".to_string(), 0, 5)],
        };
        let err = declare_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("out of range"), "got: {err}");
    }

    // ---------------------------------------------------------------- points & paths

    #[test]
    fn points_typecheck() {
        let env = interval_env();
        let chk = Checker::new(&env);
        for p in ["Interval.i0", "Interval.i1"] {
            let ty = chk.infer_closed(&cn(p)).unwrap();
            assert!(Reducer::new(&env).is_def_eq(&ty, &cn("Interval")));
        }
    }

    #[test]
    fn seg_typechecks() {
        let env = interval_env();
        let chk = Checker::new(&env);
        let goal = eq_app(Level::of_nat(1), cn("Interval"), cn("Interval.i0"), cn("Interval.i1"));
        chk.check(&mut LocalCtx::new(), &cn("Interval.seg"), &goal).unwrap();
    }

    /// SOUNDNESS (adversarial): the path is only propositional — it does not reduce.
    #[test]
    fn path_does_not_reduce_to_refl() {
        let env = interval_env();
        let red = Reducer::new(&env);
        assert_eq!(red.whnf(&cn("Interval.seg")), cn("Interval.seg"));
        let nbe = crate::nbe::Nbe::new(&env);
        assert_eq!(nbe.normalize(&cn("Interval.seg")), cn("Interval.seg"));
    }

    /// SOUNDNESS (adversarial): the two points of the interval are NOT definitionally
    /// equal (only propositionally, via `seg`) — canonicity of the point layer.
    #[test]
    fn points_stay_distinct() {
        let env = interval_env();
        let red = Reducer::new(&env);
        assert!(!red.is_def_eq(&cn("Interval.i0"), &cn("Interval.i1")), "i0 and i1 must stay distinct");
    }

    // ---------------------------------------------------------------- recursor (n=2,m=1)

    /// COMPUTATION RULE (both points), differential reducer vs. NbE.
    #[test]
    fn interval_rec_computes_on_both_points() {
        let env = interval_env();
        let u = Level::of_nat(1);
        let (c0, c1) = (lit(10), lit(20));
        let resp = refl(u.clone(), cn("Nat"), lit(99)); // wrong on purpose is checked elsewhere; use a case-respecting one below instead
        let _ = resp;
        // Use a genuinely respecting instance: constant map, c0 = c1 = 7, resp = refl.
        let c = lit(7);
        let resp_ok = refl(u.clone(), cn("Nat"), c.clone());
        for (pt, expect) in [("Interval.i0", &c), ("Interval.i1", &c)] {
            let rec = Term::apps(
                Term::cnst(name("Interval.rec"), vec![u.clone()]),
                [cn("Nat"), c.clone(), c.clone(), resp_ok.clone(), cn(pt)],
            );
            let chk = Checker::new(&env);
            chk.check(&mut LocalCtx::new(), &rec, &cn("Nat")).unwrap();
            let red = Reducer::new(&env);
            assert!(red.is_def_eq(&rec, expect), "reducer: rec {pt} = case");
            let nbe = crate::nbe::Nbe::new(&env);
            assert_eq!(nbe.normalize(&rec), nbe.normalize(expect), "nbe: rec {pt} = case");
        }
        let (c0_, c1_) = (c0, c1);
        let _ = (c0_, c1_);
    }

    /// SOUNDNESS (adversarial): a `resp` that does NOT actually witness `Eq P case_0
    /// case_1` (mismatched cases) is rejected by the checker before `H.rec` can even
    /// be formed.
    #[test]
    fn mismatched_resp_rejected() {
        let env = interval_env();
        let u = Level::of_nat(1);
        // case_0 = 1, case_1 = 2, but resp : Eq Nat 1 1 (does not connect 1 and 2).
        let bad_resp = refl(u.clone(), cn("Nat"), lit(1));
        let rec = Term::apps(
            Term::cnst(name("Interval.rec"), vec![u.clone()]),
            [cn("Nat"), lit(1), lit(2), bad_resp, cn("Interval.i0")],
        );
        let chk = Checker::new(&env);
        assert!(chk.infer_closed(&rec).is_err(), "mismatched resp must be rejected");
    }

    /// SOUNDNESS (adversarial): `H.rec` does not fire on a path constructor — `seg`'s
    /// type is `Eq Interval i0 i1`, not `Interval`, so using it as the scrutinee is
    /// ill-typed and rejected outright.
    #[test]
    fn rec_does_not_fire_on_path() {
        let env = interval_env();
        let u = Level::of_nat(1);
        let resp_ok = refl(u.clone(), cn("Nat"), lit(7));
        let rec = Term::apps(
            Term::cnst(name("Interval.rec"), vec![u.clone()]),
            [cn("Nat"), lit(7), lit(7), resp_ok, cn("Interval.seg")],
        );
        let chk = Checker::new(&env);
        assert!(chk.infer_closed(&rec).is_err(), "rec on a path scrutinee must be rejected");
    }

    /// SOUNDNESS (adversarial): a HIT recursor never fires on a point constructor
    /// belonging to a *different* declared HIT, even though roles overlap (`Point {
    /// index: 0 }` exists in both `Interval` and `Z3`). Both are declared in one env;
    /// applying `Interval.rec` to `Z3.p0` must be ill-typed and rejected.
    #[test]
    fn rec_does_not_cross_fire_between_hits() {
        let mut env = interval_env();
        declare_hit(&mut env, &z3_spec()).unwrap();
        let u = Level::of_nat(1);
        let resp_ok = refl(u.clone(), cn("Nat"), lit(7));
        let rec = Term::apps(
            Term::cnst(name("Interval.rec"), vec![u.clone()]),
            [cn("Nat"), lit(7), lit(7), resp_ok, cn("Z3.p0")],
        );
        let chk = Checker::new(&env);
        assert!(chk.infer_closed(&rec).is_err(), "Interval.rec applied to a Z3 point must be rejected");
    }

    /// `H.rec` is stuck (not reduced) on a neutral scrutinee — canonicity for open
    /// terms too.
    #[test]
    fn rec_stuck_on_neutral() {
        let env = interval_env();
        let u = Level::of_nat(1);
        let resp_ok = refl(u.clone(), cn("Nat"), lit(7));
        let body = Term::apps(
            Term::cnst(name("Interval.rec"), vec![u.clone()]),
            [cn("Nat"), lit(7), lit(7), resp_ok, Term::Var(0)],
        );
        let f = Term::lam(cn("Interval"), body);
        let chk = Checker::new(&env);
        chk.infer_closed(&f).unwrap();
        let red = Reducer::new(&env);
        match red.whnf(&f) {
            Term::Lam(_, _) => {}
            other => panic!("expected a stuck lambda, got {other:?}"),
        }
    }

    // ---------------------------------------------------------------- recursor (n=3,m=3)

    /// `Z3.rec` computes correctly on all three points at once, with a genuinely
    /// respecting (non-constant across path direction irrelevant, since paths are
    /// propositional) triangle of `resp` proofs — here mapping to the same value `0`
    /// on all three points, the simplest respecting instance for `n=3,m=3`.
    #[test]
    fn z3_rec_computes_on_all_points() {
        let env = z3_env();
        let u = Level::of_nat(1);
        let c = lit(0);
        let resp = refl(u.clone(), cn("Nat"), c.clone());
        for pt in ["Z3.p0", "Z3.p1", "Z3.p2"] {
            let rec = Term::apps(
                Term::cnst(name("Z3.rec"), vec![u.clone()]),
                [cn("Nat"), c.clone(), c.clone(), c.clone(), resp.clone(), resp.clone(), resp.clone(), cn(pt)],
            );
            let chk = Checker::new(&env);
            chk.check(&mut LocalCtx::new(), &rec, &cn("Nat")).unwrap();
            let red = Reducer::new(&env);
            assert!(red.is_def_eq(&rec, &c), "reducer: Z3.rec {pt} = 0");
            let nbe = crate::nbe::Nbe::new(&env);
            assert_eq!(nbe.normalize(&rec), nbe.normalize(&c), "nbe: Z3.rec {pt} = 0");
        }
    }

    // ---------------------------------------------------------------- H.ind

    #[test]
    fn interval_ind_applies() {
        let env = interval_env();
        let u = Level::of_nat(1);
        // β := λ t. Eq Nat 0 0  (a constant Prop over the interval)
        let beta = Term::lam(cn("Interval"), eq_app(u.clone(), cn("Nat"), lit(0), lit(0)));
        let h0 = refl(u.clone(), cn("Nat"), lit(0));
        let h1 = refl(u.clone(), cn("Nat"), lit(0));
        let ind = Term::apps(
            Term::cnst(name("Interval.ind"), vec![]),
            [beta, h0, h1, cn("Interval.i0")],
        );
        let goal = eq_app(u.clone(), cn("Nat"), lit(0), lit(0));
        let chk = Checker::new(&env);
        chk.check(&mut LocalCtx::new(), &ind, &goal).unwrap();
    }

    // ---------------------------------------------------------------- no False

    /// ADVERSARIAL: cannot derive `False` from the general HIT schema. `seg` requires
    /// genuine `Interval`-typed endpoints — using it to prove an unrelated `Eq` is a
    /// type mismatch, and no computation rule anywhere identifies distinct closed
    /// `Nat` values.
    #[test]
    fn cannot_prove_false() {
        let env = interval_env();
        let bogus_goal = eq_app(Level::of_nat(0), cn("Nat"), lit(3), lit(5));
        let chk = Checker::new(&env);
        assert!(
            chk.check(&mut LocalCtx::new(), &cn("Interval.seg"), &bogus_goal).is_err(),
            "Interval.seg must not check against an unrelated Eq goal"
        );
    }

    /// ADVERSARIAL: two independently declared HITs cannot be confused to derive a
    /// definitional equality that only a (propositional) path constructor grants —
    /// e.g. `Interval.i0` and `Interval.i1` are never `is_def_eq` even after `Z3` is
    /// also declared in the same env.
    #[test]
    fn no_definitional_collapse_with_multiple_hits_declared() {
        let mut env = interval_env();
        declare_hit(&mut env, &z3_spec()).unwrap();
        let red = Reducer::new(&env);
        assert!(!red.is_def_eq(&cn("Interval.i0"), &cn("Interval.i1")));
        assert!(!red.is_def_eq(&cn("Z3.p0"), &cn("Z3.p1")));
        assert!(!red.is_def_eq(&cn("Z3.p1"), &cn("Z3.p2")));
    }
}
