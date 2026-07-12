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
//!   * a type former `H : Type 0` (fixed universe, non-parametric, non-indexed — see
//!     "Supported class" below),
//!   * `n ≥ 1` **point constructors** `H.p_0, …, H.p_{n-1}`, each with its own
//!     (possibly empty) list of [`Field`]s — a field is either [`Field::Rec`] (a
//!     strictly-positive recursive occurrence of `H` itself, e.g. `List`'s `cons`'s
//!     tail) or [`Field::NonRec`] (a fixed, closed, `H`-*free* type, e.g. `Nat`); so
//!     `H.p_i : field_0 → field_1 → … → H`,
//!   * `m ≥ 0` **path constructors** `H.e_j`, each optionally **quantified** over
//!     extra variables and an extra hypothesis (mirroring a set-quotient's `glue : Π a
//!     b, R a b → mk a = mk b`), relating two applications of point constructors *to
//!     concrete field arguments*: `H.e_j : Π q_0 .. q_{k-1} (h : premise),
//!     Eq H (H.p_lhs a_0 .. a_{r-1}) (H.p_rhs b_0 .. b_{s-1})` — a propositional
//!     identification, holding only through the existing [`Eq`] inductive, never
//!     definitionally (no interval/cubical machinery). The point constructors `H.e_j`
//!     relates must have **no `Field::Rec` field** (see "Supported class" for why).
//!
//! `declare_hit` synthesizes and installs, generically in the spec:
//!
//! ```text
//!   H          : Type 0
//!   H.p_i      : field_0 → .. → field_{k_i-1} → H                       (i = 0..n)
//!   H.e_j      : Π q_.. (premise?), Eq.{1} H (H.p_lhs a_..) (H.p_rhs b_..)  (j = 0..m)
//!   H.rec.{v}  : Π (P : Sort v)
//!                  (case_0 : field'_0 → .. → field'_{k_0-1} → P) ..
//!                  (resp_0 : Π q_.. (premise?),
//!                            Eq.{v} P (case_lhs a_..) (case_rhs b_..)) ..
//!                H → P
//!   H.ind      : Π (β : H → Prop) (h_0 : β (H.p_0)) .. ,
//!                Π (t : H), β t              (only offered when every point ctor is nullary)
//! ```
//!
//! where a `case_i`'s field telescope replaces every `Field::Rec` slot with `P`
//! (the already-computed recursive result, exactly as `Nat.rec`'s `succ`-case is
//! `Π (n:Nat), motive n → motive (succ n)` collapsed to `P → P` for a *non-dependent*
//! `P`) and keeps every `Field::NonRec` slot as its original field type — and with the
//! **ι-rule**, added generically to both the trusted [`crate::reduce`] and the fast
//! [`crate::nbe`] (differentially checked in tests):
//!
//! ```text
//!   H.rec.{v} P case_.. resp_.. (H.p_i a_0 .. a_{k-1})  ↦  case_i b_0 .. b_{k-1}
//!     where b_j = a_j                              if field_j is Field::NonRec
//!           b_j = H.rec.{v} P case_.. resp_.. a_j   if field_j is Field::Rec
//! ```
//!
//! This generalizes exactly what [`crate::circle`] and [`crate::trunc`] each
//! hand-wrote once (one nullary point constructor + path constructor(s) + a recursor)
//! to an arbitrary user-chosen set of **fielded** point constructors and **quantified**
//! path constructors — the way `rv_kernel::generate` synthesizes an ordinary
//! inductive's recursor from its declared (fielded) constructors, but for a 1-HIT.
//!
//! ## Why this is SOUND
//!
//! * **Point constructors never become definitionally equal via paths.** Each `H.e_j`
//!   is an axiom-shaped constant with **no** reduction rule — nothing makes it reduce
//!   to `Eq.refl`, and nothing reduces a point-constructor application because of it.
//!   Point constructors remain stable canonical values; conversion never merges two
//!   distinct ones (adversarial tests `points_stay_distinct`, `path_does_not_reduce_to_refl`).
//! * **The ι-rule fires ONLY on a literal point constructor, fully applied to its
//!   declared fields**, never on a path constructor, a partially-applied point
//!   constructor, or a neutral. [`crate::reduce::Reducer::try_hit_rec`] weak-head
//!   reduces the scrutinee and matches its head against a `HitRole::Point` **of the
//!   same `id`** with a spine length equal to that point constructor's declared arity —
//!   a path constructor's type is `Eq H _ _`, not `H`, so it can never even *appear* as
//!   a well-typed `H.rec` scrutinee (adversarial test `rec_does_not_fire_on_path`); a
//!   scrutinee from a *different* declared HIT is rejected by the `id` guard even
//!   though both may share a role tag (adversarial test
//!   `rec_does_not_cross_fire_between_hits`); an under-applied point constructor
//!   (fewer args than its arity) stays stuck (adversarial test
//!   `rec_stuck_on_underapplied_point`).
//! * **Respectfulness is checked, not trusted.** Each `resp_j` must type-check
//!   *before* `H.rec` can be formed at all; the ι-rule discards it at reduction time
//!   exactly as `Quot.lift`/`Trunc.lift`/`S¹.rec` discard their `resp`/`lp` — soundness
//!   comes from `resp_j` having been checked to *exist*, never from it being inspected
//!   computationally. A mismatched `resp_j` is rejected by ordinary type-checking
//!   (adversarial test `mismatched_resp_rejected`).
//! * **`H.ind` eliminates only into `Prop`**, with no computation rule; proof
//!   irrelevance makes the missing ι-rule unobservable. Kept to the original nullary
//!   restriction (see "Supported class") — extending it to fielded point constructors
//!   needs the recursive-field hypothesis threaded exactly as `H.rec`'s `case_i` does,
//!   which is straightforward but left as future work alongside indexed HITs, to keep
//!   this change centered on the priority-1 request (fielded `H.rec`).
//! * **Strict positivity is enforced by construction and checked at declaration time**:
//!   every `Field::NonRec(t)` is rejected if `t` mentions `H`'s own type former
//!   anywhere (`occurs_const`) — the *only* way `H` may appear in a field is as the
//!   entire field (`Field::Rec`), never nested inside another type (no `H → Nat`, no
//!   `List H`; adversarial test `nonrec_field_mentioning_self_rejected`). This is a
//!   deliberately conservative (but sound) approximation of full strict-positivity
//!   checking (which would also accept some *nested* strictly-positive occurrences,
//!   e.g. `List H` for an already strictly-positive `List`) — see "Supported class".
//!
//! ## Supported class and restrictions (read this before relying on this module)
//!
//! `declare_hit` supports exactly:
//!
//!   * **non-indexed, non-parametric** HITs: `H : Type 0` only — no `H : Π params,
//!     Type` and no index family `H : Π indices, Type`. A general schema would need to
//!     reuse the ordinary indexed-inductive-declaration machinery in
//!     `rv_kernel::generate`/`mutual`; layering path constructors and a joint
//!     index-threading recursor on top of that is a materially larger change, left as
//!     documented future work (this is the "indexed HIT families" item from the
//!     broader goal, deliberately not attempted here to keep the fielded extension
//!     sound and well-tested);
//!   * **point constructors with fields**, each field either `Field::Rec` (a bare
//!     recursive occurrence of `H`) or `Field::NonRec` (a fixed closed type not
//!     mentioning `H` at all, and *not* depending on the values of earlier fields of
//!     the same constructor — i.e. non-dependent field telescopes, matching
//!     `Nat.succ`'s `Nat → Nat` but not e.g. a `Σ`-like field whose type mentions a
//!     sibling field's value);
//!   * **path constructors** between applications of two (possibly equal) point
//!     constructors to concrete field arguments, optionally **quantified** over extra
//!     variables and an extra hypothesis premise (enough to express a genuine
//!     set-quotient's `glue : Π a b, R a b → mk a = mk b` for a *fixed*, already
//!     top-level-declared relation `R` — since `H` itself carries no parameters, `R`
//!     and the quantifiers' types cannot themselves be parameters of `H`, only
//!     previously-declared closed types/relations; true parametric quotients need
//!     parametric HITs, item above). **Restriction**: a path constructor may only
//!     relate point constructors that have **no `Field::Rec` field** — i.e. no
//!     recursive point constructor may be a path endpoint. This keeps the recursor's
//!     `resp_j` premise a direct application of `case_lhs`/`case_rhs` to the (already
//!     non-recursive, hence untransformed) field arguments, rather than needing
//!     `resp_j`'s type to itself embed a recursive `H.rec` call — sound in principle
//!     (ordinary induction handles exactly this via the IH) but a materially larger
//!     change than the fielded extension asked for here (this is the honest partial:
//!     fielded-recursive point constructors and quantified path constructors both
//!     work, just not *simultaneously on the same point constructor*);
//!   * **eliminators**: the non-dependent `H.rec` (into any `Sort v`, generalized to
//!     fielded point constructors as above) and the dependent, `Prop`-only `H.ind`,
//!     **still restricted to nullary point constructors** (unchanged from before this
//!     extension — extending `H.ind` to fielded point constructors is straightforward
//!     future work, not attempted here). A dependent, `Type`-valued eliminator is
//!     **not** offered, for the same reason [`crate::circle`]/[`crate::trunc`] omit it:
//!     getting the dependent computation/subject-reduction interaction right for an
//!     arbitrary path shape, without an interval, is delicate enough that an unsound
//!     instance would let `False` be derived.
//!
//! Anything outside this class (indexed/parametric HITs, a `Type`-valued dependent
//! eliminator, a dependent eliminator over fielded point constructors, path
//! constructors touching recursive point constructors, 2-dimensional path
//! constructors between paths) needs genuine interval/cubical machinery or
//! substantially more indexing infrastructure, and is out of scope here, exactly as
//! [`crate::circle`]'s "Supported class" section argues for the original schema.
//!
//! [`crate::circle`]'s `S¹` and [`crate::trunc`]'s `Trunc` are left as their existing
//! hand-coded, independently-tested instances. This module ships the general
//! mechanism plus worked examples covering: the original nullary interval `I` and
//! 3-cycle `Z₃`; a **fielded, non-recursive** set-quotient `NatModR` (`mk : Nat →
//! NatModR`, `glue : Π a b, R a b → mk a = mk b` for a concrete `R`); and a **fielded,
//! recursive** list-like HIT `FreeMonoid` (`unit : FreeMonoid`, `cons : Nat →
//! FreeMonoid → FreeMonoid`, no path constructors) exercising the recursive ι-rule.
//!
//! [`Eq`]: crate::inductive::declare_eq

use crate::env::{Decl, Env, Hit, HitRole};
use crate::level::Level;
use crate::term::{name, Name, Term};
use std::rc::Rc;

/// A field of a point constructor: either a strictly-positive recursive occurrence of
/// the HIT being declared, or a fixed, closed, `H`-free type. See the module docs.
#[derive(Clone, Debug)]
pub enum Field {
    /// A recursive field of type `H` itself.
    Rec,
    /// A non-recursive field of a fixed closed type, which must not mention `H`'s own
    /// type former (checked by `declare_hit`; positivity).
    NonRec(Term),
}

/// A user's declaration of one point constructor: a name plus its (possibly empty,
/// possibly recursive) field list.
#[derive(Clone, Debug)]
pub struct PointSpec {
    pub name: String,
    pub fields: Vec<Field>,
}

impl PointSpec {
    /// A nullary point constructor (the original, pre-fielded schema's shape).
    pub fn nullary(name: impl Into<String>) -> Self {
        PointSpec { name: name.into(), fields: Vec::new() }
    }
}

/// A user's declaration of one path constructor: `H.name : Π quantifiers.. (h :
/// premise)?, Eq H (H.p_{lhs.0} lhs.1..) (H.p_{rhs.0} rhs.1..)`.
///
/// `premise`, `lhs.1`, and `rhs.1` are given as raw terms in the de Bruijn context of
/// `quantifiers` (innermost = last quantifier = `Var(0)`) — `premise` is typed in that
/// context; `lhs.1`/`rhs.1` are typed in the context of `quantifiers` extended by
/// `premise` if present (so `Var(0)` there is the premise's own bound hypothesis, if
/// any, shifted past).
#[derive(Clone, Debug)]
pub struct PathSpec {
    pub name: String,
    /// Types of extra universally-quantified variables, outermost first.
    pub quantifiers: Vec<Term>,
    /// An optional extra hypothesis, in the context of `quantifiers`.
    pub premise: Option<Term>,
    /// `(point index, field arguments)` for the left endpoint.
    pub lhs: (usize, Vec<Term>),
    /// `(point index, field arguments)` for the right endpoint.
    pub rhs: (usize, Vec<Term>),
}

impl PathSpec {
    /// An unquantified path constructor between two nullary point constructors — the
    /// original, pre-generalized schema's shape.
    pub fn simple(name: impl Into<String>, lhs: usize, rhs: usize) -> Self {
        PathSpec {
            name: name.into(),
            quantifiers: Vec::new(),
            premise: None,
            lhs: (lhs, Vec::new()),
            rhs: (rhs, Vec::new()),
        }
    }
}

/// A user's declaration of a 1-HIT: `type_name`'s point and path constructors. See the
/// module docs for the exact supported class.
#[derive(Clone, Debug)]
pub struct HitSpec {
    /// The type former's name, e.g. `"Interval"`.
    pub type_name: String,
    /// The point constructors. Must be non-empty.
    pub points: Vec<PointSpec>,
    /// The path constructors.
    pub paths: Vec<PathSpec>,
}

/// `Eq.{lvl} T x y`.
fn eq_app(lvl: Level, t: Term, x: Term, y: Term) -> Term {
    Term::apps(Term::cnst(name("Eq"), vec![lvl]), [t, x, y])
}

/// Does `t` mention the constant `id` anywhere (used for strict-positivity checking of
/// non-recursive fields)?
fn occurs_const(t: &Term, id: &Name) -> bool {
    match t {
        Term::Const(n, _) => n == id,
        Term::App(f, a) => occurs_const(f, id) || occurs_const(a, id),
        Term::Lam(d, b) => occurs_const(d, id) || occurs_const(b, id),
        Term::Pi(_, d, b) => occurs_const(d, id) || occurs_const(b, id),
        Term::Let(_, ty, v, b) => occurs_const(ty, id) || occurs_const(v, id) || occurs_const(b, id),
        Term::PLam(b) => occurs_const(b, id),
        Term::PApp(p, r) => occurs_const(p, id) || occurs_const(r, id),
        Term::PathP(fam, a0, a1) => {
            occurs_const(fam, id) || occurs_const(a0, id) || occurs_const(a1, id)
        }
        Term::Sort(_) | Term::Var(_) | Term::Meta(_) | Term::I | Term::IZero | Term::IOne => false,
        Term::Sys(branches) => branches.iter().any(|(_, t)| occurs_const(t, id)),
        Term::Partial(_, a) => occurs_const(a, id),
        Term::Transp(fam, _, a) => occurs_const(fam, id) || occurs_const(a, id),
        Term::HComp(ty, _, u, u0) => {
            occurs_const(ty, id) || occurs_const(u, id) || occurs_const(u0, id)
        }
    }
}

/// Wrap `target` in a telescope of `fields`, outermost first. `rec_dom_at(j)` gives
/// the domain to use for a `Field::Rec` slot at position `j` (0-based, outermost
/// first) — for a point constructor's own type this is always the closed `H` (so the
/// position doesn't matter); for a `case_i` it is `P` referenced at the correct de
/// Bruijn depth for that position, which *does* depend on `j` since each field opens
/// one more binder before the next field's domain is written.
fn telescope(fields: &[Field], mut rec_dom_at: impl FnMut(usize) -> Term, target: Term) -> Term {
    let mut ty = target;
    for (j, f) in fields.iter().enumerate().rev() {
        let dom = match f {
            Field::Rec => rec_dom_at(j),
            Field::NonRec(t) => t.clone(),
        };
        ty = Term::pi(dom, ty);
    }
    ty
}

/// Declare and install a new 1-HIT into `env` per `spec`. Requires the `Eq` inductive
/// (with `Eq.refl`) to already be installed. Rejects: a malformed spec (no point
/// constructors, a path endpoint out of range, a path field-argument count mismatch, a
/// path constructor touching a point constructor with a `Field::Rec` field, or a
/// non-recursive field mentioning `H` itself — see the module docs), and re-use of any
/// name the spec would introduce.
pub fn declare_hit(env: &mut Env, spec: &HitSpec) -> Result<(), String> {
    match env.get("Eq") {
        Some(Decl::Inductive(_)) => {}
        _ => return Err(format!("HIT '{}' requires the 'Eq' inductive first", spec.type_name)),
    }
    let n = spec.points.len();
    if n == 0 {
        return Err(format!("HIT '{}' needs at least one point constructor", spec.type_name));
    }
    let m = spec.paths.len();

    let id: Name = name(&spec.type_name);

    // Positivity: no non-recursive field may mention `H` itself.
    for p in &spec.points {
        for f in &p.fields {
            if let Field::NonRec(t) = f {
                if occurs_const(t, &id) {
                    return Err(format!(
                        "HIT '{}': point constructor '{}' has a non-recursive field mentioning '{}' \
                         itself — only a bare `Field::Rec` field may recur (strict positivity)",
                        spec.type_name, p.name, spec.type_name
                    ));
                }
            }
        }
    }

    for path in &spec.paths {
        for (label, (idx, args)) in [("lhs", &path.lhs), ("rhs", &path.rhs)] {
            if *idx >= n {
                return Err(format!(
                    "HIT '{}': path '{}' {label} endpoint out of range (have {n} point constructors)",
                    spec.type_name, path.name
                ));
            }
            let arity = spec.points[*idx].fields.len();
            if args.len() != arity {
                return Err(format!(
                    "HIT '{}': path '{}' {label} gives {} field argument(s) but point constructor \
                     '{}' has arity {arity}",
                    spec.type_name,
                    path.name,
                    args.len(),
                    spec.points[*idx].name
                ));
            }
            if spec.points[*idx].fields.iter().any(|f| matches!(f, Field::Rec)) {
                return Err(format!(
                    "HIT '{}': path '{}' {label} targets point constructor '{}', which has a \
                     recursive field — path constructors may not target a recursive point \
                     constructor (see module docs, 'Supported class')",
                    spec.type_name, path.name, spec.points[*idx].name
                ));
            }
        }
    }

    let rec_name = format!("{}.rec", spec.type_name);
    let ind_name = format!("{}.ind", spec.type_name);
    let mut all_names: Vec<&str> = vec![spec.type_name.as_str(), rec_name.as_str(), ind_name.as_str()];
    for p in &spec.points {
        all_names.push(p.name.as_str());
    }
    for path in &spec.paths {
        all_names.push(path.name.as_str());
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

    let one = Level::of_nat(1); // `Eq` over an `H : Type 0` value is `Eq.{1} …`.
    let v = Level::param(0); // `H.rec`'s target universe.

    let h_ty = Term::cnst(id.clone(), vec![]);
    let point_head = |i: usize| Term::cnst(name(&spec.points[i].name), vec![]);
    let point_app = |i: usize, args: &[Term]| Term::apps(point_head(i), args.iter().cloned());

    // ------------------------------------------------------------------
    // H : Type 0
    // ------------------------------------------------------------------
    env.insert(
        id.clone(),
        Decl::Hit(Rc::new(Hit { id: id.clone(), role: HitRole::Type, num_levels: 0, ty: Term::typ(0) })),
    )?;

    // ------------------------------------------------------------------
    // H.p_i : field_0 → .. → field_{k_i-1} → H   (i = 0..n)
    // ------------------------------------------------------------------
    for (i, p) in spec.points.iter().enumerate() {
        let ty = telescope(&p.fields, |_| h_ty.clone(), h_ty.clone());
        let rec_fields: Vec<bool> = p.fields.iter().map(|f| matches!(f, Field::Rec)).collect();
        env.insert(
            name(&p.name),
            Decl::Hit(Rc::new(Hit {
                id: id.clone(),
                role: HitRole::Point { index: i as u32, fields: Rc::new(rec_fields) },
                num_levels: 0,
                ty,
            })),
        )?;
    }

    // ------------------------------------------------------------------
    // H.e_j : Π quantifiers.. (premise)?,
    //         Eq.{1} H (H.p_lhs lhs_args..) (H.p_rhs rhs_args..)   (j = 0..m)
    // ------------------------------------------------------------------
    for path in &spec.paths {
        let (lhs_i, lhs_args) = &path.lhs;
        let (rhs_i, rhs_args) = &path.rhs;
        let body = eq_app(one.clone(), h_ty.clone(), point_app(*lhs_i, lhs_args), point_app(*rhs_i, rhs_args));
        let mut ty = body;
        if let Some(prem) = &path.premise {
            ty = Term::pi(prem.clone(), ty);
        }
        for q in path.quantifiers.iter().rev() {
            ty = Term::pi(q.clone(), ty);
        }
        env.insert(
            name(&path.name),
            Decl::Hit(Rc::new(Hit {
                id: id.clone(),
                role: HitRole::Path { lhs: *lhs_i as u32, rhs: *rhs_i as u32 },
                num_levels: 0,
                ty,
            })),
        )?;
    }

    // ------------------------------------------------------------------
    // H.rec.{v} : Π (P : Sort v) (case_0 : ..) .. (case_{n-1} : ..)
    //               (resp_0 : ..) .. (resp_{m-1} : ..),
    //             H → P
    //
    // Binder layout (0-indexed): b_0 = P, b_{1+i} = case_i (i<n),
    // b_{1+n+j} = resp_j (j<m), b_{1+n+m} = t.
    // ------------------------------------------------------------------
    let total_before_t = 1 + n + m; // index of the `t` binder
    let rec_target = Term::Var(total_before_t); // n+m+1, `P` referenced after all binders
    let mut rec_ty = Term::pi(h_ty.clone(), rec_target);
    for dst in (0..total_before_t).rev() {
        let binder_ty = if dst == 0 {
            // P : Sort v
            Term::Sort(v.clone())
        } else if dst <= n {
            // case_{dst-1} : field'_0 → .. → field'_{k-1} → P
            let i = dst - 1;
            let p_idx0 = dst - 1; // P's index at this depth, before any field binder
            let k = spec.points[i].fields.len();
            let target = Term::Var(p_idx0 + k);
            telescope(&spec.points[i].fields, |j| Term::Var(p_idx0 + j), target)
        } else {
            // resp_j : Π quantifiers.. (premise)?,
            //          Eq.{v} P (case_lhs lhs_args..) (case_rhs rhs_args..)
            let j = dst - 1 - n;
            let path = &spec.paths[j];
            let (lhs_i, lhs_args) = &path.lhs;
            let (rhs_i, rhs_args) = &path.rhs;
            let body_ctx = path.quantifiers.len() + path.premise.is_some() as usize;
            let p_idx = dst - 1 + body_ctx; // P's index from inside resp_j's own telescope
            let case_lhs_idx = dst - 1 - (1 + lhs_i) + body_ctx;
            let case_rhs_idx = dst - 1 - (1 + rhs_i) + body_ctx;
            let lhs_app = Term::apps(Term::Var(case_lhs_idx), lhs_args.iter().cloned());
            let rhs_app = Term::apps(Term::Var(case_rhs_idx), rhs_args.iter().cloned());
            let body = eq_app(v.clone(), Term::Var(p_idx), lhs_app, rhs_app);
            let mut ty = body;
            if let Some(prem) = &path.premise {
                ty = Term::pi(prem.clone(), ty);
            }
            for q in path.quantifiers.iter().rev() {
                ty = Term::pi(q.clone(), ty);
            }
            ty
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
    // Unchanged from the original schema: still requires every point constructor to
    // be *nullary* (see module docs — extending the dependent eliminator to fielded
    // point constructors is future work), so this is only installed in that case.
    // ------------------------------------------------------------------
    let all_nullary = spec.points.iter().all(|p| p.fields.is_empty());
    if all_nullary {
        let ind_target = Term::app(Term::Var(n + 1), Term::Var(0));
        let mut ind_ty = Term::pi(h_ty.clone(), ind_target);
        let total_before_t_ind = 1 + n;
        for dst in (0..total_before_t_ind).rev() {
            let binder_ty = if dst == 0 {
                Term::arrow(h_ty.clone(), Term::prop())
            } else {
                let beta_idx = dst - 1;
                Term::app(Term::Var(beta_idx), point_head(dst - 1))
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
    }

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

    /// Worked example 1: the interval `I`, two (nullary) points and one path — `i0 :
    /// I`, `i1 : I`, `seg : Eq I i0 i1`.
    fn interval_spec() -> HitSpec {
        HitSpec {
            type_name: "Interval".to_string(),
            points: vec![PointSpec::nullary("Interval.i0"), PointSpec::nullary("Interval.i1")],
            paths: vec![PathSpec::simple("Interval.seg", 0, 1)],
        }
    }

    /// Worked example 2: a 3-cycle `Z3` — three nullary points and three paths.
    fn z3_spec() -> HitSpec {
        HitSpec {
            type_name: "Z3".to_string(),
            points: vec![
                PointSpec::nullary("Z3.p0"),
                PointSpec::nullary("Z3.p1"),
                PointSpec::nullary("Z3.p2"),
            ],
            paths: vec![
                PathSpec::simple("Z3.e01", 0, 1),
                PathSpec::simple("Z3.e12", 1, 2),
                PathSpec::simple("Z3.e20", 2, 0),
            ],
        }
    }

    /// Worked example 3 (**fielded, non-recursive**): a set-quotient of `Nat` by a
    /// fixed relation `R`. `NatModR.mk : Nat → NatModR`, `NatModR.glue : Π a b, R a b
    /// → mk a = mk b` — exactly the "quotient as a user-declared HIT" example from the
    /// module docs, with `R` a concrete, previously-declared relation. `R` itself is
    /// installed as a plain top-level `Axiom` by `nat_mod_r_env` before the HIT is
    /// declared; `declare_hit` never inspects `R`'s definition.
    fn nat_mod_r_spec() -> HitSpec {
        let nat = || cn("Nat");
        let r = || cn("NatModR.R");
        HitSpec {
            type_name: "NatModR".to_string(),
            points: vec![PointSpec { name: "NatModR.mk".to_string(), fields: vec![Field::NonRec(nat())] }],
            paths: vec![PathSpec {
                name: "NatModR.glue".to_string(),
                quantifiers: vec![nat(), nat()],
                // premise: R a b, in context [a, b] (a = Var(1), b = Var(0))
                premise: Some(Term::apps(r(), [Term::Var(1), Term::Var(0)])),
                // field args, in context [a, b, premise] (a = Var(2), b = Var(1))
                lhs: (0, vec![Term::Var(2)]),
                rhs: (0, vec![Term::Var(1)]),
            }],
        }
    }

    fn nat_mod_r_env() -> Env {
        let mut env = base_env();
        let nat = || cn("Nat");
        let r_ty = Term::arrow(nat(), Term::arrow(nat(), Term::prop()));
        env.insert(name("NatModR.R"), Decl::Axiom { num_levels: 0, ty: r_ty }).unwrap();
        declare_hit(&mut env, &nat_mod_r_spec()).unwrap();
        env
    }

    /// Worked example 4 (**fielded, recursive**): a free-monoid-like list of `Nat`,
    /// with no path constructors — exercises the recursive ι-rule (`Field::Rec`)
    /// standalone. `unit : FreeMonoid`, `cons : Nat → FreeMonoid → FreeMonoid`.
    fn free_monoid_spec() -> HitSpec {
        HitSpec {
            type_name: "FreeMonoid".to_string(),
            points: vec![
                PointSpec::nullary("FreeMonoid.unit"),
                PointSpec {
                    name: "FreeMonoid.cons".to_string(),
                    fields: vec![Field::NonRec(cn("Nat")), Field::Rec],
                },
            ],
            paths: vec![],
        }
    }

    fn free_monoid_env() -> Env {
        let mut env = base_env();
        declare_hit(&mut env, &free_monoid_spec()).unwrap();
        env
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
    fn nat_mod_r_constants_wellformed() {
        let env = nat_mod_r_env();
        let chk = Checker::new(&env);
        // No `NatModR.ind` — the type has a fielded point constructor.
        for n in ["NatModR", "NatModR.mk", "NatModR.glue", "NatModR.rec"] {
            chk.infer_closed(env.get(n).unwrap().ty()).unwrap_or_else(|e| panic!("{n} ill-formed: {e}"));
        }
        assert!(env.get("NatModR.ind").is_none(), "no dependent eliminator for a fielded HIT");
    }

    #[test]
    fn free_monoid_constants_wellformed() {
        let env = free_monoid_env();
        let chk = Checker::new(&env);
        for n in ["FreeMonoid", "FreeMonoid.unit", "FreeMonoid.cons", "FreeMonoid.rec"] {
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
        let spec = HitSpec { type_name: "Bad".to_string(), points: vec![], paths: vec![] };
        let err = declare_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("at least one point"), "got: {err}");
    }

    #[test]
    fn spec_rejects_bad_path_index() {
        let mut env = base_env();
        let spec = HitSpec {
            type_name: "Bad".to_string(),
            points: vec![PointSpec::nullary("Bad.p0")],
            paths: vec![PathSpec::simple("Bad.e", 0, 5)],
        };
        let err = declare_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("out of range"), "got: {err}");
    }

    /// SOUNDNESS (adversarial): a non-recursive field mentioning `H` itself is
    /// rejected (only a bare `Field::Rec` slot may recur — strict positivity).
    #[test]
    fn nonrec_field_mentioning_self_rejected() {
        let mut env = base_env();
        let spec = HitSpec {
            type_name: "Bad".to_string(),
            points: vec![PointSpec {
                name: "Bad.p0".to_string(),
                // A non-recursive field whose *type* mentions `Bad` — e.g. `Bad → Nat` —
                // is not a bare recursive occurrence and must be rejected.
                fields: vec![Field::NonRec(Term::arrow(Term::cnst(name("Bad"), vec![]), cn("Nat")))],
            }],
            paths: vec![],
        };
        let err = declare_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("strict positivity") || err.contains("mentioning"), "got: {err}");
    }

    /// SOUNDNESS (adversarial): a path constructor may not target a point constructor
    /// with a recursive field (see module docs, "Supported class").
    #[test]
    fn path_touching_recursive_point_rejected() {
        let mut env = base_env();
        let spec = HitSpec {
            type_name: "Bad".to_string(),
            points: vec![
                PointSpec::nullary("Bad.unit"),
                PointSpec {
                    name: "Bad.cons".to_string(),
                    fields: vec![Field::NonRec(cn("Nat")), Field::Rec],
                },
            ],
            paths: vec![PathSpec {
                name: "Bad.oops".to_string(),
                quantifiers: vec![],
                premise: None,
                lhs: (0, vec![]),
                rhs: (1, vec![lit(0), Term::cnst(name("Bad.unit"), vec![])]),
            }],
        };
        let err = declare_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("recursive field"), "got: {err}");
    }

    /// SOUNDNESS (adversarial): a path field-argument count mismatch is rejected.
    #[test]
    fn path_field_arity_mismatch_rejected() {
        let mut env = base_env();
        let spec = HitSpec {
            type_name: "Bad".to_string(),
            points: vec![PointSpec { name: "Bad.mk".to_string(), fields: vec![Field::NonRec(cn("Nat"))] }],
            paths: vec![PathSpec {
                name: "Bad.e".to_string(),
                quantifiers: vec![],
                premise: None,
                lhs: (0, vec![lit(0)]),
                rhs: (0, vec![]), // wrong arity: Bad.mk needs exactly one field
            }],
        };
        let err = declare_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("arity"), "got: {err}");
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
        let c = lit(7);
        let resp_ok = refl(u.clone(), cn("Nat"), c.clone());
        for pt in ["Interval.i0", "Interval.i1"] {
            let rec = Term::apps(
                Term::cnst(name("Interval.rec"), vec![u.clone()]),
                [cn("Nat"), c.clone(), c.clone(), resp_ok.clone(), cn(pt)],
            );
            let chk = Checker::new(&env);
            chk.check(&mut LocalCtx::new(), &rec, &cn("Nat")).unwrap();
            let red = Reducer::new(&env);
            assert!(red.is_def_eq(&rec, &c), "reducer: rec {pt} = case");
            let nbe = crate::nbe::Nbe::new(&env);
            assert_eq!(nbe.normalize(&rec), nbe.normalize(&c), "nbe: rec {pt} = case");
        }
    }

    /// SOUNDNESS (adversarial): a `resp` that does NOT actually witness `Eq P case_0
    /// case_1` (mismatched cases) is rejected by the checker before `H.rec` can even
    /// be formed.
    #[test]
    fn mismatched_resp_rejected() {
        let env = interval_env();
        let u = Level::of_nat(1);
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
    /// belonging to a *different* declared HIT, even though roles overlap. Both are
    /// declared in one env; applying `Interval.rec` to `Z3.p0` must be ill-typed.
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

    /// `H.rec` stays stuck on a partially-applied (under-arity) point constructor —
    /// only reachable for ill-typed input, but the ι-rule itself must not misfire.
    #[test]
    fn rec_stuck_on_underapplied_point() {
        let env = free_monoid_env();
        let u = Level::of_nat(1);
        let c0 = lit(0);
        let cons_case = Term::lam(cn("Nat"), Term::lam(cn("Nat"), Term::Var(1)));
        let partial = Term::app(Term::cnst(name("FreeMonoid.cons"), vec![]), lit(3)); // missing the tail
        let rec = Term::apps(
            Term::cnst(name("FreeMonoid.rec"), vec![u.clone()]),
            [cn("Nat"), c0, cons_case, partial],
        );
        let red = Reducer::new(&env);
        // whnf must not crash and must not reduce past the stuck applied-point head.
        let result = red.whnf(&rec);
        assert!(matches!(result.unfold_apps().0, Term::Const(n, _) if n == name("FreeMonoid.rec")));
    }

    // ---------------------------------------------------------------- recursor (n=3,m=3)

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

    // ---------------------------------------------------------------- fielded recursor (NatModR)

    /// COMPUTATION RULE for the fielded, non-recursive `NatModR`: `NatModR.rec P case
    /// resp (NatModR.mk a) ↦ case a`, differential reducer vs. NbE.
    #[test]
    fn nat_mod_r_rec_computes() {
        let env = nat_mod_r_env();
        let u = Level::of_nat(1);
        // motive: constant Nat; case := λ_, 0 (constant), whose resp is trivially refl.
        let case = Term::lam(cn("Nat"), lit(0));
        let resp = Term::lam(
            cn("Nat"),
            Term::lam(
                cn("Nat"),
                Term::lam(
                    Term::apps(cn("NatModR.R"), [Term::Var(1), Term::Var(0)]),
                    refl(u.clone(), cn("Nat"), lit(0)),
                ),
            ),
        );
        let scrut = Term::app(Term::cnst(name("NatModR.mk"), vec![]), lit(42));
        let rec = Term::apps(
            Term::cnst(name("NatModR.rec"), vec![u.clone()]),
            [cn("Nat"), case, resp, scrut],
        );
        let chk = Checker::new(&env);
        chk.check(&mut LocalCtx::new(), &rec, &cn("Nat")).unwrap();
        let red = Reducer::new(&env);
        assert!(red.is_def_eq(&rec, &lit(0)), "reducer: NatModR.rec (mk 42) = 0");
        let nbe = crate::nbe::Nbe::new(&env);
        assert_eq!(nbe.normalize(&rec), nbe.normalize(&lit(0)), "nbe: NatModR.rec (mk 42) = 0");
    }

    // ---------------------------------------------------------------- fielded+recursive recursor (FreeMonoid)

    /// COMPUTATION RULE for the fielded, **recursive** `FreeMonoid`: sums a list-like
    /// value via `Nat.rec`-style accumulation, exercising the recursive ι-substitution
    /// (`H.rec` calling itself on the `Field::Rec` field). `sum (cons 3 (cons 4 unit))
    /// = 7`, differential reducer vs. NbE.
    #[test]
    fn free_monoid_rec_computes_recursively() {
        let env = free_monoid_env();
        let u = Level::of_nat(1);
        let add = |m: Term, n: Term| {
            Term::apps(
                Term::cnst(name("Nat.rec"), vec![Level::of_nat(1)]),
                [
                    Term::lam(cn("Nat"), cn("Nat")),
                    n,
                    Term::lam(cn("Nat"), Term::lam(cn("Nat"), Term::app(cn("Nat.succ"), Term::Var(0)))),
                    m,
                ],
            )
        };
        let cons_case = Term::lam(cn("Nat"), Term::lam(cn("Nat"), add(Term::Var(1), Term::Var(0))));
        let sum = |scrut: Term| {
            Term::apps(
                Term::cnst(name("FreeMonoid.rec"), vec![u.clone()]),
                [cn("Nat"), lit(0), cons_case.clone(), scrut],
            )
        };
        let cons = |n: Term, tail: Term| Term::apps(Term::cnst(name("FreeMonoid.cons"), vec![]), [n, tail]);
        let unit = || cn("FreeMonoid.unit");
        let list = cons(lit(3), cons(lit(4), unit()));
        let expr = sum(list);
        let chk = Checker::new(&env);
        chk.check(&mut LocalCtx::new(), &expr, &cn("Nat")).unwrap();
        let red = Reducer::new(&env);
        assert!(red.is_def_eq(&expr, &lit(7)), "reducer: sum [3,4] = 7");
        let nbe = crate::nbe::Nbe::new(&env);
        assert_eq!(nbe.normalize(&expr), nbe.normalize(&lit(7)), "nbe: sum [3,4] = 7");

        // Base case: sum unit = 0.
        let base = sum(unit());
        assert!(red.is_def_eq(&base, &lit(0)));
        assert_eq!(nbe.normalize(&base), nbe.normalize(&lit(0)));
    }

    // ---------------------------------------------------------------- H.ind

    #[test]
    fn interval_ind_applies() {
        let env = interval_env();
        let u = Level::of_nat(1);
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
    /// definitional equality that only a (propositional) path constructor grants.
    #[test]
    fn no_definitional_collapse_with_multiple_hits_declared() {
        let mut env = interval_env();
        declare_hit(&mut env, &z3_spec()).unwrap();
        let red = Reducer::new(&env);
        assert!(!red.is_def_eq(&cn("Interval.i0"), &cn("Interval.i1")));
        assert!(!red.is_def_eq(&cn("Z3.p0"), &cn("Z3.p1")));
        assert!(!red.is_def_eq(&cn("Z3.p1"), &cn("Z3.p2")));
    }

    /// ADVERSARIAL: two distinct `FreeMonoid` values built from distinct field data
    /// (`cons 3 unit` vs. `cons 4 unit`) stay definitionally distinct — a fielded
    /// point constructor's field carries real information, not erased to a bare tag.
    #[test]
    fn fielded_points_with_different_fields_stay_distinct() {
        let env = free_monoid_env();
        let cons = |n: Term| Term::apps(Term::cnst(name("FreeMonoid.cons"), vec![]), [n, cn("FreeMonoid.unit")]);
        let red = Reducer::new(&env);
        assert!(!red.is_def_eq(&cons(lit(3)), &cons(lit(4))));
    }
}
