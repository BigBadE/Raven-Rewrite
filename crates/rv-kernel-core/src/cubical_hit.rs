//! A **general, user-declarable cubical HIT schema** — `declare_cubical_hit` —
//! generalizing [`crate::interval_hit`]'s `I2` and [`crate::circle_cubical`]'s
//! `S1c` into one parameterized mechanism, now extended to **fielded point
//! constructors** (see "Fielded point recursor" below).
//!
//! ## Supported class
//!
//! A cubical HIT `H` presented by:
//!
//!   * `n ≥ 1` **point constructors** `H.point_0, …, H.point_{n-1}`, each with its
//!     own (possibly empty) list of [`Field`]s — a field is either [`Field::Rec`]
//!     (a strictly-positive recursive occurrence of `H` itself) or
//!     [`Field::NonRec`] (a fixed, closed, `H`-free type) — mirroring
//!     [`crate::hit`]'s propositional schema exactly; `H.point_i : field_0 → … →
//!     field_{k_i-1} → H`, and
//!   * `m ≥ 0` genuine **cubical path constructors** `H.path_0, …, H.path_{m-1}`,
//!     each optionally **quantified** over extra variables (mirroring
//!     [`crate::hit::PathSpec`]'s quantifiers — enough to express a genuine
//!     `Π a b, R a b → …` premise), relating two applications of point
//!     constructors *to concrete field arguments*:
//!     `H.path_j : Π q_0 … q_{k-1}, Path H (H.point_{lhs_j} a_0..) (H.point_{rhs_j} b_0..)`
//!     — a real [`crate::term::Term::PathP`]-classified path (built on
//!     [`crate::cubical`]'s `PLam`/`PApp`/`PathP`, *not* the inductive `Eq`).
//!     `lhs_j == rhs_j` is legal (a self-loop); `lhs_j != rhs_j` connects two
//!     distinct points. **Restriction** (see "What's deferred"): the point
//!     constructors a path targets must have **no `Field::Rec` field** — no
//!     recursive point constructor may be a path endpoint, and
//!   * a **`Type`-valued, computing, motive-dependent** recursor
//!
//! ```text
//!   H.rec.{v} : Π (C : H → Sort v)
//!                 (c_0 : …) … (c_{n-1} : …)
//!                 (s_0 : …) … (s_{m-1} : …)
//!                 (x : H), C x
//! ```
//!
//! where each `c_i` (a **fielded point recursor** case — see below) and each `s_j`
//! (a **quantified path recursor** case) are synthesized generically from the
//! declared shape, with `n + m` ι-rules:
//!
//! ```text
//!   H.rec C c_.. s_.. (H.point_i a_0..a_{k-1})       ↦  c_i b_0 .. b_{k-1}
//!     where b_j = a_j                            if field_j is Field::NonRec
//!           b_j = a_j (H.rec C c_.. s_.. a_j)     if field_j is Field::Rec
//!                                                 (the field itself, THEN its IH)
//!   H.rec C c_.. s_.. (H.path_j q_0..q_{k-1} @ r)    ↦  (s_j q_0..q_{k-1}) @ r
//! ```
//!
//! ## Fielded point recursor
//!
//! For a nullary point (`k=0`) this is exactly the original schema's
//! `c_i : C point_i`. For a fielded point `H.point_i : A → H → H` (say, field 0
//! non-recursive of type `A`, field 1 recursive), the case is the same shape an
//! *ordinary* dependent inductive recursor generates for a fielded constructor
//! (e.g. `Nat.rec`'s `succ`-case `Π (n:Nat), C n → C (succ n)`, generalized to
//! arbitrary field lists):
//!
//! ```text
//!   c_i : Π (a : A) (x : H), C x → C (H.point_i a x)
//! ```
//!
//! i.e. **every** field keeps its original type (`A`, or `H` for a `Field::Rec`
//! slot — unlike [`crate::hit`]'s *non-dependent* schema, which collapses a
//! `Field::Rec` slot straight to the already-computed result `P`, this schema's
//! motive-**dependent** `C` needs the original recursive value too, so it stays,
//! `H`-typed), and each `Field::Rec` slot gets one **extra trailing induction
//! hypothesis** binder `C x` (`x` the field just bound) before moving to the next
//! field — exactly `crate::generate`'s dependent-recursor construction, specialized
//! to this schema's single motive `C`. The ι-rule ([`Self::point_case_ty`]'s
//! reduction counterpart, [`crate::reduce::Reducer::try_cubical_hit_rec`]/
//! [`crate::nbe::Nbe::try_cubical_hit_rec`]) applies `c_i` to the field values
//! *interleaved* with a freshly-built recursive `H.rec …` call for each
//! `Field::Rec` field — mirroring [`crate::hit::declare_hit`]'s
//! `try_hit_rec`/its NbE counterpart move-for-move (see those functions' doc
//! comments), just inserting the extra field-value argument this schema's richer,
//! dependent case type requires.
//!
//! ## Quantified path recursor case
//!
//! A quantified `H.path_j : Π q.., Path H (point_lhs a..) (point_rhs b..)` gets a
//! recursor case of the *same* shape, quantified identically:
//!
//! ```text
//!   s_j : Π q_0..q_{k-1}, PathP (λi. C (H.path_j q.. @ i)) (c_lhs a..) (c_rhs b..)
//! ```
//!
//! (`c_lhs`/`c_rhs` here are the *case* functions for the endpoint point
//! constructors, applied to the same field arguments `a../b..` the path spec
//! itself uses — valid because path endpoints are restricted to **non-recursive**
//! point constructors, so `a../b..` are themselves plain field values, never
//! requiring translation through an IH). The path ι-rule fires when the scrutinee
//! weak-head-reduces to `H.path_j` applied to exactly its `k` quantifier
//! arguments, `@`-applied to an interval value `r`: `H.rec .. (H.path_j q.. @ r) ↦
//! (s_j q..) @ r`.
//!
//! This is *exactly* [`crate::interval_hit`]'s `I2` (`n=2`, one unquantified path,
//! distinct endpoints, all-nullary points) and [`crate::circle_cubical`]'s `S1c`
//! (`n=1`, one unquantified path, self-loop, nullary point), generalized to
//! arbitrary `n`/`m` **and** fielded points/quantified paths — see
//! `tests::rederive_i2`/`tests::rederive_s1c` below, which re-declare both through
//! this schema (with empty field lists / no quantifiers) and confirm they
//! type-check and *compute* identically to the hand-coded originals.
//!
//! ## Worked example: a fielded HIT the nullary schema couldn't express
//!
//! `tests::natsq_spec` declares a **set-quotient-flavored** cubical HIT `NatSQ`:
//! `mk : Nat → NatSQ` (a fielded, non-recursive point) and `glue : Π a b, R a b →
//! Path NatSQ (mk a) (mk b)` (a quantified path constructor with the SAME fielded
//! point as both endpoints) — neither expressible by the original nullary-only
//! schema. `tests::free_monoid_cubical_spec` separately exercises a fielded,
//! **recursive** point (`cons : Nat → FreeMonoidC → FreeMonoidC`, no paths) to
//! isolate the recursive-field ι-substitution from the quantified-path machinery.
//!
//! ## 2-dimensional (higher) path constructors: `S²`
//!
//! `p ≥ 0` genuinely **2-dimensional cubical "surface" (2-path) constructors**
//! `H.surf_0, …, H.surf_{p-1}` — see [`CubSurfSpec`] — are also supported, in the
//! **"S²" shape**: each `H.surf_k : Path (Path H p p) (refl p) (refl p)`, a
//! square/2-cell whose all four boundaries are `refl` at a single **nullary**
//! point constructor `p`. `tests::s2_spec` declares the sphere `S²` this way:
//! one point `S2g.base`, one 2-cell `S2g.surf : Path (Path S2g base base) (refl
//! base) (refl base)` — the simplest HIT the 1-path-only schema above cannot
//! express at all (no `Path`-classified term can itself be a *point* of `H`, so
//! a genuine "loop of loops" needs a strictly higher-dimensional constructor).
//! The recursor gains one **doubly-quantified `PathP`** case per surface,
//!
//! ```text
//!   t_k : PathP (λi. PathP (λj. C (H.surf_k @ i @ j)) c_base c_base)
//!               (refl c_base) (refl c_base)
//! ```
//!
//! (`c_base` the base point's own recursor case — trivial, since `base` is
//! nullary), with ι-rule `H.rec .. (H.surf_k @ i @ j) ↦ (t_k @ i) @ j` — see
//! [`Self::declare_cubical_hit`]'s surface-declaration block and
//! [`crate::reduce::Reducer::try_cubical_hit_rec`]/
//! [`crate::nbe::Nbe::try_cubical_hit_rec`]'s surface arms (tried *before* the
//! ordinary 1-path arm in both, since a surface's doubly-`PApp`-applied
//! scrutinee shape is structurally a special case of the 1-path arm's broader
//! `PApp(p, r)` pattern — see those functions' doc comments for exactly how the
//! two are disambiguated without cross-firing). Getting `t_k`'s own type to
//! *type-check* required one small, general extension to
//! [`crate::check::Checker::path_boundary_one`] — chasing one extra level of the
//! same boundary equation it already establishes for ordinary 1-paths (see that
//! function's updated doc comment for the exact addition and its soundness
//! argument); no change to [`crate::reduce`]'s untyped reduction rules was
//! needed or made (the reducer/NbE ι-rules above are ordinary, narrowly-scoped
//! *reduction* rules, structurally disjoint from that *typing-time* boundary
//! extension).
//!
//! `tests::s2_surf_iota_computes_and_boundary_agrees` checks the ι-rule computes
//! for a concrete witness and that all four corners (`i0`/`i1` × `j0`/`j1`)
//! agree with the point rule; `tests::rejects_surf_based_at_fielded_point`/
//! `tests::rejects_surf_out_of_range_base` are the adversarial rejection tests;
//! `tests::no_cross_fire_between_two_distinct_s2_hits`/
//! `tests::cannot_prove_false_via_surf_schema` mirror the 1-path schema's
//! identical soundness tests one dimension up.
//!
//! ## What's deferred
//!
//! * **Path constructors touching a recursive point constructor** — the path
//!   endpoint restriction above (mirrors [`crate::hit`]'s identical restriction and
//!   for the identical reason: `s_j`'s type would need to embed a recursive
//!   `H.rec` call in its own boundary, which is sound in principle but a
//!   materially larger change than fielded points + quantified paths asked for
//!   here).
//! * **Dependent field telescopes** (a field's type depending on an earlier
//!   field's value) — every `Field::NonRec(t)` must be closed, matching
//!   [`crate::hit`]'s identical restriction.
//! * **A genuinely dependent eliminator requiring `hcomp`/`transp` beyond direct
//!   `PathP` application** (composing across multiple path constructors) — not
//!   attempted, as before.
//! * **The fully general 2-path ("square") schema** — an arbitrary square `c :
//!   PathP (λi. Path H (l @ i) (r @ i)) p q` between two *arbitrary, possibly
//!   distinct* declared 1-paths `l`/`r` (e.g. the torus `T²`'s `surf : p·q ≡
//!   q·p`), rather than the "S²" restriction landed here (all four sides `refl`
//!   at one nullary point). Only the "S²" shape is implemented — see the
//!   section above. A general square's boundary coherence would need the
//!   **general** (not one-level-bounded) version of the
//!   `path_boundary_one` extension described above, plus quantified/fielded
//!   surfaces analogous to §"Quantified path recursor case" — a materially
//!   larger change deferred in favor of landing a genuinely sound, if simpler,
//!   higher HIT.
//! * **3-dimensional (or higher) path constructors** — not attempted; the
//!   `path_boundary_one` extension above is bounded to exactly one extra level
//!   (matching this schema's "at most 2-dimensional" scope).
//! * **Indexed/parametric HITs** (`H` itself taking parameters or indices) — out of
//!   scope, as `crate::hit`'s module doc argues for its identical restriction.
//!
//! ## Why this is SOUND
//!
//! Structurally identical to the original schema's soundness argument (see the
//! previous revision's "Why this is SOUND" section, preserved by every test below
//! that re-derives `I2`/`S1c`/figure-eight through the now-fielded machinery with
//! empty field lists), extended for the two new axes:
//!
//! * **No new checking rule, for fielded points either.** Every constant remains
//!   an ordinary typed [`crate::env::Decl::CubHit`] constant, checked once at
//!   `declare_cubical_hit` time by the *pre-existing* `Term::Pi`/`Term::PathP`
//!   typing rules — a fielded point constructor's type is just an ordinary
//!   (possibly-recursive) `Π`-telescope ending in `H`, exactly like any inductive
//!   constructor; no new typing rule is added for "cubical HIT" at all, fielded or
//!   not.
//! * **Strict positivity is enforced by construction and checked at declaration
//!   time**, verbatim mirroring [`crate::hit`]'s identical check: every
//!   `Field::NonRec(t)` is rejected if `t` mentions `H`'s own type former anywhere
//!   (`occurs_const`) — the *only* way `H` may appear in a field is as the entire
//!   field (`Field::Rec`), never nested inside another type (adversarial test
//!   `rejects_nonrec_field_mentioning_self`).
//! * **Generically synthesized, narrowly-scoped ι-rules**
//!   ([`crate::reduce::Reducer::try_cubical_hit_rec`],
//!   [`crate::nbe::Nbe::try_cubical_hit_rec`], differentially cross-checked by
//!   every test below): the point rule fires only on a literal `H.point_i`
//!   *fully applied to exactly its declared field arity* — a partially-applied
//!   point constructor (fewer args than its arity) or a neutral stays stuck
//!   (adversarial test `rec_stuck_on_underapplied_fielded_point`); the path rule
//!   fires only when the scrutinee's weak-head form is *literally* `H.path_j`
//!   applied to exactly its declared quantifier arity, `@`-applied to `r`, for the
//!   *same* HIT `id` as the `H.rec` head being reduced — never on a neutral, never
//!   cross-firing against a different declared HIT's constructors (guarded by
//!   `id`, exactly as before; adversarial test
//!   `no_cross_fire_between_two_distinct_declared_hits`).
//! * **The recursive-field ι-substitution is the same move as
//!   [`crate::hit::declare_hit`]'s `try_hit_rec`** (only inserting the extra
//!   original-field-value argument this schema's dependent case type requires
//!   before its IH) — soundness carries over identically: the recursive
//!   `H.rec …` call is only ever built from the *same* `C`/case/resp arguments
//!   already in scope, applied to a strictly smaller field value (never
//!   fabricating a value from nothing), so no new closed inhabitant of any type is
//!   manufactured beyond what the caller-supplied cases/paths already produce
//!   (adversarial test `free_monoid_cubical_rec_computes_recursively`, plus
//!   reducer/NbE differential checks throughout).
//! * **Endpoint coherence** is the same *derived*, no-new-equation fact the
//!   original schema relies on, now for quantified paths too: each `s_j`'s own
//!   declared type is checked against `path_j`'s own declared boundary at
//!   `H.rec`'s *formation* site (the ordinary `PathP` well-formedness obligation,
//!   now under the `s_j`'s own quantifier telescope), and at *reduction* time
//!   [`crate::check::Checker::path_boundary`] (proven sound in [`crate::cubical`]'s
//!   Phase 1) gives the boundary equations definitionally for every instantiation
//!   of the quantifiers — so the path ι-rule's boundary values agree with the
//!   point ι-rule's values for every `j` and every quantifier instantiation,
//!   without any new checking or reduction rule (test
//!   `natsq_glue_self_relation_boundary_computes` checks this explicitly at both
//!   `i0`/`i1` for a concretely-reducing witness — see that test's doc comment
//!   for why an *opaque* `resp` witness's boundary is a checked, not reduced,
//!   fact).
//! * **Canonicity.** The `n` point constructors (now fielded) remain the only
//!   closed point-shaped normal forms of `H` up to their field values — two
//!   applications of the same fielded point constructor to *different* field data
//!   stay definitionally distinct (test
//!   `fielded_points_with_different_fields_stay_distinct`); `H.path_j …` is
//!   always `Path`-classified, never `H`-classified, so it can never appear as a
//!   closed value *of type `H`* — only `H.path_j … @ r` can, handled precisely by
//!   the path ι-rule.
//! * **Anti-`False`.** No new equation is manufactured between unrelated closed
//!   terms: `H.rec`'s path ι-rule only ever returns `(s_j q..) @ r` for the
//!   caller-*supplied* `s_j`; distinct point constructors (or the same one with
//!   distinct field data) of `H` stay non-definitionally-equal (checked below,
//!   including for the new `NatSQ`/`FreeMonoidC` examples); no `Path Nat 0 1`/
//!   `Empty` is derivable (adversarial test `cannot_prove_false_via_generic_schema`).
//! * **Reducer/NbE agreement.** Both ι-rules are implemented once each,
//!   structurally mirroring one another exactly (generalized over fielded points
//!   and quantified paths, guarded by `id`); every test below checks both
//!   independently and compares normal forms.
//! * **The 2-path ("S²") schema adds no new checking or reduction primitive
//!   either.** `H.surf_k`'s declared type is an ordinary `PathP`-of-`PathP`,
//!   checked by the *pre-existing* `Term::PathP` formation rule (twice,
//!   structurally) — exactly like every other constant this module declares;
//!   its ι-rule ([`crate::reduce::Reducer::try_cubical_hit_rec`]/
//!   [`crate::nbe::Nbe::try_cubical_hit_rec`]'s surface arms) fires *only* on a
//!   literal, doubly-`PApp`-applied `H.surf_k @ i @ j` for the *same* HIT `id`
//!   — never on a singly-applied surface (which isn't even `H`-typed — its type
//!   is `Path H p p` — adversarial test `rec_stuck_on_underapplied_surf`), a
//!   neutral, or a different HIT's surface (guarded by `id`, test
//!   `no_cross_fire_between_two_distinct_s2_hits`). The one genuinely new piece
//!   is [`crate::check::Checker::path_boundary_one`]'s one-level-deeper nested
//!   boundary case (needed to type-check `t_k`'s own `PathP`-of-`PathP` goal) —
//!   which, per that function's own doc comment, derives no equation beyond
//!   what the inner `PApp`'s own already-checked `PathP` typing judgement
//!   already forces; it is a **typing-time** extension only, entirely disjoint
//!   from the (unmodified) untyped reduction rules in `crate::reduce`/
//!   `crate::nbe`. Anti-`False` (test `cannot_prove_false_via_surf_schema`) and
//!   reducer/NbE agreement (test `s2_surf_iota_computes_and_boundary_agrees`)
//!   are checked exactly as for the 1-path schema, one dimension up.

use crate::env::{CubHit, CubHitRole, Decl, Env};
use crate::level::Level;
use crate::term::{name, Name, Term};
use std::rc::Rc;

/// A field of a point constructor: either a strictly-positive recursive occurrence
/// of the HIT being declared, or a fixed, closed, `H`-free type. Mirrors
/// [`crate::hit::Field`] exactly (see that module's doc for the strict-positivity
/// argument this schema reuses verbatim) — duplicated here (rather than shared)
/// to keep this module's public API self-contained and independently ownable.
#[derive(Clone, Debug)]
pub enum Field {
    /// A recursive field of type `H` itself.
    Rec,
    /// A non-recursive field of a fixed closed type, which must not mention `H`'s
    /// own type former (checked by `declare_cubical_hit`; strict positivity).
    NonRec(Term),
}

/// A user's declaration of one point constructor: a name plus its (possibly empty,
/// possibly recursive) field list.
#[derive(Clone, Debug)]
pub struct CubPointSpec {
    pub name: String,
    pub fields: Vec<Field>,
}

impl CubPointSpec {
    /// A nullary point constructor — the original, pre-fielded schema's shape.
    pub fn nullary(name: impl Into<String>) -> Self {
        CubPointSpec { name: name.into(), fields: Vec::new() }
    }
}

/// A user's declaration of one cubical path constructor:
/// `H.name : Π quantifiers.., Path H (H.point_{lhs.0} lhs.1..) (H.point_{rhs.0} rhs.1..)`.
///
/// `quantifiers` and the `lhs.1`/`rhs.1` field-argument terms follow exactly
/// [`crate::hit::PathSpec`]'s de Bruijn convention: `quantifiers[i]`'s type is
/// written in the context of `quantifiers[0..i]` (innermost = most-recently
/// quantified = `Var(0)`), and `lhs.1`/`rhs.1` are raw terms in the context of
/// *all* quantifiers (so a premise like `R a b` is just the last quantifier's
/// type, `Π a b (h : R a b), ..` — no separate "premise" slot is needed).
#[derive(Clone, Debug)]
pub struct CubPathSpec {
    pub name: String,
    /// Types of extra universally-quantified variables, outermost first.
    pub quantifiers: Vec<Term>,
    /// `(point index, field arguments)` for the left endpoint. The targeted point
    /// constructor must have **no `Field::Rec` field** (see the module doc,
    /// "What's deferred").
    pub lhs: (usize, Vec<Term>),
    /// `(point index, field arguments)` for the right endpoint.
    pub rhs: (usize, Vec<Term>),
}

impl CubPathSpec {
    /// An unquantified path constructor between two nullary point constructors —
    /// the original, pre-generalized schema's shape.
    pub fn simple(name: impl Into<String>, lhs: usize, rhs: usize) -> Self {
        CubPathSpec {
            name: name.into(),
            quantifiers: Vec::new(),
            lhs: (lhs, Vec::new()),
            rhs: (rhs, Vec::new()),
        }
    }
}

/// A user's declaration of one **2-dimensional ("surface"/higher) path
/// constructor** — restricted to the "S²" shape (see the module doc,
/// "2-dimensional (higher) path constructors"): a square/2-cell based at a
/// single **nullary** point constructor, `H.name : Path (Path H p p) (refl p)
/// (refl p)` where `p = H.point_{base}`. This is deliberately *not* the fully
/// general square-with-arbitrary-1-path-sides schema (deferred — see the module
/// doc's "What's deferred") — landing the simplest genuinely-higher case (`S²`)
/// soundly, rather than a broken general one.
#[derive(Clone, Debug)]
pub struct CubSurfSpec {
    pub name: String,
    /// The (must be **nullary** — arity 0) point constructor this 2-cell is
    /// based at, all four ways round.
    pub base: usize,
}

/// A user-supplied specification of a cubical HIT: its type-former name, its
/// (possibly fielded) point constructors, its (possibly quantified) path
/// constructors, and its (S²-shaped) 2-path ("surface") constructors. See the
/// module doc for the exact supported class.
#[derive(Clone, Debug)]
pub struct CubHitSpec {
    pub name: String,
    pub points: Vec<CubPointSpec>,
    pub paths: Vec<CubPathSpec>,
    pub surfaces: Vec<CubSurfSpec>,
}

impl CubHitSpec {
    /// The name of the generated recursor, `"{name}.rec"`.
    pub fn rec_name(&self) -> String {
        format!("{}.rec", self.name)
    }
}

/// Does `t` mention the constant `id` anywhere (used for strict-positivity
/// checking of non-recursive fields)? A verbatim copy of
/// [`crate::hit`]'s identical helper (duplicated rather than shared to keep this
/// module self-contained — see the module doc).
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
        Term::INeg(r) => occurs_const(r, id),
        Term::IMeet(r, s) | Term::IJoin(r, s) => occurs_const(r, id) || occurs_const(s, id),
        Term::Sort(_) | Term::Var(_) | Term::Meta(_) | Term::I | Term::IZero | Term::IOne => false,
        Term::Sys(branches) => branches.iter().any(|(_, t)| occurs_const(t, id)),
        Term::Partial(_, a) => occurs_const(a, id),
        Term::Transp(fam, _, a) => occurs_const(fam, id) || occurs_const(a, id),
        Term::HComp(ty, _, u, u0) => {
            occurs_const(ty, id) || occurs_const(u, id) || occurs_const(u0, id)
        }
        Term::Glue(a, branches) => {
            occurs_const(a, id) || branches.iter().any(|(_, t2, e)| occurs_const(t2, id) || occurs_const(e, id))
        }
        Term::Unglue(a, branches, u) => {
            occurs_const(a, id)
                || branches.iter().any(|(_, t2, e)| occurs_const(t2, id) || occurs_const(e, id))
                || occurs_const(u, id)
        }
        Term::GlueIntro(branches, a) => {
            occurs_const(a, id) || branches.iter().any(|(_, t2)| occurs_const(t2, id))
        }
    }
}

/// `H` (the bare type former).
fn hconst(spec: &CubHitSpec) -> Term {
    Term::cnst(name(&spec.name), vec![])
}
/// `H.point_i` (bare constant; apply separately for a fielded point).
fn point(spec: &CubHitSpec, i: usize) -> Term {
    Term::cnst(name(&spec.points[i].name), vec![])
}
/// `H.path_j` (bare constant; apply separately for a quantified path).
fn pathc(spec: &CubHitSpec, j: usize) -> Term {
    Term::cnst(name(&spec.paths[j].name), vec![])
}
/// `H.surf_k` (bare constant; `@`-apply twice for the 2-cell).
fn surfc(spec: &CubHitSpec, k: usize) -> Term {
    Term::cnst(name(&spec.surfaces[k].name), vec![])
}

/// Build a de-Bruijn `Var` referencing the binder assigned **level** `level`
/// (0-based, in the order the binders were introduced) from a position that is
/// currently `depth` binders deep. Standard de-Bruijn-level-to-index conversion:
/// `index = depth - level - 1`.
fn var_at(level: usize, depth: usize) -> Term {
    Term::Var(depth - level - 1)
}

/// Build the recursor's `i`-th ("point") case type `c_i` — the
/// **motive-dependent** generalization of [`crate::hit`]'s non-dependent
/// `case_i` (see the module doc's "Fielded point recursor" section for the exact
/// shape: every field keeps its original type, and each `Field::Rec` field gets
/// one extra trailing induction-hypothesis binder `C x`). `c_level_depth` is the
/// number of binders in scope immediately before `c_i`'s own type is written
/// (i.e. `C` is `var_at(0, c_level_depth)` from there), matching this file's
/// `var_at`/level convention throughout. A nullary point (`fields.is_empty()`)
/// degenerates to exactly the original schema's `c_i : C point_i`.
fn point_case_ty(spec: &CubHitSpec, i: usize, c_level_depth: usize) -> Term {
    let fields = &spec.points[i].fields;
    let mut binder_domains: Vec<Term> = Vec::new();
    // The level assigned to each field's own binder (needed to reference it both
    // as an IH's argument and in the final `point_i field..` application).
    let mut field_levels: Vec<usize> = Vec::new();
    let mut opened = 0usize; // binders opened so far within this telescope
    for f in fields {
        let field_level = c_level_depth + opened;
        field_levels.push(field_level);
        match f {
            Field::Rec => {
                // The field itself keeps its original (recursive) type `H`.
                binder_domains.push(hconst(spec));
                opened += 1;
                // Immediately followed by its induction hypothesis `C x`.
                let depth_here = c_level_depth + opened;
                let c_ref = var_at(0, depth_here);
                let field_ref = var_at(field_level, depth_here);
                binder_domains.push(Term::app(c_ref, field_ref));
                opened += 1;
            }
            Field::NonRec(t) => {
                binder_domains.push(t.clone());
                opened += 1;
            }
        }
    }
    let final_depth = c_level_depth + opened;
    let c_ref = var_at(0, final_depth);
    let field_terms: Vec<Term> = field_levels.iter().map(|&lvl| var_at(lvl, final_depth)).collect();
    let applied = Term::apps(point(spec, i), field_terms);
    let mut ty = Term::app(c_ref, applied);
    for dom in binder_domains.into_iter().rev() {
        ty = Term::pi(dom, ty);
    }
    ty
}

/// Install a general cubical HIT into `env` per `spec` — see the module doc for
/// the exact recursor signature and ι-rules. Rejects: fewer than one point
/// constructor, an out-of-range `lhs`/`rhs` path endpoint index, a path
/// field-argument count mismatch, a path constructor touching a point
/// constructor with a recursive field, a non-recursive field mentioning `H`
/// itself (strict positivity), and re-declaration of any of the generated names.
pub fn declare_cubical_hit(env: &mut Env, spec: &CubHitSpec) -> Result<(), String> {
    let n = spec.points.len();
    let m = spec.paths.len();
    let p = spec.surfaces.len();
    if n == 0 {
        return Err("a cubical HIT needs at least one point constructor".to_string());
    }
    let id: Name = name(&spec.name);

    // Strict positivity: no non-recursive field may mention `H` itself.
    for p in &spec.points {
        for f in &p.fields {
            if let Field::NonRec(t) = f {
                if occurs_const(t, &id) {
                    return Err(format!(
                        "cubical HIT '{}': point constructor '{}' has a non-recursive field mentioning \
                         '{}' itself — only a bare `Field::Rec` field may recur (strict positivity)",
                        spec.name, p.name, spec.name
                    ));
                }
            }
        }
    }

    for path in &spec.paths {
        for (label, (idx, fargs)) in [("lhs", &path.lhs), ("rhs", &path.rhs)] {
            if *idx >= n {
                return Err(format!(
                    "path constructor '{}' has an out-of-range {label} endpoint (index {idx}, but only {n} points)",
                    path.name
                ));
            }
            let arity = spec.points[*idx].fields.len();
            if fargs.len() != arity {
                return Err(format!(
                    "path '{}' {label} gives {} field argument(s) but point constructor '{}' has arity {arity}",
                    path.name,
                    fargs.len(),
                    spec.points[*idx].name
                ));
            }
            if spec.points[*idx].fields.iter().any(|f| matches!(f, Field::Rec)) {
                return Err(format!(
                    "path '{}' {label} targets point constructor '{}', which has a recursive field — path \
                     constructors may not (yet) target a recursive point constructor (see module docs)",
                    path.name, spec.points[*idx].name
                ));
            }
        }
    }

    // 2-path ("surface") constructors: `base` must be in range and NULLARY (the
    // "S²" restriction — see `CubSurfSpec`'s doc comment and the module doc's
    // "What's deferred" for the general-square case this doesn't attempt).
    for surf in &spec.surfaces {
        if surf.base >= n {
            return Err(format!(
                "surface constructor '{}' has an out-of-range base point (index {}, but only {n} points)",
                surf.name, surf.base
            ));
        }
        if !spec.points[surf.base].fields.is_empty() {
            return Err(format!(
                "surface constructor '{}' targets point constructor '{}', which is not nullary — 2-path \
                 constructors may only (yet) be based at a nullary point (see module docs, 'S²' restriction)",
                surf.name, spec.points[surf.base].name
            ));
        }
    }

    let mut all_names: Vec<&str> = vec![spec.name.as_str()];
    all_names.extend(spec.points.iter().map(|p| p.name.as_str()));
    all_names.extend(spec.paths.iter().map(|p| p.name.as_str()));
    all_names.extend(spec.surfaces.iter().map(|s| s.name.as_str()));
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

    let v = Level::param(0); // H.rec's target universe.

    // ------------------------------------------------------------------
    // H : Type 0
    // ------------------------------------------------------------------
    env.insert(
        id.clone(),
        Decl::CubHit(Rc::new(CubHit { id: id.clone(), role: CubHitRole::Type, num_levels: 0, ty: Term::typ(0) })),
    )?;

    // ------------------------------------------------------------------
    // H.point_i : field_0 -> .. -> field_{k_i-1} -> H, for i in 0..n
    // ------------------------------------------------------------------
    for (i, p) in spec.points.iter().enumerate() {
        let mut ty = hconst(spec);
        for f in p.fields.iter().rev() {
            let dom = match f {
                Field::Rec => hconst(spec),
                Field::NonRec(t) => t.clone(),
            };
            ty = Term::pi(dom, ty);
        }
        let is_rec_fields: Vec<bool> = p.fields.iter().map(|f| matches!(f, Field::Rec)).collect();
        env.insert(
            name(&p.name),
            Decl::CubHit(Rc::new(CubHit {
                id: id.clone(),
                role: CubHitRole::Point { idx: i as u32, fields: Rc::new(is_rec_fields) },
                num_levels: 0,
                ty,
            })),
        )?;
    }

    // ------------------------------------------------------------------
    // H.path_j : Π quantifiers.., Path H (point_lhs lhs_args..) (point_rhs rhs_args..)
    // ------------------------------------------------------------------
    for (j, path) in spec.paths.iter().enumerate() {
        let (lhs_i, lhs_args) = &path.lhs;
        let (rhs_i, rhs_args) = &path.rhs;
        let lhs_app = Term::apps(point(spec, *lhs_i), lhs_args.iter().cloned());
        let rhs_app = Term::apps(point(spec, *rhs_i), rhs_args.iter().cloned());
        let body = Term::path(hconst(spec), lhs_app, rhs_app);
        let mut ty = body;
        for q in path.quantifiers.iter().rev() {
            ty = Term::pi(q.clone(), ty);
        }
        env.insert(
            name(&path.name),
            Decl::CubHit(Rc::new(CubHit {
                id: id.clone(),
                role: CubHitRole::Path {
                    idx: j as u32,
                    lhs: *lhs_i as u32,
                    rhs: *rhs_i as u32,
                    num_quant: path.quantifiers.len() as u32,
                },
                num_levels: 0,
                ty,
            })),
        )?;
    }

    // ------------------------------------------------------------------
    // H.surf_k : Path (Path H p p) (refl p) (refl p), where p = H.point_{base}
    // (the "S²" 2-path shape — see `CubSurfSpec`'s doc comment).
    // ------------------------------------------------------------------
    for (k, surf) in spec.surfaces.iter().enumerate() {
        let base_pt = point(spec, surf.base); // nullary, so the bare constant IS the point value.
        let inner = Term::path(hconst(spec), base_pt.clone(), base_pt.clone());
        let refl_base = crate::cubical::refl(&base_pt);
        let ty = Term::path(inner, refl_base.clone(), refl_base);
        env.insert(
            name(&surf.name),
            Decl::CubHit(Rc::new(CubHit {
                id: id.clone(),
                role: CubHitRole::Surf { idx: k as u32, base: surf.base as u32 },
                num_levels: 0,
                ty,
            })),
        )?;
    }

    // ------------------------------------------------------------------
    // H.rec.{v} : Π (C : H -> Sort v)
    //               (c_0 : ..) .. (c_{n-1} : ..)
    //               (s_0 : ..) .. (s_{m-1} : ..)
    //               (t_0 : ..) .. (t_{p-1} : ..)
    //               (x : H), C x
    //
    // Binder levels (0-based, introduction order): C=0, c_i=1+i, s_j=1+n+j,
    // t_k=1+n+m+k, x=1+n+m+p — see `var_at`'s doc comment for the depth/level
    // convention.
    // ------------------------------------------------------------------
    let x_level = 1 + n + m + p;

    // Innermost: `C x`, written at depth = x_level + 1.
    let codomain = {
        let depth = x_level + 1;
        Term::app(var_at(0, depth), var_at(x_level, depth))
    };
    // `x : H`, written at depth = x_level.
    let mut acc = Term::pi(hconst(spec), codomain);

    // t_{p-1} .. t_0, each written at depth = 1 + n + m + k (before its own
    // double-interval telescope is opened). Mirrors `H.surf_k`'s own declared
    // type exactly, one level up: `H` -> `C` (applied), `H.point_base` -> the
    // point recursor case `c_base` (a plain var reference, since `base` is
    // nullary — no field telescope to thread through), and the boundary
    // `refl`/`Path` structure preserved verbatim, so that `t_k`'s type is
    // always well-formed by the *same* `PathP`/`Path` typing rules `H.surf_k`
    // itself was checked against above (see the module doc's soundness
    // argument, "Boundary coherence").
    for k in (0..p).rev() {
        let surf = &spec.surfaces[k];
        let depth = 1 + n + m + k;
        // `c_base`, the base point's recursor case, at the two depths it's
        // needed at (before/after opening the outer interval binder `i`).
        let c_base_outer = var_at(1 + surf.base, depth);
        let c_base_inner = var_at(1 + surf.base, depth + 1);
        let inner_family = {
            // Depth right after opening BOTH interval binders `i` (level =
            // `depth`) and `j` (level = `depth + 1`).
            let fam_depth = depth + 2;
            let c_ref = var_at(0, fam_depth);
            let i_ref = var_at(depth, fam_depth);
            let j_ref = var_at(depth + 1, fam_depth);
            let surf_call = Term::papp(Term::papp(surfc(spec, k), i_ref), j_ref);
            Term::app(c_ref, surf_call)
        };
        let inner_pathp = Term::pathp(inner_family, c_base_inner.clone(), c_base_inner);
        let outer_refl = crate::cubical::refl(&c_base_outer);
        let t_ty = Term::pathp(inner_pathp, outer_refl.clone(), outer_refl);
        acc = Term::pi(t_ty, acc);
    }

    // s_{m-1} .. s_0, each written at depth = 1 + n + j (before its own
    // quantifier/PathP telescope is opened).
    for j in (0..m).rev() {
        let path = &spec.paths[j];
        let depth = 1 + n + j;
        let q = path.quantifiers.len();
        let (lhs_i, lhs_args) = &path.lhs;
        let (rhs_i, rhs_args) = &path.rhs;
        // Depth immediately after all `q` quantifier binders are opened.
        let body_depth = depth + q;
        let family = {
            // One more binder for the PathP's own interval variable `i`.
            let fam_depth = body_depth + 1;
            let c_ref = var_at(0, fam_depth);
            // `path_j` applied to the SAME quantifier values, in declaration
            // order (q_0 first), shifted past the interval binder.
            let qvars: Vec<Term> = (0..q).map(|k| Term::Var(q - k)).collect();
            let path_call = Term::papp(Term::apps(pathc(spec, j), qvars), Term::Var(0));
            Term::app(c_ref, path_call)
        };
        let c_lhs_head = var_at(1 + *lhs_i, body_depth);
        let c_rhs_head = var_at(1 + *rhs_i, body_depth);
        let c_lhs = Term::apps(c_lhs_head, lhs_args.iter().cloned());
        let c_rhs = Term::apps(c_rhs_head, rhs_args.iter().cloned());
        let mut s_ty = Term::pathp(family, c_lhs, c_rhs);
        for qt in path.quantifiers.iter().rev() {
            s_ty = Term::pi(qt.clone(), s_ty);
        }
        acc = Term::pi(s_ty, acc);
    }

    // c_{n-1} .. c_0, each written at depth = 1 + i (before its own field/IH
    // telescope is opened).
    for i in (0..n).rev() {
        let depth = 1 + i;
        let c_ty = point_case_ty(spec, i, depth);
        acc = Term::pi(c_ty, acc);
    }

    // C : H -> Sort v, written at depth = 0.
    let rec_ty = Term::pi(Term::arrow(hconst(spec), Term::Sort(v)), acc);

    env.insert(
        name(&rec_name_owned),
        Decl::CubHit(Rc::new(CubHit {
            id,
            role: CubHitRole::Rec { num_points: n as u32, num_paths: m as u32, num_surfaces: p as u32 },
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
            points: vec![CubPointSpec::nullary("MyI.zero"), CubPointSpec::nullary("MyI.one")],
            paths: vec![CubPathSpec::simple("MyI.seg", 0, 1)],
            surfaces: vec![],
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
        let spec = CubHitSpec { name: "Empty2".to_string(), points: vec![], paths: vec![],
            surfaces: vec![],
        };
        let err = declare_cubical_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("at least one point"), "got: {err}");
    }

    #[test]
    fn rejects_out_of_range_path_endpoint() {
        let mut env = base_env();
        let spec = CubHitSpec {
            name: "Bad".to_string(),
            points: vec![CubPointSpec::nullary("Bad.p0")],
            paths: vec![CubPathSpec::simple("Bad.bogus", 0, 5)],
            surfaces: vec![],
        };
        let err = declare_cubical_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("out-of-range"), "got: {err}");
    }

    #[test]
    fn rejects_double_install() {
        let mut env = base_env();
        let spec = CubHitSpec {
            name: "Dup".to_string(),
            points: vec![CubPointSpec::nullary("Dup.p0")],
            paths: vec![],
            surfaces: vec![],
        };
        declare_cubical_hit(&mut env, &spec).unwrap();
        let err = declare_cubical_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("already declared"), "got: {err}");
    }

    /// SOUNDNESS (adversarial): a non-recursive field mentioning `H` itself is
    /// rejected — only a bare `Field::Rec` slot may recur (strict positivity).
    #[test]
    fn rejects_nonrec_field_mentioning_self() {
        let mut env = base_env();
        let spec = CubHitSpec {
            name: "Bad".to_string(),
            points: vec![CubPointSpec {
                name: "Bad.p0".to_string(),
                fields: vec![Field::NonRec(Term::arrow(Term::cnst(name("Bad"), vec![]), cn("Nat")))],
            }],
            paths: vec![],
            surfaces: vec![],
        };
        let err = declare_cubical_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("strict positivity") || err.contains("mentioning"), "got: {err}");
    }

    /// SOUNDNESS (adversarial): a path constructor may not target a point
    /// constructor with a recursive field.
    #[test]
    fn rejects_path_touching_recursive_point() {
        let mut env = base_env();
        let spec = CubHitSpec {
            name: "Bad".to_string(),
            points: vec![
                CubPointSpec::nullary("Bad.unit"),
                CubPointSpec { name: "Bad.cons".to_string(), fields: vec![Field::NonRec(cn("Nat")), Field::Rec] },
            ],
            paths: vec![CubPathSpec {
                name: "Bad.oops".to_string(),
                quantifiers: vec![],
                lhs: (0, vec![]),
                rhs: (1, vec![lit(0), Term::cnst(name("Bad.unit"), vec![])]),
            }],
            surfaces: vec![],
        };
        let err = declare_cubical_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("recursive field"), "got: {err}");
    }

    /// SOUNDNESS (adversarial): a path field-argument count mismatch is rejected.
    #[test]
    fn rejects_path_field_arity_mismatch() {
        let mut env = base_env();
        let spec = CubHitSpec {
            name: "Bad".to_string(),
            points: vec![CubPointSpec { name: "Bad.mk".to_string(), fields: vec![Field::NonRec(cn("Nat"))] }],
            paths: vec![CubPathSpec {
                name: "Bad.e".to_string(),
                quantifiers: vec![],
                lhs: (0, vec![lit(0)]),
                rhs: (0, vec![]), // wrong arity
            }],
            surfaces: vec![],
        };
        let err = declare_cubical_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("arity"), "got: {err}");
    }

    // ---------------------------------------------------------------------
    // Re-derivation #1: I2 via the general schema (all-nullary, unquantified).
    // ---------------------------------------------------------------------

    fn i2_spec() -> CubHitSpec {
        CubHitSpec {
            name: "I2g".to_string(),
            points: vec![CubPointSpec::nullary("I2g.zero"), CubPointSpec::nullary("I2g.one")],
            paths: vec![CubPathSpec::simple("I2g.seg", 0, 1)],
            surfaces: vec![],
        }
    }

    #[test]
    fn rederive_i2_typechecks_like_the_hand_coded_original() {
        let mut env = base_env();
        install_interval_hit(&mut env).unwrap();
        let spec = i2_spec();
        declare_cubical_hit(&mut env, &spec).unwrap();
        let chk = Checker::new(&env);
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

        let rz = rec(zero.clone());
        chk.check(&mut LocalCtx::new(), &rz, &cn("Nat")).unwrap();
        assert!(red.is_def_eq(&rz, &lit(7)));
        assert_eq!(nbe.normalize(&rz), lit(7));

        let ro = rec(one.clone());
        chk.check(&mut LocalCtx::new(), &ro, &cn("Nat")).unwrap();
        assert!(red.is_def_eq(&ro, &lit(7)));
        assert_eq!(nbe.normalize(&ro), lit(7));

        let scrut = Term::papp(seg, Term::Var(0));
        let whole = Term::plam(rec(scrut));
        let ty = chk.infer_closed(&whole).unwrap();
        assert!(red.is_def_eq(&ty, &Term::path(cn("Nat"), lit(7), lit(7))));
        let expected = Term::plam(lit(7).lift(1, 0));
        assert!(red.is_def_eq(&whole, &expected));
        assert_eq!(nbe.normalize(&whole), nbe.normalize(&expected));

        let via_i0 = rec(Term::papp(cn("I2g.seg"), Term::IZero));
        assert!(red.is_def_eq(&via_i0, &rz));
        let via_i1 = rec(Term::papp(cn("I2g.seg"), Term::IOne));
        assert!(red.is_def_eq(&via_i1, &ro));

        assert!(!red.is_def_eq(&zero, &one));
    }

    // ---------------------------------------------------------------------
    // Re-derivation #2: S1c (self-loop) via the general schema.
    // ---------------------------------------------------------------------

    fn s1c_spec() -> CubHitSpec {
        CubHitSpec {
            name: "S1g".to_string(),
            points: vec![CubPointSpec::nullary("S1g.base")],
            paths: vec![CubPathSpec::simple("S1g.loop", 0, 0)],
            surfaces: vec![],
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

        let scrut = Term::papp(loop_.clone(), Term::Var(0));
        let whole = Term::plam(rec(scrut));
        let ty = chk.infer_closed(&whole).unwrap();
        assert!(red.is_def_eq(&ty, &Term::path(cn("Nat"), lit(4), lit(4))));
        let expected = Term::plam(lit(4).lift(1, 0));
        assert!(red.is_def_eq(&whole, &expected));
        assert_eq!(nbe.normalize(&whole), nbe.normalize(&expected));

        let via_i0 = rec(Term::papp(loop_.clone(), Term::IZero));
        let via_i1 = rec(Term::papp(loop_.clone(), Term::IOne));
        assert!(red.is_def_eq(&via_i0, &rb));
        assert!(red.is_def_eq(&via_i1, &rb));
        assert!(red.is_def_eq(&via_i0, &via_i1));

        let refl_base = crate::cubical::refl(&base);
        assert!(!red.is_def_eq(&loop_, &refl_base));
    }

    // ---------------------------------------------------------------------
    // A HIT the hand-coded pair didn't cover: a "figure eight" — one point,
    // TWO independent self-loops.
    // ---------------------------------------------------------------------

    fn figure_eight_spec() -> CubHitSpec {
        CubHitSpec {
            name: "Fig8".to_string(),
            points: vec![CubPointSpec::nullary("Fig8.base")],
            paths: vec![CubPathSpec::simple("Fig8.loop1", 0, 0), CubPathSpec::simple("Fig8.loop2", 0, 0)],
            surfaces: vec![],
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

    #[test]
    fn figure_eight_loops_compute_independently() {
        let mut env = base_env();
        declare_cubical_hit(&mut env, &figure_eight_spec()).unwrap();
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

        let rb = rec(base);
        assert!(red.is_def_eq(&rb, &cn("a")));

        let scrut1 = Term::papp(loop1, Term::Var(0));
        let whole1 = Term::plam(rec(scrut1));
        chk.infer_closed(&whole1).unwrap();
        let expected1 = Term::plam(Term::papp(cn("l1"), Term::Var(0)));
        assert!(red.is_def_eq(&whole1, &expected1));
        assert_eq!(nbe.normalize(&whole1), nbe.normalize(&expected1));

        let scrut2 = Term::papp(loop2, Term::Var(0));
        let whole2 = Term::plam(rec(scrut2));
        chk.infer_closed(&whole2).unwrap();
        let expected2 = Term::plam(Term::papp(cn("l2"), Term::Var(0)));
        assert!(red.is_def_eq(&whole2, &expected2));
        assert_eq!(nbe.normalize(&whole2), nbe.normalize(&expected2));

        assert!(!red.is_def_eq(&whole1, &whole2));
    }

    // ---------------------------------------------------------------------
    // Adversarial: per-id no cross-fire between two independently declared
    // cubical HITs (even ones with structurally identical shapes).
    // ---------------------------------------------------------------------

    #[test]
    fn no_cross_fire_between_two_distinct_declared_hits() {
        let mut env = base_env();
        let spec_a = CubHitSpec {
            name: "Ia".to_string(),
            points: vec![CubPointSpec::nullary("Ia.zero"), CubPointSpec::nullary("Ia.one")],
            paths: vec![CubPathSpec::simple("Ia.seg", 0, 1)],
            surfaces: vec![],
        };
        let spec_b = CubHitSpec {
            name: "Ib".to_string(),
            points: vec![CubPointSpec::nullary("Ib.zero"), CubPointSpec::nullary("Ib.one")],
            paths: vec![CubPathSpec::simple("Ib.seg", 0, 1)],
            surfaces: vec![],
        };
        declare_cubical_hit(&mut env, &spec_a).unwrap();
        declare_cubical_hit(&mut env, &spec_b).unwrap();
        let chk = Checker::new(&env);
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

    // ---------------------------------------------------------------------
    // NEW: fielded, recursive point — `FreeMonoidC`, no path constructors.
    // Exercises the recursive-field ι-substitution standalone.
    // ---------------------------------------------------------------------

    fn free_monoid_cubical_spec() -> CubHitSpec {
        CubHitSpec {
            name: "FreeMonoidC".to_string(),
            points: vec![
                CubPointSpec::nullary("FreeMonoidC.unit"),
                CubPointSpec {
                    name: "FreeMonoidC.cons".to_string(),
                    fields: vec![Field::NonRec(cn("Nat")), Field::Rec],
                },
            ],
            paths: vec![],
            surfaces: vec![],
        }
    }

    #[test]
    fn free_monoid_cubical_wellformed() {
        let mut env = base_env();
        declare_cubical_hit(&mut env, &free_monoid_cubical_spec()).unwrap();
        let chk = Checker::new(&env);
        for n in ["FreeMonoidC", "FreeMonoidC.unit", "FreeMonoidC.cons", "FreeMonoidC.rec"] {
            chk.infer_closed(env.get(n).unwrap().ty()).unwrap_or_else(|e| panic!("{n} ill-formed: {e}"));
        }
    }

    /// COMPUTATION RULE for a fielded, **recursive** point: `sum (cons 3 (cons 4
    /// unit)) = 7`, exercising the recursive `H.rec` ι-substitution (differential
    /// reducer vs. NbE).
    #[test]
    fn free_monoid_cubical_rec_computes_recursively() {
        let mut env = base_env();
        declare_cubical_hit(&mut env, &free_monoid_cubical_spec()).unwrap();
        let u = Level::of_nat(1);
        let add = |a: Term, b: Term| {
            Term::apps(
                Term::cnst(name("Nat.rec"), vec![u.clone()]),
                [
                    Term::lam(cn("Nat"), cn("Nat")),
                    b,
                    Term::lam(cn("Nat"), Term::lam(cn("Nat"), Term::app(cn("Nat.succ"), Term::Var(0)))),
                    a,
                ],
            )
        };
        // Non-dependent motive `C := λ_. Nat`.
        let motive = Term::lam(cn("FreeMonoidC"), cn("Nat").lift(1, 0));
        // cons-case: `Π (a:Nat) (x:FreeMonoidC), Nat -> Nat` (the `Nat` domain for `x`'s
        // IH, since `C x = Nat` for this constant motive).
        let cons_case = Term::lam(
            cn("Nat"),
            Term::lam(cn("FreeMonoidC"), Term::lam(cn("Nat"), add(Term::Var(2), Term::Var(0)))),
        );
        let sum = |scrut: Term| {
            Term::apps(
                Term::cnst(name("FreeMonoidC.rec"), vec![u.clone()]),
                [motive.clone(), lit(0), cons_case.clone(), scrut],
            )
        };
        let cons =
            |n: Term, tail: Term| Term::apps(Term::cnst(name("FreeMonoidC.cons"), vec![]), [n, tail]);
        let unit = || cn("FreeMonoidC.unit");
        let list = cons(lit(3), cons(lit(4), unit()));
        let expr = sum(list);
        let chk = Checker::new(&env);
        chk.check(&mut LocalCtx::new(), &expr, &cn("Nat")).unwrap();
        let red = Reducer::new(&env);
        assert!(red.is_def_eq(&expr, &lit(7)), "reducer: sum [3,4] = 7");
        let nbe = Nbe::new(&env);
        assert_eq!(nbe.normalize(&expr), nbe.normalize(&lit(7)), "nbe: sum [3,4] = 7");

        let base = sum(unit());
        assert!(red.is_def_eq(&base, &lit(0)));
        assert_eq!(nbe.normalize(&base), nbe.normalize(&lit(0)));
    }

    /// `H.rec` stays stuck on a partially-applied (under-arity) fielded point
    /// constructor — the fielded ι-rule must not misfire.
    #[test]
    fn rec_stuck_on_underapplied_fielded_point() {
        let mut env = base_env();
        declare_cubical_hit(&mut env, &free_monoid_cubical_spec()).unwrap();
        let u = Level::of_nat(1);
        let motive = Term::lam(cn("FreeMonoidC"), cn("Nat").lift(1, 0));
        let cons_case = Term::lam(
            cn("Nat"),
            Term::lam(cn("FreeMonoidC"), Term::lam(cn("Nat"), Term::Var(1))),
        );
        let partial = Term::app(Term::cnst(name("FreeMonoidC.cons"), vec![]), lit(3)); // missing the tail
        let rec = Term::apps(
            Term::cnst(name("FreeMonoidC.rec"), vec![u]),
            [motive, lit(0), cons_case, partial],
        );
        let red = Reducer::new(&env);
        let result = red.whnf(&rec);
        assert!(matches!(result.unfold_apps().0, Term::Const(n, _) if n == name("FreeMonoidC.rec")));
    }

    /// ADVERSARIAL / canonicity: two `FreeMonoidC` values built from distinct
    /// field data stay definitionally distinct — a fielded point constructor's
    /// field carries real information, never erased to a bare tag.
    #[test]
    fn fielded_points_with_different_fields_stay_distinct() {
        let mut env = base_env();
        declare_cubical_hit(&mut env, &free_monoid_cubical_spec()).unwrap();
        let cons =
            |n: Term| Term::apps(Term::cnst(name("FreeMonoidC.cons"), vec![]), [n, cn("FreeMonoidC.unit")]);
        let red = Reducer::new(&env);
        assert!(!red.is_def_eq(&cons(lit(3)), &cons(lit(4))));
    }

    // ---------------------------------------------------------------------
    // NEW worked example: `NatSQ`, a set-quotient-flavored cubical HIT — a
    // FIELDED point (`mk : Nat -> NatSQ`) plus a QUANTIFIED path (`glue : Π a b,
    // R a b -> Path NatSQ (mk a) (mk b)`) — neither expressible by the original
    // nullary-only schema.
    // ---------------------------------------------------------------------

    fn natsq_env_and_spec() -> (Env, CubHitSpec) {
        let mut env = base_env();
        // A fixed, previously-declared relation `R : Nat -> Nat -> Type 0`.
        let r_ty = Term::arrow(cn("Nat"), Term::arrow(cn("Nat"), Term::typ(0)));
        env.insert(name("NatSQ.R"), Decl::Axiom { num_levels: 0, ty: r_ty }).unwrap();
        let spec = CubHitSpec {
            name: "NatSQ".to_string(),
            points: vec![CubPointSpec { name: "NatSQ.mk".to_string(), fields: vec![Field::NonRec(cn("Nat"))] }],
            paths: vec![CubPathSpec {
                name: "NatSQ.glue".to_string(),
                // Π (a:Nat) (b:Nat) (h : R a b), .. — innermost = h = Var(0).
                quantifiers: vec![
                    cn("Nat"),
                    cn("Nat"),
                    Term::apps(cn("NatSQ.R"), [Term::Var(1), Term::Var(0)]),
                ],
                lhs: (0, vec![Term::Var(2)]),
                rhs: (0, vec![Term::Var(1)]),
            }],
            surfaces: vec![],
        };
        (env, spec)
    }

    #[test]
    fn natsq_wellformed_and_glue_typechecks() {
        let (mut env, spec) = natsq_env_and_spec();
        declare_cubical_hit(&mut env, &spec).unwrap();
        let chk = Checker::new(&env);
        for n in ["NatSQ", "NatSQ.mk", "NatSQ.glue", "NatSQ.rec"] {
            chk.infer_closed(env.get(n).unwrap().ty()).unwrap_or_else(|e| panic!("{n} ill-formed: {e}"));
        }
        // `NatSQ.glue` itself well-typechecks against its own declared Π-PathP type
        // (redundant with `infer_closed` above but pins down the exact shape).
        let a = lit(3);
        let b = lit(3);
        env.insert(
            name("h_refl_R"),
            Decl::Axiom { num_levels: 0, ty: Term::apps(cn("NatSQ.R"), [a.clone(), b.clone()]) },
        )
        .unwrap();
        let chk = Checker::new(&env);
        let applied = Term::apps(cn("NatSQ.glue"), [a.clone(), b.clone(), cn("h_refl_R")]);
        let goal = Term::path(
            cn("NatSQ"),
            Term::app(cn("NatSQ.mk"), a),
            Term::app(cn("NatSQ.mk"), b),
        );
        chk.check(&mut LocalCtx::new(), &applied, &goal).unwrap();
    }

    /// COMPUTATION RULE: the quantified path ι-rule. `rec .. (glue a b h @ r)`
    /// reduces to `(resp a b h) @ r`, for a *neutral* (opaque, axiomatized) `resp`
    /// witness — differential reducer vs. NbE. (Endpoint/boundary coherence itself
    /// — `resp a b h`'s boundary matching `case a`/`case b` — is a *type-checking*
    /// fact, established once when `resp` is checked against `H.rec`'s `s_j`
    /// parameter type at the call site below via `chk.infer_closed`; it is not, in
    /// general, a definitional *reduction* fact for an opaque `resp` — only a
    /// concretely-known `PLam` witness reduces at `i0`/`i1`, exactly as Phase 1's
    /// `PApp` rule requires (see `crate::reduce::Reducer::whnf`'s `PApp` arm's doc
    /// comment). `natsq_glue_self_relation_boundary_computes` below demonstrates
    /// the concrete-witness case, where the boundary genuinely *does* reduce.)
    #[test]
    fn natsq_glue_path_iota_computes() {
        let (mut env, spec) = natsq_env_and_spec();
        declare_cubical_hit(&mut env, &spec).unwrap();
        let u = Level::of_nat(1);
        // Non-dependent motive `C := λ_. Nat`; case := λ a. a (identity on the field);
        // respectfulness `s := λ a b h. refl a`... but `refl a : Path Nat a a`, whereas
        // we need `Path Nat (case a) (case b) = Path Nat a b` for GENERIC a/b -- since
        // `a`/`b` aren't definitionally equal in general, use a genuinely axiomatized
        // path witness instead (mirrors `hit.rs`'s `nat_mod_r` test setup).
        env.insert(
            name("NatSQ.resp"),
            Decl::Axiom {
                num_levels: 0,
                ty: Term::pi(
                    cn("Nat"),
                    Term::pi(
                        cn("Nat"),
                        Term::pi(
                            Term::apps(cn("NatSQ.R"), [Term::Var(1), Term::Var(0)]),
                            Term::path(cn("Nat"), Term::Var(2), Term::Var(1)),
                        ),
                    ),
                ),
            },
        )
        .unwrap();
        let motive = Term::lam(cn("NatSQ"), cn("Nat").lift(1, 0));
        let case = Term::lam(cn("Nat"), Term::Var(0));
        let resp = cn("NatSQ.resp");
        let rec = |scrut: Term| {
            Term::apps(
                Term::cnst(name("NatSQ.rec"), vec![u.clone()]),
                [motive.clone(), case.clone(), resp.clone(), scrut],
            )
        };
        let chk = Checker::new(&env);
        let red = Reducer::new(&env);
        let nbe = Nbe::new(&env);

        // Point rule: `rec (mk a) = a`.
        let a = lit(3);
        let mk_a = Term::app(cn("NatSQ.mk"), a.clone());
        let ra = rec(mk_a.clone());
        chk.check(&mut LocalCtx::new(), &ra, &cn("Nat")).unwrap();
        assert!(red.is_def_eq(&ra, &a));
        assert_eq!(nbe.normalize(&ra), nbe.normalize(&a));

        // Path rule: `rec (glue a b h @ r) = (resp a b h) @ r`.
        let b = lit(5);
        let mk_b = Term::app(cn("NatSQ.mk"), b.clone());
        env.insert(
            name("h_ab"),
            Decl::Axiom { num_levels: 0, ty: Term::apps(cn("NatSQ.R"), [a.clone(), b.clone()]) },
        )
        .unwrap();
        // (env was extended after `chk`/`red`/`nbe` were built above; rebuild them.)
        let chk = Checker::new(&env);
        let red = Reducer::new(&env);
        let nbe = Nbe::new(&env);
        let rec = |scrut: Term| {
            Term::apps(
                Term::cnst(name("NatSQ.rec"), vec![u.clone()]),
                [motive.clone(), case.clone(), resp.clone(), scrut],
            )
        };
        let glue_applied = Term::apps(cn("NatSQ.glue"), [a.clone(), b.clone(), cn("h_ab")]);
        let scrut = Term::papp(glue_applied, Term::Var(0));
        let whole = Term::plam(rec(scrut));
        chk.infer_closed(&whole).unwrap();
        let expected = Term::plam(Term::papp(
            Term::apps(cn("NatSQ.resp"), [a.clone(), b.clone(), cn("h_ab")]),
            Term::Var(0),
        ));
        assert!(red.is_def_eq(&whole, &expected));
        assert_eq!(nbe.normalize(&whole), nbe.normalize(&expected));
        let _ = mk_b; // (kept only to document the intended `mk b` endpoint above)
    }

    /// COMPUTATION RULE, endpoint coherence with a CONCRETE (genuinely reducing)
    /// witness: a **self-relation** instance `glue a a h : Path NatSQ (mk a) (mk
    /// a)` whose `resp` is a real `refl`-built `PLam`, not an opaque axiom — so
    /// `rec .. (glue a a h @ i0)`/`@ i1` both genuinely reduce, and agree with the
    /// point rule `rec (mk a)`, exactly the boundary-coherence argument the module
    /// doc makes (definitional agreement derived from `PathP` well-formedness plus
    /// a concrete `PLam` witness's real computation rule, not a new equation).
    #[test]
    fn natsq_glue_self_relation_boundary_computes() {
        // A dedicated fielded-point + quantified-SELF-loop HIT (`glue` relates
        // `mk a` to itself, for `a`s satisfying a unary predicate `RR`) — unlike
        // `NatSQ.glue` (which relates *different* fields `a`/`b` generically, so no
        // *generic* concrete witness can exist), a self-relation lets a single
        // `refl`-built `PLam` witness `resp := λ a h. refl a` type-check for EVERY
        // `a`, giving a genuinely reducing boundary to exercise.
        let mut env = base_env();
        let rr_ty = Term::arrow(cn("Nat"), Term::typ(0));
        env.insert(name("SelfSQ.RR"), Decl::Axiom { num_levels: 0, ty: rr_ty }).unwrap();
        let spec = CubHitSpec {
            name: "SelfSQ".to_string(),
            points: vec![CubPointSpec { name: "SelfSQ.mk".to_string(), fields: vec![Field::NonRec(cn("Nat"))] }],
            paths: vec![CubPathSpec {
                name: "SelfSQ.glue".to_string(),
                // Π (a:Nat) (h : RR a), .. — innermost = h = Var(0).
                quantifiers: vec![cn("Nat"), Term::app(cn("SelfSQ.RR"), Term::Var(0))],
                lhs: (0, vec![Term::Var(1)]),
                rhs: (0, vec![Term::Var(1)]),
            }],
            surfaces: vec![],
        };
        declare_cubical_hit(&mut env, &spec).unwrap();

        let u = Level::of_nat(1);
        let a = lit(3);
        env.insert(name("h_a"), Decl::Axiom { num_levels: 0, ty: Term::app(cn("SelfSQ.RR"), a.clone()) }).unwrap();
        let motive = Term::lam(cn("SelfSQ"), cn("Nat").lift(1, 0));
        let case = Term::lam(cn("Nat"), Term::Var(0));
        // `resp := λ a h. refl a` — a concrete `PLam`, genuinely reducing at
        // `i0`/`i1`, and well-typed for EVERY `a` (self-relation).
        let resp = Term::lam(
            cn("Nat"),
            Term::lam(Term::app(cn("SelfSQ.RR"), Term::Var(0)), crate::cubical::refl(&Term::Var(1))),
        );
        let rec = |scrut: Term| {
            Term::apps(
                Term::cnst(name("SelfSQ.rec"), vec![u.clone()]),
                [motive.clone(), case.clone(), resp.clone(), scrut],
            )
        };
        let chk = Checker::new(&env);
        let red = Reducer::new(&env);
        let nbe = Nbe::new(&env);

        let mk_a = Term::app(cn("SelfSQ.mk"), a.clone());
        let ra = rec(mk_a);
        chk.check(&mut LocalCtx::new(), &ra, &cn("Nat")).unwrap();
        assert!(red.is_def_eq(&ra, &a));

        let glue_applied = Term::apps(cn("SelfSQ.glue"), [a.clone(), cn("h_a")]);
        let glue_at0 = rec(Term::papp(glue_applied.clone(), Term::IZero));
        chk.infer_closed(&glue_at0).unwrap();
        assert!(red.is_def_eq(&glue_at0, &ra), "reducer: glue boundary at i0 agrees with the point rule");
        assert_eq!(nbe.normalize(&glue_at0), nbe.normalize(&ra), "nbe: glue boundary at i0");

        let glue_at1 = rec(Term::papp(glue_applied, Term::IOne));
        assert!(red.is_def_eq(&glue_at1, &ra), "reducer: glue boundary at i1 agrees with the point rule");
        assert_eq!(nbe.normalize(&glue_at1), nbe.normalize(&ra), "nbe: glue boundary at i1");
    }

    /// ADVERSARIAL / canonicity: two distinct `NatSQ.mk` applications stay
    /// definitionally distinct (only propositionally identified where `glue`
    /// actually applies) — `mk 3` and `mk 4` are not identified absent a `glue`
    /// witness relating them.
    #[test]
    fn natsq_points_with_different_fields_stay_distinct() {
        let (mut env, spec) = natsq_env_and_spec();
        declare_cubical_hit(&mut env, &spec).unwrap();
        let red = Reducer::new(&env);
        let mk = |n: Term| Term::app(cn("NatSQ.mk"), n);
        assert!(!red.is_def_eq(&mk(lit(3)), &mk(lit(4))));
    }

    // ---------------------------------------------------------------------
    // NEW: a genuine HIGHER cubical HIT — `S²`, one point (`base`) and one
    // 2-path ("surface") constructor `surf : Path (Path S² base base) (refl
    // base) (refl base)`, the simplest example the 1-path-only schema above
    // cannot express (see the module doc, "2-dimensional (higher) path
    // constructors").
    // ---------------------------------------------------------------------

    fn s2_spec() -> CubHitSpec {
        CubHitSpec {
            name: "S2g".to_string(),
            points: vec![CubPointSpec::nullary("S2g.base")],
            paths: vec![],
            surfaces: vec![CubSurfSpec { name: "S2g.surf".to_string(), base: 0 }],
        }
    }

    #[test]
    fn s2_wellformed_and_surf_typechecks() {
        let mut env = base_env();
        declare_cubical_hit(&mut env, &s2_spec()).unwrap();
        let chk = Checker::new(&env);
        for n in ["S2g", "S2g.base", "S2g.surf", "S2g.rec"] {
            chk.infer_closed(env.get(n).unwrap().ty()).unwrap_or_else(|e| panic!("{n} ill-formed: {e}"));
        }
        // `S2g.surf` itself checks against the literal `Path (Path S2g base base)
        // (refl base) (refl base)` goal — pins the exact declared shape down.
        let base = cn("S2g.base");
        let inner = Term::path(cn("S2g"), base.clone(), base.clone());
        let goal = Term::path(inner, crate::cubical::refl(&base), crate::cubical::refl(&base));
        chk.check(&mut LocalCtx::new(), &cn("S2g.surf"), &goal).unwrap();
    }

    /// SOUNDNESS (adversarial): a 2-path ("surface") constructor may only be
    /// based at a NULLARY point constructor (the "S²" restriction) — a fielded
    /// base point is rejected.
    #[test]
    fn rejects_surf_based_at_fielded_point() {
        let mut env = base_env();
        let spec = CubHitSpec {
            name: "Bad".to_string(),
            points: vec![CubPointSpec { name: "Bad.mk".to_string(), fields: vec![Field::NonRec(cn("Nat"))] }],
            paths: vec![],
            surfaces: vec![CubSurfSpec { name: "Bad.surf".to_string(), base: 0 }],
        };
        let err = declare_cubical_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("not nullary") || err.contains("nullary"), "got: {err}");
    }

    /// SOUNDNESS (adversarial): an out-of-range `base` index is rejected.
    #[test]
    fn rejects_surf_out_of_range_base() {
        let mut env = base_env();
        let spec = CubHitSpec {
            name: "Bad2".to_string(),
            points: vec![CubPointSpec::nullary("Bad2.p0")],
            paths: vec![],
            surfaces: vec![CubSurfSpec { name: "Bad2.surf".to_string(), base: 5 }],
        };
        let err = declare_cubical_hit(&mut env, &spec).unwrap_err();
        assert!(err.contains("out-of-range"), "got: {err}");
    }

    /// COMPUTATION RULE: the 2-path ι-rule. `rec .. (surf @ i @ j)` reduces to
    /// `(t @ i) @ j` for a CONCRETE (genuinely reducing) `PLam`-of-`PLam`
    /// witness `t = refl (refl 7)` — differential reducer vs. NbE, and (since
    /// `t` is concrete) exercises the boundary at every corner too (`i0`/`i1`
    /// composed with `j0`/`j1` all collapse to the point rule's value, exactly
    /// the argument the module doc's "Boundary coherence" section makes, now
    /// one dimension up).
    #[test]
    fn s2_surf_iota_computes_and_boundary_agrees() {
        let mut env = base_env();
        declare_cubical_hit(&mut env, &s2_spec()).unwrap();
        let u = Level::of_nat(1);
        let seven = lit(7);
        let motive = Term::lam(cn("S2g"), cn("Nat").lift(1, 0));
        // `t := refl (refl 7) : Path (Path Nat 7 7) (refl 7) (refl 7)` — a
        // concrete, genuinely-reducing witness (mirrors
        // `natsq_glue_self_relation_boundary_computes`'s use of a concrete
        // `PLam` witness rather than an opaque axiom, one dimension up).
        let t = crate::cubical::refl(&crate::cubical::refl(&seven));
        let rec = |scrut: Term| {
            Term::apps(Term::cnst(name("S2g.rec"), vec![u.clone()]), [motive.clone(), seven.clone(), t.clone(), scrut])
        };
        let chk = Checker::new(&env);
        let red = Reducer::new(&env);
        let nbe = Nbe::new(&env);

        // Point rule: `rec base = 7`.
        let rb = rec(cn("S2g.base"));
        chk.check(&mut LocalCtx::new(), &rb, &cn("Nat")).unwrap();
        assert!(red.is_def_eq(&rb, &seven));
        assert_eq!(nbe.normalize(&rb), nbe.normalize(&seven));

        // 2-path rule: `rec (surf @ i @ j) = (t @ i) @ j = 7`, for symbolic
        // `i`/`j` (two nested `plam`s; `i = Var(1)`, `j = Var(0)` inside).
        let scrut = Term::papp(Term::papp(cn("S2g.surf"), Term::Var(1)), Term::Var(0));
        let whole = Term::plam(Term::plam(rec(scrut)));
        let ty = chk.infer_closed(&whole).unwrap();
        let inner_ty = Term::path(cn("Nat"), seven.clone(), seven.clone());
        let expected_ty =
            Term::path(inner_ty, crate::cubical::refl(&seven), crate::cubical::refl(&seven));
        assert!(red.is_def_eq(&ty, &expected_ty));
        let expected = Term::plam(Term::plam(seven.lift(2, 0)));
        assert!(red.is_def_eq(&whole, &expected));
        assert_eq!(nbe.normalize(&whole), nbe.normalize(&expected));

        // Boundary coherence at every corner: `surf @ i0/i1 @ j0/j1` all agree
        // with the point rule (`rec base = 7`), for the concrete witness `t`.
        for i_end in [Term::IZero, Term::IOne] {
            for j_end in [Term::IZero, Term::IOne] {
                let corner = rec(Term::papp(Term::papp(cn("S2g.surf"), i_end.clone()), j_end.clone()));
                chk.check(&mut LocalCtx::new(), &corner, &cn("Nat")).unwrap();
                assert!(red.is_def_eq(&corner, &rb), "reducer: corner {i_end:?}/{j_end:?} agrees with rec base");
                assert_eq!(nbe.normalize(&corner), nbe.normalize(&rb), "nbe: corner {i_end:?}/{j_end:?}");
            }
        }
    }

    /// `H.rec` stays stuck on a partially-applied ("under-dimensioned") surface
    /// — a SINGLE `@`-application `surf @ i` (not the required double
    /// `surf @ i @ j`) must not misfire the 2-path ι-rule (it isn't even
    /// `H`-typed — `surf @ i : Path S2g base base` — so this can only arise as
    /// an ill-typed scrutinee/stuck neutral, exercised here directly at the
    /// reducer level to pin down the ι-rule's own arity discipline).
    #[test]
    fn rec_stuck_on_underapplied_surf() {
        let mut env = base_env();
        declare_cubical_hit(&mut env, &s2_spec()).unwrap();
        let u = Level::of_nat(1);
        let motive = Term::lam(cn("S2g"), cn("Nat").lift(1, 0));
        let t = crate::cubical::refl(&crate::cubical::refl(&lit(7)));
        let partial = Term::papp(cn("S2g.surf"), Term::Var(0)); // only ONE `@`
        let rec = Term::plam(Term::apps(
            Term::cnst(name("S2g.rec"), vec![u]),
            [motive, lit(7), t, partial],
        ));
        let red = Reducer::new(&env);
        let result = red.whnf(&rec);
        // Stays a stuck `PLam` around the (still-stuck) `H.rec` application —
        // never collapses to a point-rule/surface-rule result.
        match &result {
            Term::PLam(body) => {
                let (h, _) = body.unfold_apps();
                assert!(matches!(h, Term::Const(n, _) if n == name("S2g.rec")));
            }
            other => panic!("expected a stuck PLam, got {other:?}"),
        }
    }

    /// ANTI-`False`: cannot derive `Path Nat 0 1` via the 2-path schema either.
    #[test]
    fn cannot_prove_false_via_surf_schema() {
        let mut env = base_env();
        declare_cubical_hit(&mut env, &s2_spec()).unwrap();
        let chk = Checker::new(&env);
        let bogus_goal = Term::path(Term::path(cn("Nat"), lit(3), lit(3)), crate::cubical::refl(&lit(3)), crate::cubical::refl(&lit(3)));
        // `S2g.surf`'s own declared type is `Path (Path S2g base base) ..` — an
        // unrelated `Nat`-typed 2-path goal must not check.
        assert!(chk.check(&mut LocalCtx::new(), &cn("S2g.surf"), &bogus_goal).is_err());
        let red = Reducer::new(&env);
        assert!(!red.is_def_eq(&lit(0), &lit(1)));
    }

    /// Adversarial: per-`id` no cross-fire between two independently declared
    /// `S²`-shaped HITs (even structurally identical ones) — mirrors
    /// `no_cross_fire_between_two_distinct_declared_hits` one dimension up.
    #[test]
    fn no_cross_fire_between_two_distinct_s2_hits() {
        let mut env = base_env();
        let spec_a = CubHitSpec {
            name: "S2a".to_string(),
            points: vec![CubPointSpec::nullary("S2a.base")],
            paths: vec![],
            surfaces: vec![CubSurfSpec { name: "S2a.surf".to_string(), base: 0 }],
        };
        let spec_b = CubHitSpec {
            name: "S2b".to_string(),
            points: vec![CubPointSpec::nullary("S2b.base")],
            paths: vec![],
            surfaces: vec![CubSurfSpec { name: "S2b.surf".to_string(), base: 0 }],
        };
        declare_cubical_hit(&mut env, &spec_a).unwrap();
        declare_cubical_hit(&mut env, &spec_b).unwrap();
        let chk = Checker::new(&env);
        let motive = Term::lam(cn("S2a"), cn("Nat").lift(1, 0));
        let t = crate::cubical::refl(&crate::cubical::refl(&lit(0)));
        let bogus = Term::apps(
            Term::cnst(name("S2a.rec"), vec![Level::of_nat(1)]),
            [motive, lit(0), t, cn("S2b.base")],
        );
        assert!(chk.infer_closed(&bogus).is_err(), "S2a.rec must reject an S2b-typed scrutinee");
    }
}
