//! The global environment: the set of declarations the kernel reasons against.
//!
//! Everything that isn't pure λ-calculus lives here as a named declaration and is
//! referenced from terms by [`Term::Const`]. There are five kinds:
//!
//! * **Axiom** — a name with a type and no definition (e.g. classical `lem`). Trusted
//!   *as stated*; the kernel checks the type is well-formed but never the "truth".
//! * **Definition** — a name with a type and a value; unfolds by δ-reduction.
//! * **Inductive** — a datatype former (`Nat`, `Eq`, `And`, …).
//! * **Constructor** — an introduction rule of some inductive (`Nat.succ`).
//! * **Recursor** — the eliminator of some inductive (`Nat.rec`); its computation
//!   rules drive ι-reduction.
//!
//! Each declaration records how many **universe parameters** it abstracts over; a
//! `Const(name, levels)` referencing it must supply exactly that many level
//! arguments.

use crate::term::{Name, Term};
use std::collections::HashMap;
use std::rc::Rc;

/// One ι-reduction rule of a recursor: how it computes on a given constructor.
///
/// When `rec … (ctor fields…)` is fully applied, the reducer replaces it with `rhs`
/// applied to the recursor's *non-major* arguments followed by the constructor's
/// fields (see [`crate::reduce`] for the exact arity bookkeeping). `rhs` is a closed
/// term built at inductive-declaration time.
#[derive(Clone, Debug)]
pub struct RecRule {
    /// The constructor this rule fires on.
    pub ctor: Name,
    /// Number of (non-parameter) fields the constructor takes.
    pub num_fields: usize,
    /// The right-hand side, expecting to be applied to
    /// `[params…, motive, minors…, ctor_fields…]`.
    pub rhs: Term,
}

/// A recursor (eliminator) declaration.
#[derive(Clone, Debug)]
pub struct Recursor {
    /// Universe parameters of the recursor (the inductive's params plus, possibly,
    /// the motive's elimination universe).
    pub num_levels: u32,
    /// The recursor's own type.
    pub ty: Term,
    /// The inductive it eliminates.
    pub ind: Name,
    /// Number of parameters of the inductive (uniform across constructors).
    pub num_params: usize,
    /// Number of motives. `1` for an ordinary inductive; for a member of a **mutual**
    /// group it is the group size (one motive per type in the group), all of which
    /// precede the minor premises.
    pub num_motives: usize,
    /// Number of indices of the inductive.
    pub num_indices: usize,
    /// Number of minor premises (one per constructor — across *all* types of a mutual
    /// group).
    pub num_minors: usize,
    /// Per-constructor computation rules, keyed by constructor name.
    pub rules: HashMap<Name, RecRule>,
}

impl Recursor {
    /// Total count of arguments before the *major premise*: `params + motives +
    /// minors + indices`. The major premise (the scrutinee) sits at this position.
    pub fn major_pos(&self) -> usize {
        self.num_params + self.num_motives + self.num_minors + self.num_indices
    }
}

/// An inductive type former.
#[derive(Clone, Debug)]
pub struct Inductive {
    pub num_levels: u32,
    /// The type of the type former itself (e.g. `Nat : Type 0`, `Eq : Π A, A → A →
    /// Prop`).
    pub ty: Term,
    /// Number of uniform parameters (the prefix of the type former's domain shared
    /// by every constructor).
    pub num_params: usize,
    /// Number of indices (the remaining domain of the type former).
    pub num_indices: usize,
    /// Names of the constructors, in declaration order.
    pub ctors: Vec<Name>,
    /// Name of the recursor generated for this inductive.
    pub recursor: Name,
    /// The whole mutual group this type belongs to, in declaration order (just `[self]`
    /// for an ordinary inductive). Used to compile mutually-recursive functions.
    pub group: Vec<Name>,
}

/// A constructor declaration.
#[derive(Clone, Debug)]
pub struct Constructor {
    pub num_levels: u32,
    /// The constructor's type (a `Π`-telescope ending in an application of its
    /// inductive).
    pub ty: Term,
    /// The inductive this constructs.
    pub ind: Name,
    /// This constructor's position among its inductive's constructors (its tag).
    pub index: usize,
    /// Number of non-parameter fields.
    pub num_fields: usize,
}

/// A **coinductive** ("codata") type former — a *greatest* fixpoint.
///
/// Where an [`Inductive`] is presented by its **constructors** (introduction rules)
/// and eliminated by a **recursor**, a coinductive is presented by its
/// **destructors** ([`Destructor`], observation/projection rules) and *introduced*
/// by a **corecursor** ([`Corecursor`], the `unfold`/coiteration primitive). The two
/// are exact categorical duals: an inductive is the initial algebra of its
/// constructor-signature functor, a coinductive is the *final coalgebra* of its
/// destructor-signature functor.
///
/// The kernel supports coinductives with **uniform parameters** plus an optional
/// **index telescope** (e.g. `Stream A`, `Colist A`, or the indexed `Bisim A (s t :
/// Stream A) : Prop`). Each destructor observes one field of the unfolded state; a
/// destructor whose result type is the coinductive itself (e.g. `Stream.tail : Stream
/// A → Stream A`, or `Bisim.tail_bisim : Bisim A s t → Bisim A (tail s) (tail t)`) is a
/// *corecursive* observation — see [`crate::coinductive`] for the exact supported form
/// and restriction (a single non-indexed carrier `X`, indices transformed by a fixed
/// per-destructor term over `[params, indices]`).
#[derive(Clone, Debug)]
pub struct Coinductive {
    pub num_levels: u32,
    /// The type former's type: `Π params. Π indices. Sort _`.
    pub ty: Term,
    /// Number of uniform parameters.
    pub num_params: usize,
    /// Number of indices (0 for the original non-indexed form).
    pub num_indices: usize,
    /// Names of the destructors, in declaration order.
    pub dtors: Vec<Name>,
    /// Name of the corecursor generated for this coinductive.
    pub corecursor: Name,
}

/// A **destructor** (observation) of a coinductive: `d : Π params. S params → R`.
///
/// `R` (the *result* type, under the params and the scrutinee binder) is either an
/// ordinary type (a plain observation, like `Stream.head : Stream A → A`) or the
/// coinductive itself applied to the parameters (a *corecursive* observation, like
/// `Stream.tail : Stream A → Stream A`). Applying a destructor to a corecursor
/// application is the ν-redex that drives coinductive computation.
#[derive(Clone, Debug)]
pub struct Destructor {
    pub num_levels: u32,
    /// The destructor's type: `Π params. S params → R`.
    pub ty: Term,
    /// The coinductive it observes.
    pub coind: Name,
    /// This destructor's position among its coinductive's destructors (its tag).
    pub index: usize,
    /// Whether this observation returns the coinductive itself (a corecursive step).
    pub corecursive: bool,
}

/// The **corecursor** (`S.corec`/`unfold`) of a coinductive — its sole introduction
/// rule and the dual of a [`Recursor`].
///
/// Its type is
///
/// ```text
///   S.corec.{levels v} : Π params.
///       Π (X : Sort v).                                     -- the coalgebra carrier / state
///       Π (step_d : Π indices. X → R_d[X for S]) …          -- one (index-polymorphic) step per destructor d
///       Π indices (seed : X). S params indices
/// ```
///
/// where for a plain destructor `R_d` is its result type (which may mention the
/// *step's own* `indices` binders) and for a corecursive destructor `R_d` is `X` (the
/// *next* state — the carrier itself is **not** indexed; see [`crate::coinductive`]).
/// The trailing `indices` (right before `seed`) are the *current* indices, threaded
/// through the ν-rule and updated at each corecursive observation by substituting the
/// destructor's declared index-transform (see [`CorecRule::index_transform`]). A
/// single ν-rule per destructor drives reduction: observing the seed unfolds exactly
/// one layer (see [`crate::reduce`]).
#[derive(Clone, Debug)]
pub struct Corecursor {
    pub num_levels: u32,
    pub ty: Term,
    /// The coinductive it introduces.
    pub coind: Name,
    pub num_params: usize,
    /// Number of destructors (= number of `step` arguments).
    pub num_dtors: usize,
    /// Number of indices (0 for the original non-indexed form).
    pub num_indices: usize,
    /// Per-destructor ν-reduction data, keyed by destructor name.
    pub rules: HashMap<Name, CorecRule>,
}

impl Corecursor {
    /// Position of the carrier `X` argument in `S.corec`'s spine (right after params).
    pub fn carrier_pos(&self) -> usize {
        self.num_params
    }
    /// Position of the first "current indices" argument: `params + carrier + steps`.
    pub fn index_pos(&self) -> usize {
        self.num_params + 1 + self.num_dtors
    }
    /// Position of the `seed` argument: `params + carrier + steps + indices`.
    pub fn seed_pos(&self) -> usize {
        self.index_pos() + self.num_indices
    }
    /// Total number of arguments `S.corec` takes.
    pub fn arity(&self) -> usize {
        self.seed_pos() + 1
    }
}

/// One ν-reduction rule: how observing destructor `dtor` of a corecursor application
/// computes.
#[derive(Clone, Debug)]
pub struct CorecRule {
    pub dtor: Name,
    /// The step argument's position among `S.corec`'s arguments.
    pub step_index: usize,
    /// Whether this destructor is corecursive (its result is the coinductive again).
    pub corecursive: bool,
    /// For a **corecursive** destructor: the new index arguments, one term per index,
    /// each living in the context `[params, indices]` (params outermost, `Var(0)` the
    /// innermost/last index — see [`crate::coinductive`]). Instantiating these with the
    /// corecursor's *current* `[params, indices]` arguments computes the *next*
    /// indices at ν-reduction time. Empty when `num_indices == 0` or the destructor is
    /// plain.
    pub index_transform: Vec<Term>,
}

/// Which of the five fixed **quotient** constants a [`Quotient`] declaration is.
///
/// The quotient schema (`Quot`, `Quot.mk`, `Quot.sound`, `Quot.lift`, `Quot.ind`) is a
/// fixed set of constants installed once (see [`crate::quotient`]), not a per-quotient
/// datatype. The reducer needs to recognise only `Lift` (its computation rule fires on
/// a `Mk` scrutinee); the other roles are ordinary typed constants with no reduction of
/// their own (`Sound` and `Type`/`Mk`/`Ind` are canonical/neutral).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum QuotRole {
    /// The type former `Quot A R`.
    Type,
    /// The constructor `Quot.mk A R a`.
    Mk,
    /// The soundness axiom `Quot.sound … : R a b → mk a = mk b`.
    Sound,
    /// The eliminator `Quot.lift A R B f resp : Quot A R → B` (drives the ι-rule
    /// `Quot.lift … f resp (Quot.mk … a) ↦ f a`).
    Lift,
    /// The `Prop`-eliminator `Quot.ind` (no computation rule; sound by proof
    /// irrelevance — see [`crate::quotient`]).
    Ind,
    /// The **dependent** recursor `Quot.rec A R C f resp : Π (q : Quot A R), C q`,
    /// eliminating into an arbitrary `Sort v` (not just `Prop`) given a respectfulness
    /// premise transporting `f a` to `f b` along `Quot.sound` whenever `R a b`. Drives
    /// the same-shaped ι-rule `Quot.rec … C f resp (Quot.mk … a) ↦ f a` (its argument
    /// spine positions coincide with `Lift`'s: `f` at index 3, the scrutinee at index
    /// 5) — see [`crate::quotient`].
    Rec,
}

/// Which of the five fixed **propositional-truncation** constants a [`Trunc`]
/// declaration is.
///
/// Propositional truncation `∥A∥` (`Trunc A : Prop`) is the canonical *higher inductive
/// type* (see [`crate::trunc`]): a point constructor `tr : A → ∥A∥` together with a
/// **path/equality constructor** collapsing `∥A∥` to a mere proposition
/// (`eq : Π (x y : ∥A∥), x = y`). Like the quotient schema it is a fixed set of constants
/// installed once, not a per-instance datatype. The reducer needs to recognise only
/// `Lift` (its computation rule fires on a `Tr` scrutinee); the others are ordinary typed
/// constants with no reduction of their own.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TruncRole {
    /// The type former `Trunc A : Prop`.
    Type,
    /// The point constructor `Trunc.tr A a : Trunc A`.
    Tr,
    /// The path constructor `Trunc.eq A x y : x = y` (all elements equal — the
    /// *truncation* that makes `Trunc A` a mere proposition). Identifies propositionally
    /// (through `Eq`), never definitionally.
    Eq,
    /// The recursor `Trunc.lift A P f resp : Trunc A → P` (drives the ι-rule
    /// `Trunc.lift … f resp (Trunc.tr … a) ↦ f a`).
    Lift,
    /// The `Prop`-eliminator `Trunc.ind` (no computation rule; sound by proof
    /// irrelevance — see [`crate::trunc`]).
    Ind,
    /// The **isProp-guarded dependent** recursor `Trunc.rec A C isProp f : Π t, C t`,
    /// eliminating into an arbitrary `Sort v` (not just `Prop`) given a proof that `C`
    /// is a mere proposition *pointwise* (`isProp : Π t (x y : C t), Eq (C t) x y`).
    /// Drives the ι-rule `Trunc.rec … isProp f (Trunc.tr … a) ↦ f a` (spine positions:
    /// `f` at index 3, the scrutinee at index 4) — see [`crate::trunc`].
    Rec,
}

/// A member of the fixed **propositional-truncation** schema — one of the five `Trunc*`
/// constants. Structurally identical to [`Quotient`]; kept as a distinct decl so the
/// reducer can special-case `Trunc.lift` independently of `Quot.lift`.
#[derive(Clone, Debug)]
pub struct Trunc {
    pub role: TruncRole,
    pub num_levels: u32,
    pub ty: Term,
}

/// Which of the five fixed **circle** constants a [`Circle`] declaration is.
///
/// The circle `S¹` (see [`crate::circle`]) is a **non-truncated** 1-HIT: a point
/// constructor `base : S¹` together with a genuine self-loop **path** constructor
/// `loop : Eq S¹ base base`. Unlike [`Trunc`] (whose `eq` identifies *every* pair of
/// points, collapsing the type to a mere proposition and living in `Prop`), `S¹` lives in
/// `Type` and only ONE specific path is postulated — the defining example of a
/// non-truncated HIT. The reducer needs to recognise only `Rec` (its computation rule
/// fires on a `Base` scrutinee); the others are ordinary typed constants with no
/// reduction of their own.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CircleRole {
    /// The type former `S¹ : Type 0`.
    Type,
    /// The point constructor `S¹.base : S¹`.
    Base,
    /// The path constructor `S¹.loop : Eq S¹ S¹.base S¹.base` (a self-loop). Holds only
    /// propositionally (through `Eq`), never definitionally.
    Loop,
    /// The non-dependent recursor `S¹.rec P pt lp : S¹ → P` (drives the ι-rule
    /// `S¹.rec P pt lp S¹.base ↦ pt`; `lp : Eq P pt pt` is the respectfulness premise for
    /// the `loop` path constructor, discarded at reduction time).
    Rec,
    /// The `Prop`-eliminator `S¹.ind` (no computation rule; sound by proof irrelevance —
    /// see [`crate::circle`]).
    Ind,
}

/// A member of the fixed **circle** schema — one of the five `S¹.*` constants.
/// Structurally identical to [`Trunc`]; kept as a distinct decl so the reducer can
/// special-case `S¹.rec` independently of `Trunc.lift`/`Quot.lift`.
#[derive(Clone, Debug)]
pub struct Circle {
    pub role: CircleRole,
    pub num_levels: u32,
    pub ty: Term,
}

/// Which role a member of a **user-declared 1-HIT** (see [`crate::hit`]) plays. Unlike
/// [`CircleRole`]/[`TruncRole`] (each a fixed, hand-coded five-constant instance),
/// [`crate::hit::declare_hit`] installs a *family* of these per user declaration, so
/// every [`Hit`] additionally carries an `id` (the type former's name) identifying
/// *which* declared HIT it belongs to — the reducer/NbE must only ever match a `Rec`
/// scrutinee against a `Point` of the *same* `id`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum HitRole {
    /// The type former `H : Type 0`.
    Type,
    /// A point constructor, tagged with its `0`-based index among the declared point
    /// constructors — this is what the `Rec`/`Ind` ι-rules match on and what a path
    /// constructor's `lhs`/`rhs` refer to — plus its field list: `fields[j] == true`
    /// means field `j` is a **recursive** occurrence of `H` itself (the ι-rule
    /// substitutes a recursive `H.rec` call for it); `false` means a non-recursive
    /// field of some fixed, closed (`H`-free) type. `fields.len()` is this point
    /// constructor's arity — `0` recovers the original nullary case.
    Point { index: u32, fields: Rc<Vec<bool>> },
    /// A path constructor `H.<name> : Eq H point[lhs] point[rhs]`, holding only
    /// propositionally (through `Eq`) — never definitionally, and with no reduction
    /// rule of its own. `lhs`/`rhs` are point-constructor indices.
    Path { lhs: u32, rhs: u32 },
    /// The non-dependent recursor `H.rec.{v} : Π P case_0 .. case_{n-1} resp_0 ..
    /// resp_{m-1}, H → P`, gated by one respectfulness premise `resp_j : Eq P
    /// case_{lhs_j} case_{rhs_j}` per declared path constructor. Its single ι-rule
    /// fires only when the scrutinee weak-head-reduces to a `Point { index: i }` of the
    /// *same* `id`, reducing to `case_i` (discarding all `resp_j`).
    Rec { num_points: u32, num_paths: u32 },
    /// The `Prop`-only dependent eliminator `H.ind : Π (β : H → Prop) (h_0 : β
    /// point_0) .. (h_{n-1} : β point_{n-1}), Π t, β t`. No computation rule of its
    /// own; sound by proof irrelevance in `Prop` exactly as `S¹.ind`/`Trunc.ind`.
    Ind { num_points: u32 },
}

/// Which of the five fixed **interval-HIT** constants an [`I2`] declaration is.
///
/// `I2` (see [`crate::interval_hit`]) is the **computing** counterpart of [`Circle`]:
/// two point constructors `zero`/`one : I2` and a genuine **cubical** path constructor
/// `seg : Path I2 zero one` (a [`crate::term::Term::PathP`]/`PLam`-classified path, not
/// an inductive `Eq`), together with a **`Type`-valued, computing** dependent recursor
/// `I2.rec`. Unlike [`CircleRole`]'s `S¹.rec` (whose `lp : Eq P pt pt` premise is
/// discarded at ι-time, and which only ever fires on the point constructor `base`),
/// `I2.rec`'s ι-rules fire on *both* `zero`/`one` **and** on `seg @ r` — the point where
/// this schema genuinely outruns the propositional (`Eq`-based) HIT machinery: the path
/// constructor itself computes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum I2Role {
    /// The type former `I2 : Type 0`.
    Type,
    /// The point constructor `I2.zero : I2`.
    Zero,
    /// The point constructor `I2.one : I2`.
    One,
    /// The cubical path constructor `I2.seg : Path I2 I2.zero I2.one` — a genuine
    /// `PathP`/`PLam`-classified path (see [`crate::cubical`]), not an inductive `Eq`.
    /// Holds *definitionally*: `I2.seg @ r` is a bona fide interval application, and
    /// (via `I2.rec`'s ι-rule) actually computes.
    Seg,
    /// The **`Type`-valued, computing** dependent recursor
    /// `I2.rec.{v} : Π (C : I2 → Sort v) (c0 : C zero) (c1 : C one)
    ///   (s : PathP (λ i. C (seg @ i)) c0 c1) (x : I2), C x`.
    /// Drives **two** ι-rules (see [`crate::interval_hit`]):
    ///   `I2.rec C c0 c1 s zero ↦ c0`, `I2.rec C c0 c1 s one ↦ c1` (point ι-rules,
    ///   analogous to [`CircleRole::Rec`]'s single point rule), **and**
    ///   `I2.rec C c0 c1 s (seg @ r) ↦ s @ r` (the **path** ι-rule — the one a
    ///   propositional/`Eq`-based HIT recursor cannot express, since there `s` would be
    ///   discarded rather than applied).
    Rec,
}

/// A member of the fixed **interval-HIT** schema — one of the five `I2.*` constants.
/// See [`I2Role`] and [`crate::interval_hit`] for the full schema and its soundness
/// argument.
#[derive(Clone, Debug)]
pub struct I2 {
    pub role: I2Role,
    pub num_levels: u32,
    pub ty: Term,
}

/// Which of the four fixed **cubical circle** constants an [`S1c`] declaration is.
///
/// `S1c` (see [`crate::circle_cubical`]) is the cubical counterpart of [`Circle`]
/// (`S¹`, `Eq`-based, propositional `loop`) in the same way [`I2`] is the cubical
/// counterpart of the interval — here there is exactly *one* point constructor
/// (`base`) and exactly *one* path constructor, but that path constructor is a
/// genuine **self**-loop: `loop : Path S1c base base`, both endpoints `base`. The
/// dependent recursor `S1c.rec`'s path ι-rule fires on `loop @ r`, computing it away
/// to `l @ r` for the caller-supplied `l : PathP (λi. C (loop @ i)) b b` — the thing
/// `S1.loop`'s `Eq`-classified, non-computing path cannot express.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum S1cRole {
    /// The type former `S1c : Type 0`.
    Type,
    /// The point constructor `S1c.base : S1c`.
    Base,
    /// The cubical path constructor `S1c.loop : Path S1c S1c.base S1c.base` — a
    /// genuine `PathP`/`PLam`-classified SELF-loop (see [`crate::cubical`]), not an
    /// inductive `Eq`. Both endpoints are (definitionally) `S1c.base`.
    Loop,
    /// The **`Type`-valued, computing** dependent recursor
    /// `S1c.rec.{v} : Π (C : S1c → Sort v) (b : C base)
    ///   (l : PathP (λ i. C (loop @ i)) b b) (x : S1c), C x`.
    /// Drives **two** ι-rules (see [`crate::circle_cubical`]):
    ///   `S1c.rec C b l base ↦ b` (point ι-rule), and
    ///   `S1c.rec C b l (loop @ r) ↦ l @ r` (the **path** ι-rule — the loop
    ///   computes).
    Rec,
}

/// A member of the fixed **cubical circle** schema — one of the four `S1c.*`
/// constants. See [`S1cRole`] and [`crate::circle_cubical`] for the full schema and
/// its soundness argument.
#[derive(Clone, Debug)]
pub struct S1c {
    pub role: S1cRole,
    pub num_levels: u32,
    pub ty: Term,
}

/// Which of a **general, user-declarable cubical HIT**'s constants a [`CubHit`]
/// declaration is (see [`crate::cubical_hit`]). This generalizes [`I2Role`]/
/// [`S1cRole`] into one parameterized schema: `n ≥ 1` nullary point constructors
/// and `m ≥ 0` genuine cubical `Path` constructors between (possibly equal, i.e.
/// self-loop) point constructors, plus one `Type`-valued, computing recursor whose
/// ι-rules are synthesized generically from `n`/`m` rather than hand-written per
/// HIT. Every constant belonging to one declared HIT shares the same [`CubHit::id`]
/// (the HIT's own type-former name), so the reducer/NbE only ever fire a HIT's
/// ι-rules against scrutinees built from *that same* HIT's constructors — two
/// distinct `declare_cubical_hit` calls never cross-fire, exactly as
/// [`Hit`]/[`HitRole`] already ensure for the propositional (`Eq`-based) schema.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CubHitRole {
    /// The type former `H : Type 0`.
    Type,
    /// The `i`-th (0-based) point constructor `H.point_i`, tagged with its field
    /// list exactly as [`HitRole::Point`]: `fields[j] == true` means field `j` is a
    /// **strictly-positive recursive** occurrence of `H` itself (the `Rec` ι-rule
    /// threads a recursive `H.rec` call through it, plus an extra induction-hypothesis
    /// binder in the recursor's motive-dependent case type — see
    /// [`crate::cubical_hit`]); `false` means a non-recursive field of some fixed,
    /// closed (`H`-free) type. `fields.len()` is this point constructor's arity — `0`
    /// recovers the original nullary case (`I2`/`S1c`/figure-eight).
    Point { idx: u32, fields: Rc<Vec<bool>> },
    /// The `j`-th (0-based) cubical path constructor `H.path_j : Π quantifiers..,
    /// Path H (H.point_{lhs} lhs_args..) (H.point_{rhs} rhs_args..)` — a genuine
    /// `PathP`/`PLam`-classified path (see [`crate::cubical`]), not an inductive
    /// `Eq`. `lhs == rhs` is a legal self-loop. `num_quant` is the number of extra
    /// universally-quantified binders `H.path_j` takes before yielding the `Path`
    /// (`0` recovers the original unquantified case) — the ι-rule matches the
    /// scrutinee's path-constructor spine against exactly this many arguments before
    /// firing, mirroring [`HitRole::Point`]'s arity check.
    Path { idx: u32, lhs: u32, rhs: u32, num_quant: u32 },
    /// The `k`-th (0-based) **2-dimensional ("surface"/higher) path constructor**
    /// `H.surf_k : PathP (λi. Path H (l@i) (r@i)) top bottom` — a genuine
    /// square/2-cell based at a single **nullary** point constructor `base`, whose
    /// four sides `l`/`r`/`top`/`bottom` are each either `refl (H.point_base)`
    /// (`None`) or a declared, **unquantified self-loop** 1-path constructor at
    /// `base` (`Some(path_idx)`) — see [`crate::cubical_hit`]'s module doc,
    /// "2-dimensional (higher) path constructors". The all-`None` case recovers
    /// the original "S²" shape exactly; e.g. the torus `T²` sets `l = r =
    /// Some(loopP_idx)`, `top = bottom = Some(loopQ_idx)`. `base` is the (0-based)
    /// index of that nullary point constructor. Doubly `PApp`-applied
    /// (`H.surf_k @ i @ j`), never singly — the ι-rule matches exactly that
    /// doubly-applied spine shape (independent of the sides' shape, which only
    /// affects *typing*, not this structural reduction rule).
    Surf { idx: u32, base: u32, left: Option<u32>, right: Option<u32>, top: Option<u32>, bottom: Option<u32> },
    /// The `l`-th (0-based) **3-dimensional ("cube"/higher) path constructor**
    /// `H.cube_l : PathP (λi. PathP (λj. Path H p p) (refl p) (refl p))
    /// (refl (refl p)) (refl (refl p))` — a fully-degenerate 3-cell based at a
    /// single **nullary** point constructor `base` (the "S³" shape — see
    /// [`crate::cubical_hit::CubCubeSpec`]'s doc comment; unlike [`Self::Surf`],
    /// no `left`/`right`/`top`/`bottom` sides — every side is `refl` at this
    /// dimension, generalization to non-degenerate 3-cells is deferred).
    /// Triply `PApp`-applied (`H.cube_l @ i @ j @ k`), never fewer — the
    /// ι-rule matches exactly that triply-applied spine shape.
    Cube { idx: u32, base: u32 },
    /// The **`Type`-valued, computing** dependent recursor `H.rec`, generically
    /// synthesized for `num_points` point constructors, `num_paths` path
    /// constructors, `num_surfaces` 2-path ("surface") constructors, and
    /// `num_cubes` 3-path ("cube") constructors (see [`crate::cubical_hit`] for
    /// the exact signature and ι-rules — a direct generalization of
    /// [`I2Role::Rec`]/[`S1cRole::Rec`]).
    Rec { num_points: u32, num_paths: u32, num_surfaces: u32, num_cubes: u32 },
}

/// A member of a **general, user-declared cubical HIT**, installed by
/// [`crate::cubical_hit::declare_cubical_hit`]. See [`CubHitRole`] for the
/// per-constant breakdown and [`crate::cubical_hit`] for the schema's supported
/// class and soundness argument.
#[derive(Clone, Debug)]
pub struct CubHit {
    /// The name of this HIT's type former, shared by every constant of the same
    /// declaration — the reducer/NbE compare this `id` before firing any ι-rule so
    /// distinct declared cubical HITs never cross-fire.
    pub id: Name,
    pub role: CubHitRole,
    pub num_levels: u32,
    pub ty: Term,
}

/// A member of a **user-declared 1-HIT** family, installed by
/// [`crate::hit::declare_hit`]. See [`HitRole`] for the per-constant breakdown and
/// [`crate::hit`] for the schema's soundness argument and the supported class of HITs.
#[derive(Clone, Debug)]
pub struct Hit {
    /// The name of this HIT's type former — shared by every constant belonging to the
    /// same declaration, so the reducer/NbE never cross-match constants from two
    /// different user-declared HITs.
    pub id: Name,
    pub role: HitRole,
    pub num_levels: u32,
    pub ty: Term,
}

/// A member of the fixed **quotient** schema — one of the five `Quot*` constants.
///
/// Unlike inductives/coinductives there is no per-quotient elaboration: `install_quot`
/// installs all five constants with fixed, closed types. The [reducer](crate::reduce)
/// and [`crate::nbe`] special-case the [`QuotRole::Lift`] constant to implement the one
/// quotient computation rule; every other role is a plain typed constant.
#[derive(Clone, Debug)]
pub struct Quotient {
    pub role: QuotRole,
    pub num_levels: u32,
    pub ty: Term,
}

/// A single environment entry.
#[derive(Clone, Debug)]
pub enum Decl {
    Axiom { num_levels: u32, ty: Term },
    Def { num_levels: u32, ty: Term, value: Term },
    Inductive(Rc<Inductive>),
    Constructor(Rc<Constructor>),
    Recursor(Rc<Recursor>),
    Coinductive(Rc<Coinductive>),
    Destructor(Rc<Destructor>),
    Corecursor(Rc<Corecursor>),
    Quot(Rc<Quotient>),
    Trunc(Rc<Trunc>),
    Circle(Rc<Circle>),
    Hit(Rc<Hit>),
    I2(Rc<I2>),
    S1c(Rc<S1c>),
    CubHit(Rc<CubHit>),
}

impl Decl {
    /// The declared type of this entry (every kind has one).
    pub fn ty(&self) -> &Term {
        match self {
            Decl::Axiom { ty, .. } | Decl::Def { ty, .. } => ty,
            Decl::Inductive(i) => &i.ty,
            Decl::Constructor(c) => &c.ty,
            Decl::Recursor(r) => &r.ty,
            Decl::Coinductive(c) => &c.ty,
            Decl::Destructor(d) => &d.ty,
            Decl::Corecursor(c) => &c.ty,
            Decl::Quot(q) => &q.ty,
            Decl::Trunc(t) => &t.ty,
            Decl::Circle(c) => &c.ty,
            Decl::Hit(h) => &h.ty,
            Decl::I2(c) => &c.ty,
            Decl::S1c(c) => &c.ty,
            Decl::CubHit(c) => &c.ty,
        }
    }
    /// How many universe parameters this entry abstracts over.
    pub fn num_levels(&self) -> u32 {
        match self {
            Decl::Axiom { num_levels, .. } | Decl::Def { num_levels, .. } => *num_levels,
            Decl::Inductive(i) => i.num_levels,
            Decl::Constructor(c) => c.num_levels,
            Decl::Recursor(r) => r.num_levels,
            Decl::Coinductive(c) => c.num_levels,
            Decl::Destructor(d) => d.num_levels,
            Decl::Corecursor(c) => c.num_levels,
            Decl::Quot(q) => q.num_levels,
            Decl::Trunc(t) => t.num_levels,
            Decl::Circle(c) => c.num_levels,
            Decl::Hit(h) => h.num_levels,
            Decl::I2(c) => c.num_levels,
            Decl::S1c(c) => c.num_levels,
            Decl::CubHit(c) => c.num_levels,
        }
    }
}

/// The global declaration store.
#[derive(Clone, Debug, Default)]
pub struct Env {
    decls: HashMap<Name, Decl>,
}

impl Env {
    pub fn new() -> Self {
        Self::default()
    }

    /// Look up a declaration by name.
    pub fn get(&self, n: &str) -> Option<&Decl> {
        self.decls.get(n)
    }

    /// Whether `n` is declared.
    pub fn contains(&self, n: &str) -> bool {
        self.decls.contains_key(n)
    }

    /// Insert a declaration, rejecting redeclaration (names are immutable once
    /// added — the kernel never overwrites).
    pub fn insert(&mut self, n: Name, d: Decl) -> Result<(), String> {
        if self.decls.contains_key(&n) {
            return Err(format!("'{n}' is already declared"));
        }
        self.decls.insert(n, d);
        Ok(())
    }

    /// Iterate over every stored declaration (name, decl). Used by tooling that needs to
    /// walk the whole environment — e.g. the independent re-check harness in
    /// [`crate::kernel::recheck_all_definitions`] — never by the checker itself, which
    /// only ever looks up declarations by name.
    pub fn iter(&self) -> impl Iterator<Item = (&Name, &Decl)> {
        self.decls.iter()
    }
}
