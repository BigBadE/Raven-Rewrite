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
/// The kernel supports the **non-indexed** coinductive case with **uniform
/// parameters** (e.g. `Stream A`, `Colist A`). Each destructor observes one field of
/// the unfolded state; a destructor whose result type is the coinductive itself
/// (e.g. `Stream.tail : Stream A → Stream A`) is a *corecursive* observation.
#[derive(Clone, Debug)]
pub struct Coinductive {
    pub num_levels: u32,
    /// The type former's type: `Π params. Sort _` (no indices in the supported form).
    pub ty: Term,
    /// Number of uniform parameters.
    pub num_params: usize,
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
///       Π (X : Sort v).                                  -- the coalgebra carrier / state
///       Π (step_d : Π (x:X). R_d[X for S]) …             -- one step per destructor d
///       Π (seed : X). S params
/// ```
///
/// where for a plain destructor `R_d` is its result type and for a corecursive
/// destructor `R_d` is `X` (the *next* state). A single ν-rule per destructor drives
/// reduction: observing the seed unfolds exactly one layer (see [`crate::reduce`]).
#[derive(Clone, Debug)]
pub struct Corecursor {
    pub num_levels: u32,
    pub ty: Term,
    /// The coinductive it introduces.
    pub coind: Name,
    pub num_params: usize,
    /// Number of destructors (= number of `step` arguments).
    pub num_dtors: usize,
    /// Per-destructor ν-reduction data, keyed by destructor name.
    pub rules: HashMap<Name, CorecRule>,
}

impl Corecursor {
    /// Position of the carrier `X` argument in `S.corec`'s spine (right after params).
    pub fn carrier_pos(&self) -> usize {
        self.num_params
    }
    /// Position of the `seed` argument: `params + carrier + steps`.
    pub fn seed_pos(&self) -> usize {
        self.num_params + 1 + self.num_dtors
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
}
