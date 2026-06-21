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

/// A single environment entry.
#[derive(Clone, Debug)]
pub enum Decl {
    Axiom { num_levels: u32, ty: Term },
    Def { num_levels: u32, ty: Term, value: Term },
    Inductive(Rc<Inductive>),
    Constructor(Rc<Constructor>),
    Recursor(Rc<Recursor>),
}

impl Decl {
    /// The declared type of this entry (every kind has one).
    pub fn ty(&self) -> &Term {
        match self {
            Decl::Axiom { ty, .. } | Decl::Def { ty, .. } => ty,
            Decl::Inductive(i) => &i.ty,
            Decl::Constructor(c) => &c.ty,
            Decl::Recursor(r) => &r.ty,
        }
    }
    /// How many universe parameters this entry abstracts over.
    pub fn num_levels(&self) -> u32 {
        match self {
            Decl::Axiom { num_levels, .. } | Decl::Def { num_levels, .. } => *num_levels,
            Decl::Inductive(i) => i.num_levels,
            Decl::Constructor(c) => c.num_levels,
            Decl::Recursor(r) => r.num_levels,
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
