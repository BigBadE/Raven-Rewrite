//! Core lifetime types and definitions.

use rv_intern::Symbol;
use rv_span::FileSpan;

/// Lifetime identifier used during inference.
///
/// Each lifetime variable gets a unique ID during the inference process.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LifetimeId(pub u32);

/// Region identifier representing runtime lifetime scope.
///
/// Regions are the concrete representation of lifetimes during execution.
/// They correspond to scopes in the program where values are live.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RegionId(pub u32);

/// A lifetime in the type system.
///
/// Lifetimes track how long values are valid for, enabling memory safety
/// without garbage collection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lifetime {
    /// Named lifetime parameter (e.g., `'a`, `'b`).
    ///
    /// These are explicitly written in function signatures and type definitions.
    Named {
        /// Unique identifier for this lifetime
        id: LifetimeId,
        /// Name as written in source code
        name: Symbol,
    },

    /// The `'static` lifetime.
    ///
    /// Values with static lifetime live for the entire program execution.
    Static,

    /// Inferred lifetime to be determined by the inference algorithm.
    ///
    /// These are created during type inference and resolved to concrete
    /// lifetimes or constraints.
    Inferred {
        /// Unique identifier for this inference variable
        id: LifetimeId,
    },

    /// Error lifetime used for error recovery.
    ///
    /// When lifetime analysis encounters an error, this sentinel value
    /// allows compilation to continue for better error reporting.
    Error,
}

impl Lifetime {
    /// Creates a new named lifetime.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rv_lifetime::{Lifetime, LifetimeId};
    /// use rv_intern::Symbol;
    ///
    /// let lifetime = Lifetime::named(LifetimeId(0), Symbol::from("a"));
    /// ```
    #[must_use]
    pub fn named(id: LifetimeId, name: Symbol) -> Self {
        Self::Named { id, name }
    }

    /// Creates a new inferred lifetime variable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rv_lifetime::{Lifetime, LifetimeId};
    ///
    /// let lifetime = Lifetime::inferred(LifetimeId(1));
    /// ```
    #[must_use]
    pub fn inferred(id: LifetimeId) -> Self {
        Self::Inferred { id }
    }

    /// Returns `true` if this is the static lifetime.
    #[must_use]
    pub fn is_static(&self) -> bool {
        matches!(self, Self::Static)
    }

    /// Returns `true` if this is an error lifetime.
    #[must_use]
    pub fn is_error(&self) -> bool {
        matches!(self, Self::Error)
    }

    /// Returns the lifetime ID if this is a named or inferred lifetime.
    #[must_use]
    pub fn id(&self) -> Option<LifetimeId> {
        match self {
            Self::Named { id, .. } | Self::Inferred { id } => Some(*id),
            Self::Static | Self::Error => None,
        }
    }
}

/// Lifetime parameter declaration on functions and types.
///
/// These appear in angle brackets like `fn foo<'a, 'b>` and can have
/// outlives bounds like `'a: 'b`.
#[derive(Debug, Clone)]
pub struct LifetimeParam {
    /// Unique identifier
    pub id: LifetimeId,
    /// Parameter name (e.g., `'a`)
    pub name: Symbol,
    /// Outlives bounds (`'a: 'b` means `'a` outlives `'b`)
    pub bounds: Vec<LifetimeId>,
    /// Source location
    pub span: FileSpan,
}

impl LifetimeParam {
    /// Creates a new lifetime parameter.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rv_lifetime::{LifetimeParam, LifetimeId};
    /// use rv_intern::Symbol;
    /// use rv_span::{FileId, FileSpan, Span};
    ///
    /// let param = LifetimeParam::new(
    ///     LifetimeId(0),
    ///     Symbol::from("a"),
    ///     vec![],
    ///     FileSpan::new(FileId(0), Span::new(0, 0)),
    /// );
    /// ```
    #[must_use]
    pub fn new(id: LifetimeId, name: Symbol, bounds: Vec<LifetimeId>, span: FileSpan) -> Self {
        Self {
            id,
            name,
            bounds,
            span,
        }
    }
}

/// Constraint between two lifetimes.
///
/// Constraints are generated during inference and then solved to determine
/// the final lifetime relationships.
#[derive(Debug, Clone)]
pub enum LifetimeConstraint {
    /// Outlives constraint: `sub: sup` means `sub` outlives `sup`.
    ///
    /// This means `sub` must be valid for at least as long as `sup`.
    Outlives {
        /// The sub-lifetime (must outlive sup)
        sub: Lifetime,
        /// The super-lifetime (must be outlived by sub)
        sup: Lifetime,
        /// Source location that generated this constraint
        source: FileSpan,
    },

    /// Equality constraint: `left = right`.
    ///
    /// Both lifetimes must be exactly the same.
    Equality {
        /// Left-hand side
        left: Lifetime,
        /// Right-hand side
        right: Lifetime,
        /// Source location that generated this constraint
        source: FileSpan,
    },
}

impl LifetimeConstraint {
    /// Creates an outlives constraint.
    #[must_use]
    pub fn outlives(sub: Lifetime, sup: Lifetime, source: FileSpan) -> Self {
        Self::Outlives { sub, sup, source }
    }

    /// Creates an equality constraint.
    #[must_use]
    pub fn equality(left: Lifetime, right: Lifetime, source: FileSpan) -> Self {
        Self::Equality {
            left,
            right,
            source,
        }
    }

    /// Returns the source location that generated this constraint.
    #[must_use]
    pub fn source(&self) -> FileSpan {
        match self {
            Self::Outlives { source, .. } | Self::Equality { source, .. } => *source,
        }
    }
}
