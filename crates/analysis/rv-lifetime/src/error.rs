//! Lifetime error types.

use rv_span::FileSpan;
use thiserror::Error;

use crate::lifetime::{Lifetime, LifetimeId};

/// Result type for lifetime operations.
pub type LifetimeResult<T> = Result<T, LifetimeError>;

/// Errors that can occur during lifetime analysis.
#[derive(Debug, Clone, Error)]
pub enum LifetimeError {
    /// A value does not live long enough for its intended use.
    ///
    /// This occurs when a reference outlives the value it points to.
    #[error("value does not live long enough")]
    DoesNotLiveLongEnough {
        /// Location where the value is defined
        value_span: FileSpan,
        /// The lifetime that is required
        required_lifetime: Lifetime,
        /// The actual lifetime of the value
        actual_lifetime: Lifetime,
    },

    /// Circular lifetime dependency detected.
    ///
    /// This indicates an impossible constraint like `'a: 'b` and `'b: 'a`
    /// where neither is static.
    #[error("circular lifetime dependency detected")]
    CircularLifetime {
        /// The cycle of lifetime IDs
        cycle: Vec<LifetimeId>,
    },

    /// Cannot return a reference to a local variable.
    ///
    /// Local variables are deallocated when the function returns, so
    /// returning a reference to them would create a dangling pointer.
    #[error("cannot return reference to local variable")]
    ReturnLocalReference {
        /// Location of the return statement
        return_span: FileSpan,
        /// Location where the local variable was defined
        local_span: FileSpan,
    },

    /// Lifetime constraint cannot be satisfied.
    ///
    /// The constraint solver determined that the given constraint is
    /// impossible to satisfy.
    #[error("unsatisfiable lifetime constraint")]
    UnsatisfiableConstraint {
        /// The constraint that cannot be satisfied
        constraint: String,
        /// Source location
        span: FileSpan,
    },

    /// Conflicting lifetime bounds.
    ///
    /// Two bounds on a lifetime parameter conflict with each other.
    #[error("conflicting lifetime bounds")]
    ConflictingBounds {
        /// First bound
        first: Lifetime,
        /// Second bound
        second: Lifetime,
        /// Source location
        span: FileSpan,
    },
}

impl LifetimeError {
    /// Returns the primary source location for this error.
    #[must_use]
    pub fn span(&self) -> FileSpan {
        use rv_span::{FileId, Span};

        match self {
            Self::DoesNotLiveLongEnough { value_span, .. } => *value_span,
            Self::CircularLifetime { .. } => FileSpan::new(FileId(0), Span::new(0, 0)),
            Self::ReturnLocalReference { return_span, .. } => *return_span,
            Self::UnsatisfiableConstraint { span, .. } => *span,
            Self::ConflictingBounds { span, .. } => *span,
        }
    }
}
