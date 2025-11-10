//! Borrow checking error types.

use rv_mir::Place;
use rv_span::FileSpan;
use thiserror::Error;

use crate::loans::Loan;

/// Result type for borrow checking operations.
///
/// Borrow checking can produce multiple errors, so we collect them all.
pub type BorrowResult<T> = Result<T, Vec<BorrowError>>;

/// Errors that can occur during borrow checking.
#[derive(Debug, Clone, Error)]
pub enum BorrowError {
    /// Conflicting borrows of the same place.
    ///
    /// This occurs when trying to create a mutable borrow while an immutable
    /// borrow exists, or when trying to create any borrow while a mutable
    /// borrow exists.
    #[error("cannot borrow as mutable while immutably borrowed")]
    ConflictingBorrow {
        /// The new borrow that conflicts
        new_borrow: Loan,
        /// The existing borrow that it conflicts with
        existing_borrow: Loan,
    },

    /// Attempting to write to a borrowed place.
    ///
    /// When a place is borrowed (even immutably), the original location
    /// cannot be written to.
    #[error("cannot write to borrowed place")]
    WriteWhileBorrowed {
        /// The place being written to
        place: Place,
        /// The active loan preventing the write
        loan: Loan,
        /// Location of the write
        write_span: FileSpan,
    },

    /// Use of a moved value.
    ///
    /// After a value is moved, it can no longer be used.
    #[error("use of moved value")]
    UseAfterMove {
        /// The place being accessed
        place: Place,
        /// Location of the use
        use_span: FileSpan,
        /// Location where the value was moved
        move_span: FileSpan,
    },

    /// Attempting to borrow a moved value.
    ///
    /// Cannot create a reference to a value that has been moved.
    #[error("borrow of moved value")]
    BorrowAfterMove {
        /// The place being borrowed
        place: Place,
        /// Location of the borrow
        borrow_span: FileSpan,
        /// Location where the value was moved
        move_span: FileSpan,
    },

    /// Attempting to move a borrowed value.
    ///
    /// Cannot move a value while it is borrowed.
    #[error("cannot move out of borrowed value")]
    MoveWhileBorrowed {
        /// The place being moved
        place: Place,
        /// The active loan preventing the move
        loan: Loan,
        /// Location of the move
        move_span: FileSpan,
    },
}

impl BorrowError {
    /// Returns the primary source location for this error.
    #[must_use]
    pub fn span(&self) -> FileSpan {
        match self {
            Self::ConflictingBorrow { new_borrow, .. } => new_borrow.span,
            Self::WriteWhileBorrowed { write_span, .. } => *write_span,
            Self::UseAfterMove { use_span, .. } => *use_span,
            Self::BorrowAfterMove { borrow_span, .. } => *borrow_span,
            Self::MoveWhileBorrowed { move_span, .. } => *move_span,
        }
    }

    /// Returns a detailed message explaining the error.
    #[must_use]
    pub fn detailed_message(&self) -> String {
        match self {
            Self::ConflictingBorrow {
                new_borrow,
                existing_borrow,
            } => {
                format!(
                    "Cannot borrow {:?} as {:?} because it is already borrowed as {:?}",
                    new_borrow.place, new_borrow.kind, existing_borrow.kind
                )
            }
            Self::WriteWhileBorrowed { place, loan, .. } => {
                format!(
                    "Cannot write to {:?} because it is borrowed as {:?}",
                    place, loan.kind
                )
            }
            Self::UseAfterMove { place, .. } => {
                format!("Value {:?} has been moved and can no longer be used", place)
            }
            Self::BorrowAfterMove { place, .. } => {
                format!(
                    "Cannot borrow {:?} because it has already been moved",
                    place
                )
            }
            Self::MoveWhileBorrowed { place, loan, .. } => {
                format!(
                    "Cannot move {:?} because it is borrowed as {:?}",
                    place, loan.kind
                )
            }
        }
    }
}
