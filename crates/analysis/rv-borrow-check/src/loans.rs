//! Loan tracking for borrow checking.

use rv_lifetime::RegionId;
use rv_mir::Place;
use rv_span::FileSpan;

/// Kind of borrow operation.
///
/// This determines what access is allowed to the borrowed value and what
/// restrictions are placed on the original value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BorrowKind {
    /// Shared borrow (`&T`).
    ///
    /// Multiple shared borrows can coexist. The original value can still
    /// be read but not written or moved.
    Shared,

    /// Mutable borrow (`&mut T`).
    ///
    /// Only one mutable borrow can exist at a time. The original value
    /// cannot be accessed at all while the mutable borrow is active.
    Mutable,

    /// Move (take ownership).
    ///
    /// The value is moved out, and the original location is no longer
    /// accessible.
    Move,
}

impl BorrowKind {
    /// Returns `true` if this is a mutable borrow.
    #[must_use]
    pub fn is_mutable(&self) -> bool {
        matches!(self, Self::Mutable)
    }

    /// Returns `true` if this is a shared borrow.
    #[must_use]
    pub fn is_shared(&self) -> bool {
        matches!(self, Self::Shared)
    }

    /// Returns `true` if this is a move.
    #[must_use]
    pub fn is_move(&self) -> bool {
        matches!(self, Self::Move)
    }
}

/// A loan represents an active borrow.
///
/// Loans are created when a reference is taken and remain active for the
/// duration of the reference's lifetime (region).
#[derive(Debug, Clone)]
pub struct Loan {
    /// The place being borrowed
    pub place: Place,
    /// The kind of borrow
    pub kind: BorrowKind,
    /// The region (lifetime scope) this loan is active for
    pub region: RegionId,
    /// Source location where the borrow occurred
    pub span: FileSpan,
}

impl Loan {
    /// Creates a new loan.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rv_borrow_check::{Loan, BorrowKind};
    /// use rv_mir::{Place, LocalId};
    /// use rv_lifetime::RegionId;
    /// use rv_span::{FileId, FileSpan, Span};
    ///
    /// let loan = Loan::new(
    ///     Place::from_local(LocalId(0)),
    ///     BorrowKind::Shared,
    ///     RegionId(0),
    ///     FileSpan::new(FileId(0), Span::new(0, 0)),
    /// );
    /// ```
    #[must_use]
    pub fn new(place: Place, kind: BorrowKind, region: RegionId, span: FileSpan) -> Self {
        Self {
            place,
            kind,
            region,
            span,
        }
    }
}

/// Set of active loans at a program point.
///
/// This tracks all currently active borrows and provides methods to check
/// whether new borrows would conflict with existing ones.
#[derive(Debug, Clone)]
pub struct LoanSet {
    /// Active loans
    loans: Vec<Loan>,
}

impl LoanSet {
    /// Creates an empty loan set.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rv_borrow_check::LoanSet;
    ///
    /// let loans = LoanSet::new();
    /// assert!(loans.is_empty());
    /// ```
    #[must_use]
    pub fn new() -> Self {
        Self { loans: Vec::new() }
    }

    /// Checks if a new loan would conflict with existing loans.
    ///
    /// Returns the first conflicting loan if one exists, or `None` if the
    /// new loan is compatible with all existing loans.
    ///
    /// # Conflict Rules
    ///
    /// - Shared + Shared = OK
    /// - Shared + Mutable = Conflict
    /// - Mutable + Shared = Conflict
    /// - Mutable + Mutable = Conflict
    /// - Any + Move = Conflict
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rv_borrow_check::{LoanSet, Loan, BorrowKind};
    /// use rv_mir::{Place, LocalId};
    /// use rv_lifetime::RegionId;
    /// use rv_span::{FileId, FileSpan, Span};
    ///
    /// let mut loans = LoanSet::new();
    /// let span = FileSpan::new(FileId(0), Span::new(0, 0));
    /// let loan1 = Loan::new(
    ///     Place::from_local(LocalId(0)),
    ///     BorrowKind::Shared,
    ///     RegionId(0),
    ///     span,
    /// );
    /// loans.add_loan(loan1.clone());
    ///
    /// let loan2 = Loan::new(
    ///     Place::from_local(LocalId(0)),
    ///     BorrowKind::Mutable,
    ///     RegionId(1),
    ///     span,
    /// );
    /// // This would conflict
    /// assert!(loans.check_loan(&loan2).is_some());
    /// ```
    #[must_use]
    pub fn check_loan(&self, new_loan: &Loan) -> Option<&Loan> {
        for existing in &self.loans {
            if places_overlap(&existing.place, &new_loan.place) {
                // Check for conflicts based on borrow kinds
                let conflicts = match (existing.kind, new_loan.kind) {
                    // Shared + Shared is always OK
                    (BorrowKind::Shared, BorrowKind::Shared) => false,

                    // Any other combination conflicts
                    _ => true,
                };

                if conflicts {
                    return Some(existing);
                }
            }
        }
        None
    }

    /// Adds a loan to the active set.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rv_borrow_check::{LoanSet, Loan, BorrowKind};
    /// use rv_mir::{Place, LocalId};
    /// use rv_lifetime::RegionId;
    /// use rv_span::{FileId, FileSpan, Span};
    ///
    /// let mut loans = LoanSet::new();
    /// let span = FileSpan::new(FileId(0), Span::new(0, 0));
    /// let loan = Loan::new(
    ///     Place::from_local(LocalId(0)),
    ///     BorrowKind::Shared,
    ///     RegionId(0),
    ///     span,
    /// );
    /// loans.add_loan(loan);
    /// ```
    pub fn add_loan(&mut self, loan: Loan) {
        self.loans.push(loan);
    }

    /// Removes all loans from the specified region.
    ///
    /// This is called when a region (lifetime scope) ends, making all borrows
    /// in that region invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rv_borrow_check::{LoanSet, Loan, BorrowKind};
    /// use rv_mir::{Place, LocalId};
    /// use rv_lifetime::RegionId;
    /// use rv_span::{FileId, FileSpan, Span};
    ///
    /// let mut loans = LoanSet::new();
    /// let span = FileSpan::new(FileId(0), Span::new(0, 0));
    /// let loan = Loan::new(
    ///     Place::from_local(LocalId(0)),
    ///     BorrowKind::Shared,
    ///     RegionId(0),
    ///     span,
    /// );
    /// loans.add_loan(loan);
    /// loans.end_region(RegionId(0));
    /// assert!(loans.is_empty());
    /// ```
    pub fn end_region(&mut self, region: RegionId) {
        self.loans.retain(|loan| loan.region != region);
    }

    /// Returns all active loans.
    #[must_use]
    pub fn loans(&self) -> &[Loan] {
        &self.loans
    }

    /// Returns the number of active loans.
    #[must_use]
    pub fn len(&self) -> usize {
        self.loans.len()
    }

    /// Returns `true` if there are no active loans.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.loans.is_empty()
    }
}

impl Default for LoanSet {
    fn default() -> Self {
        Self::new()
    }
}

/// Checks if two places overlap in memory.
///
/// Places overlap if they refer to the same base local and have compatible
/// projections. For example, `x` and `x.field` overlap, as do `x.field` and
/// `x.field`.
///
/// # Examples
///
/// ```rust
/// use rv_mir::{Place, LocalId, PlaceElem};
///
/// let place1 = Place::from_local(LocalId(0));
/// let mut place2 = Place::from_local(LocalId(0));
/// place2.projection.push(PlaceElem::Field { field_idx: 0 });
///
/// // x and x.field overlap
/// ```
#[must_use]
pub fn places_overlap(place1: &Place, place2: &Place) -> bool {
    // Different locals never overlap
    if place1.local != place2.local {
        return false;
    }

    // Same local - check if projections overlap
    // Places overlap if one is a prefix of the other
    let min_len = place1.projection.len().min(place2.projection.len());

    // Compare the common prefix
    for idx in 0..min_len {
        // For our purposes, we use a simplified check
        // A full implementation would need to handle all projection types
        match (&place1.projection[idx], &place2.projection[idx]) {
            (rv_mir::PlaceElem::Field { field_idx: f1 }, rv_mir::PlaceElem::Field { field_idx: f2 }) => {
                if f1 != f2 {
                    return false;
                }
            }
            (rv_mir::PlaceElem::Index(i1), rv_mir::PlaceElem::Index(i2)) => {
                // Conservative: assume indices might alias
                // A full implementation would need to prove they don't
                if i1 != i2 {
                    // Might overlap, be conservative
                    return true;
                }
            }
            (rv_mir::PlaceElem::Deref, rv_mir::PlaceElem::Deref) => {
                // Derefs match, continue checking
            }
            _ => {
                // Different projection kinds at same level don't match
                return false;
            }
        }
    }

    // If we got here, one projection is a prefix of the other, so they overlap
    true
}
