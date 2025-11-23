//! Main borrow checking implementation.

use rustc_hash::FxHashSet;
use rv_mir::{BasicBlock, MirFunction, Operand, Place, RValue, Statement, Terminator};
use rv_span::{FileId, FileSpan, Span};

use crate::{
    error::{BorrowError, BorrowResult},
    loans::{places_overlap, BorrowKind, Loan, LoanSet},
};

/// Creates a dummy file span for cases where span information is not available.
///
/// This is used for simplified borrow checking where some MIR nodes don't yet
/// have span information attached.
fn dummy_span() -> FileSpan {
    FileSpan::new(FileId(0), Span::new(0, 0))
}

/// Main borrow checker.
///
/// The borrow checker analyzes MIR functions to ensure memory safety by
/// enforcing Rust's borrowing rules. It tracks active loans (borrows) and
/// moved values through the control flow graph.
pub struct BorrowChecker<'mir> {
    /// The MIR function being checked
    function: &'mir MirFunction,

    /// Active loans at the current program point
    loans: LoanSet,

    /// Set of places that have been moved
    moved: FxHashSet<Place>,

    /// Accumulated errors
    errors: Vec<BorrowError>,
}

impl<'mir> BorrowChecker<'mir> {
    /// Creates a new borrow checker for the given function.
    #[must_use]
    pub fn new(function: &'mir MirFunction) -> Self {
        Self {
            function,
            loans: LoanSet::new(),
            moved: FxHashSet::default(),
            errors: Vec::new(),
        }
    }

    /// Runs borrow checking on a MIR function.
    ///
    /// This is the main entry point for borrow checking. It analyzes all
    /// basic blocks in the function's control flow graph.
    ///
    /// # Errors
    ///
    /// Returns all borrow checking errors found in the function. If no errors
    /// are found, returns `Ok(())`.
    ///
    /// # Examples
    ///
    /// ```rust,no_run
    /// use rv_borrow_check::BorrowChecker;
    /// use rv_mir::MirFunction;
    ///
    /// # let function = unimplemented!();
    /// let result = BorrowChecker::check(&function);
    /// ```
    pub fn check(function: &'mir MirFunction) -> BorrowResult<()> {
        let mut checker = Self::new(function);
        checker.check_function();

        if checker.errors.is_empty() {
            Ok(())
        } else {
            Err(checker.errors)
        }
    }

    /// Checks all basic blocks in the function.
    fn check_function(&mut self) {
        // Simple forward pass through basic blocks
        // A full implementation would use a dataflow analysis with fixpoint iteration
        for block in &self.function.basic_blocks {
            self.check_block(block);
        }
    }

    /// Checks a single basic block.
    fn check_block(&mut self, block: &BasicBlock) {
        // Check all statements in the block
        for stmt in &block.statements {
            self.check_statement(stmt);
        }

        // Check the terminator
        self.check_terminator(&block.terminator);
    }

    /// Checks a statement for borrow errors.
    fn check_statement(&mut self, stmt: &Statement) {
        match stmt {
            Statement::Assign { place, rvalue, span } => {
                // Check if we can write to this place
                self.check_write_access(place, *span);

                // Check the rvalue for borrows and moves
                self.check_rvalue(rvalue, *span);
            }

            Statement::StorageDead(local) => {
                // End all loans of this local
                // Simplified: we don't track regions properly yet
                let place = Place::from_local(*local);
                self.end_loans_for_place(&place);
            }

            Statement::StorageLive(_) | Statement::Nop => {
                // No borrow checking needed
            }
        }
    }

    /// Checks an rvalue for borrow and move operations.
    fn check_rvalue(&mut self, rvalue: &RValue, span: FileSpan) {
        match rvalue {
            RValue::Ref { place, mutable } => {
                // Check if the place has been moved
                if self.is_moved(place) {
                    self.errors.push(BorrowError::BorrowAfterMove {
                        place: place.clone(),
                        borrow_span: span,
                        move_span: span, // Simplified: would track actual move location
                    });
                    return;
                }

                // Create a loan for this borrow
                let kind = if *mutable {
                    BorrowKind::Mutable
                } else {
                    BorrowKind::Shared
                };

                let loan = Loan::new(
                    place.clone(),
                    kind,
                    rv_lifetime::RegionId(0), // Simplified: use dummy region
                    span,
                );

                // Check for conflicts with existing loans
                if let Some(existing) = self.loans.check_loan(&loan) {
                    self.errors.push(BorrowError::ConflictingBorrow {
                        new_borrow: loan,
                        existing_borrow: existing.clone(),
                    });
                } else {
                    self.loans.add_loan(loan);
                }
            }

            RValue::Use(operand) => {
                self.check_operand(operand, span);
            }

            RValue::BinaryOp { left, right, .. } => {
                self.check_operand(left, span);
                self.check_operand(right, span);
            }

            RValue::UnaryOp { operand, .. } => {
                self.check_operand(operand, span);
            }

            RValue::Call { args, .. } => {
                for arg in args {
                    self.check_operand(arg, span);
                }
            }

            RValue::Aggregate { operands, .. } => {
                for operand in operands {
                    self.check_operand(operand, span);
                }
            }
        }
    }

    /// Checks an operand for use-after-move errors.
    fn check_operand(&mut self, operand: &Operand, span: FileSpan) {
        match operand {
            Operand::Move(place) => {
                // Check if already moved
                if self.is_moved(place) {
                    self.errors.push(BorrowError::UseAfterMove {
                        place: place.clone(),
                        use_span: span,
                        move_span: span, // Simplified: would track actual move location
                    });
                } else {
                    // Check if borrowed
                    if let Some(loan) = self.find_overlapping_loan(place) {
                        self.errors.push(BorrowError::MoveWhileBorrowed {
                            place: place.clone(),
                            loan: loan.clone(),
                            move_span: span,
                        });
                    } else {
                        // Record the move
                        self.moved.insert(place.clone());
                    }
                }
            }

            Operand::Copy(place) => {
                // Check if moved
                if self.is_moved(place) {
                    self.errors.push(BorrowError::UseAfterMove {
                        place: place.clone(),
                        use_span: span,
                        move_span: span, // Simplified
                    });
                }
                // Copies are OK even if borrowed
            }

            Operand::Constant(_) => {
                // Constants are always OK
            }
        }
    }

    /// Checks if writing to a place is allowed.
    fn check_write_access(&mut self, place: &Place, span: FileSpan) {
        // Check if the place is borrowed
        for loan in self.loans.loans() {
            if places_overlap(&loan.place, place) {
                // Any active loan prevents writing
                self.errors.push(BorrowError::WriteWhileBorrowed {
                    place: place.clone(),
                    loan: loan.clone(),
                    write_span: span,
                });
                return;
            }
        }

        // Writing clears the moved state
        self.moved.remove(place);
    }

    /// Checks a terminator for borrow errors.
    fn check_terminator(&mut self, terminator: &Terminator) {
        match terminator {
            Terminator::Call { args, .. } => {
                // Check all arguments
                let span = dummy_span(); // Simplified: terminators don't have spans yet
                for arg in args {
                    self.check_operand(arg, span);
                }
            }

            Terminator::Return { value } => {
                if let Some(operand) = value {
                    let span = dummy_span();
                    self.check_operand(operand, span);
                }
            }

            Terminator::SwitchInt { discriminant, .. } => {
                let span = dummy_span();
                self.check_operand(discriminant, span);
            }

            Terminator::Goto(_) | Terminator::Unreachable => {
                // No borrow checking needed
            }
        }
    }

    /// Checks if a place has been moved.
    fn is_moved(&self, place: &Place) -> bool {
        // Check if this exact place or any prefix of it has been moved
        for moved_place in &self.moved {
            if places_overlap(moved_place, place) {
                return true;
            }
        }
        false
    }

    /// Finds a loan that overlaps with the given place.
    fn find_overlapping_loan(&self, place: &Place) -> Option<&Loan> {
        self.loans
            .loans()
            .iter()
            .find(|loan| places_overlap(&loan.place, place))
    }

    /// Ends all loans for a place and its projections.
    fn end_loans_for_place(&mut self, _place: &Place) {
        // Simplified: would need to filter loans properly
        // For now, this is a no-op
    }
}
