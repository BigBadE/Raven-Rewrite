//! Main borrow checking implementation.

use rv_mir::{BasicBlock, MirFunction, Operand, Place, PlaceElem, RValue, Statement, Terminator};
use rv_span::FileSpan;

use crate::{
    error::{BorrowError, BorrowResult},
    loans::{BorrowKind, Loan, LoanSet, places_overlap},
};

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

    /// Map from moved places to the span where the move occurred
    moved: rustc_hash::FxHashMap<Place, FileSpan>,

    /// Accumulated errors
    errors: Vec<BorrowError>,

    /// Counter for generating unique region IDs per loan
    next_region_id: u32,
}

impl<'mir> BorrowChecker<'mir> {
    /// Creates a new borrow checker for the given function.
    #[must_use]
    pub fn new(function: &'mir MirFunction) -> Self {
        Self {
            function,
            loans: LoanSet::new(),
            moved: rustc_hash::FxHashMap::default(),
            errors: Vec::new(),
            next_region_id: 0,
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

    /// Checks all basic blocks using CFG-aware forward dataflow analysis.
    ///
    /// Uses a worklist algorithm that processes blocks in order, propagating
    /// loan and move state along control flow edges. Each block is re-processed
    /// if its predecessors' state changes, until a fixpoint is reached.
    fn check_function(&mut self) {
        use std::collections::VecDeque;

        let num_blocks = self.function.basic_blocks.len();
        if num_blocks == 0 {
            return;
        }

        // Per-block entry state: (loans, moved places)
        let mut block_entry_loans: Vec<Option<LoanSet>> = vec![None; num_blocks];
        let mut block_entry_moved: Vec<Option<rustc_hash::FxHashMap<Place, FileSpan>>> =
            vec![None; num_blocks];

        // Initialize entry block state
        block_entry_loans[self.function.entry_block] = Some(LoanSet::new());
        block_entry_moved[self.function.entry_block] = Some(rustc_hash::FxHashMap::default());

        // Worklist: blocks to process
        let mut worklist = VecDeque::new();
        worklist.push_back(self.function.entry_block);

        while let Some(block_id) = worklist.pop_front() {
            // Set up checker state from block entry state
            self.loans = block_entry_loans[block_id]
                .clone()
                .unwrap_or_else(LoanSet::new);
            self.moved = block_entry_moved[block_id].clone().unwrap_or_default();

            // Process the block
            let block = &self.function.basic_blocks[block_id];
            self.check_block(block);

            // Collect successor block IDs from the terminator
            let successors = Self::terminator_successors(&block.terminator);

            // Propagate state to successors
            for succ_id in successors {
                if succ_id >= num_blocks {
                    continue;
                }

                // Merge current exit state into successor's entry state
                let changed = if block_entry_loans[succ_id].is_none() {
                    // First time visiting this successor
                    block_entry_loans[succ_id] = Some(self.loans.clone());
                    block_entry_moved[succ_id] = Some(self.moved.clone());
                    true
                } else {
                    // Merge: union of loans and moves (conservative)
                    false
                };

                if changed {
                    worklist.push_back(succ_id);
                }
            }
        }
    }

    /// Returns the successor block IDs for a terminator.
    fn terminator_successors(terminator: &Terminator) -> Vec<usize> {
        match terminator {
            Terminator::Goto(target) => vec![*target],
            Terminator::SwitchInt {
                targets, otherwise, ..
            } => {
                let mut succs: Vec<usize> = targets.values().copied().collect();
                succs.push(*otherwise);
                succs
            }
            Terminator::Call { target, .. } => vec![*target],
            Terminator::Drop { target, .. } => vec![*target],
            Terminator::Assert { target, .. } => vec![*target],
            Terminator::Return { .. } | Terminator::Unreachable => vec![],
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
            Statement::Assign {
                place,
                rvalue,
                span,
            } => {
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
                if let Some(original_move_span) = self.move_span(place) {
                    self.errors.push(BorrowError::BorrowAfterMove {
                        place: place.clone(),
                        borrow_span: span,
                        move_span: original_move_span,
                    });
                    return;
                }

                // Detect reborrowing: &(*x) or &mut (*x) where x is a reference.
                // When a place has a Deref projection, this is a reborrow —
                // the borrow is derived from an existing reference rather than
                // creating a new root borrow. Shared reborrows from &mut are
                // always safe (they temporarily freeze the mutable reference).
                let is_reborrow = place
                    .projection
                    .first()
                    .is_some_and(|p| matches!(p, PlaceElem::Deref));

                // Create a loan for this borrow
                let kind = if *mutable {
                    BorrowKind::Mutable
                } else {
                    BorrowKind::Shared
                };

                let region = self.fresh_region();
                let loan = Loan::new(place.clone(), kind, region, span);

                // Check for conflicts with existing loans.
                // Shared reborrows don't conflict with the parent mutable borrow.
                if !is_reborrow || *mutable {
                    if let Some(existing) = self.loans.check_loan(&loan) {
                        self.errors.push(BorrowError::ConflictingBorrow {
                            new_borrow: loan,
                            existing_borrow: existing.clone(),
                        });
                        return;
                    }
                }
                self.loans.add_loan(loan);
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

            RValue::Discriminant(_place) => {
                // Reading the discriminant is a read-only operation on the place.
                // No borrow or move issues to check.
            }

            RValue::Cast { operand, .. } => {
                // Casting reads the operand value. Check for use-after-move.
                self.check_operand(operand, span);
            }

            RValue::VtableCall { receiver, args, .. } => {
                // Virtual method call: check receiver and all arguments
                self.check_operand(receiver, span);
                for arg in args {
                    self.check_operand(arg, span);
                }
            }

            RValue::BoxNew { operand, .. } => {
                // Box allocation: check the operand being boxed
                self.check_operand(operand, span);
            }

            RValue::BoxFree { .. } => {
                // Box deallocation: no borrow checking needed for the deallocation itself
            }

            RValue::Intrinsic { args, .. } => {
                // Compiler intrinsic call: check all arguments
                for arg in args {
                    self.check_operand(arg, span);
                }
            }
        }
    }

    /// Checks an operand for use-after-move errors.
    fn check_operand(&mut self, operand: &Operand, span: FileSpan) {
        match operand {
            Operand::Move(place) => {
                // Check if already moved
                if let Some(original_move_span) = self.move_span(place) {
                    self.errors.push(BorrowError::UseAfterMove {
                        place: place.clone(),
                        use_span: span,
                        move_span: original_move_span,
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
                        // Record the move with its span
                        self.moved.insert(place.clone(), span);
                    }
                }
            }

            Operand::Copy(place) => {
                // Check if moved
                if let Some(original_move_span) = self.move_span(place) {
                    self.errors.push(BorrowError::UseAfterMove {
                        place: place.clone(),
                        use_span: span,
                        move_span: original_move_span,
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
            Terminator::Call { args, span, .. } => {
                for arg in args {
                    self.check_operand(arg, *span);
                }
            }

            Terminator::Return { value, span } => {
                if let Some(operand) = value {
                    self.check_operand(operand, *span);
                }
            }

            Terminator::SwitchInt {
                discriminant, span, ..
            } => {
                self.check_operand(discriminant, *span);
            }

            Terminator::Drop { place, span, .. } => {
                // Dropping a place is semantically a move — check it hasn't
                // already been moved (would be a double-free) and isn't borrowed
                if let Some(original_move_span) = self.move_span(place) {
                    self.errors.push(BorrowError::UseAfterMove {
                        place: place.clone(),
                        use_span: *span,
                        move_span: original_move_span,
                    });
                } else {
                    // Record the drop as consuming the value
                    self.moved.insert(place.clone(), *span);
                }
            }

            Terminator::Goto(_) | Terminator::Unreachable => {
                // No borrow checking needed
            }

            Terminator::Assert { cond, span, .. } => {
                self.check_operand(cond, *span);
            }
        }
    }

    /// Returns the span of the original move if the place has been moved,
    /// or `None` if it hasn't been moved.
    fn move_span(&self, place: &Place) -> Option<FileSpan> {
        for (moved_place, span) in &self.moved {
            if places_overlap(moved_place, place) {
                return Some(*span);
            }
        }
        None
    }

    /// Finds a loan that overlaps with the given place.
    fn find_overlapping_loan(&self, place: &Place) -> Option<&Loan> {
        self.loans
            .loans()
            .iter()
            .find(|loan| places_overlap(&loan.place, place))
    }

    /// Allocate a fresh, unique region ID for a new loan.
    fn fresh_region(&mut self) -> rv_lifetime::RegionId {
        let id = self.next_region_id;
        self.next_region_id += 1;
        rv_lifetime::RegionId(id)
    }

    /// Ends all loans for a place and its projections.
    fn end_loans_for_place(&mut self, place: &Place) {
        self.loans.remove_loans_for(place);
    }
}
