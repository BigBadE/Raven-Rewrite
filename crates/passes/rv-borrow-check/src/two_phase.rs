//! Two-phase borrow support
//!
//! Two-phase borrows allow mutable borrows to be "reserved" before they're
//! activated. This enables patterns like:
//!
//! ```rust,ignore
//! vec.push(vec.len());  // Reserve mutable borrow, read vec.len(), then activate
//! ```
//!
//! Without two-phase borrows, the above would fail because `vec.len()` would
//! create a shared borrow while a mutable borrow is active.
//!
//! # Phases
//!
//! 1. **Reservation**: The mutable borrow is created but not yet "active"
//! 2. **Activation**: The borrow becomes fully active (after all shared borrows end)
//!
//! During the reservation phase, shared borrows are still allowed.

use rv_mir::Place;
use rv_span::FileSpan;
use std::collections::HashMap;

/// Tracks the phase of a two-phase borrow
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BorrowPhase {
    /// Borrow is reserved but not yet active (shared borrows still allowed)
    Reserved,
    /// Borrow is fully active (no other borrows allowed)
    Active,
}

/// A two-phase borrow
#[derive(Debug, Clone)]
pub struct TwoPhaseBorrow {
    /// The place being borrowed
    pub place: Place,
    /// Current phase
    pub phase: BorrowPhase,
    /// Span where reservation occurred
    pub reservation_span: FileSpan,
    /// Span where activation occurred (if activated)
    pub activation_span: Option<FileSpan>,
}

/// Context for tracking two-phase borrows
#[derive(Debug, Default)]
pub struct TwoPhaseContext {
    /// Map from borrow ID to two-phase borrow info
    borrows: HashMap<TwoPhaseBorrowId, TwoPhaseBorrow>,
    /// Next available borrow ID
    next_id: u32,
}

/// Unique identifier for a two-phase borrow
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TwoPhaseBorrowId(pub u32);

impl TwoPhaseContext {
    /// Create a new two-phase borrow context
    pub fn new() -> Self {
        Self::default()
    }

    /// Reserve a new two-phase borrow
    pub fn reserve(&mut self, place: Place, span: FileSpan) -> TwoPhaseBorrowId {
        let id = TwoPhaseBorrowId(self.next_id);
        self.next_id += 1;

        self.borrows.insert(
            id,
            TwoPhaseBorrow {
                place,
                phase: BorrowPhase::Reserved,
                reservation_span: span,
                activation_span: None,
            },
        );

        id
    }

    /// Activate a reserved borrow
    pub fn activate(&mut self, id: TwoPhaseBorrowId, span: FileSpan) {
        if let Some(borrow) = self.borrows.get_mut(&id) {
            borrow.phase = BorrowPhase::Active;
            borrow.activation_span = Some(span);
        }
    }

    /// Check if a borrow is in the reserved phase
    pub fn is_reserved(&self, id: TwoPhaseBorrowId) -> bool {
        self.borrows
            .get(&id)
            .map_or(false, |b| b.phase == BorrowPhase::Reserved)
    }

    /// Check if a borrow is active
    pub fn is_active(&self, id: TwoPhaseBorrowId) -> bool {
        self.borrows
            .get(&id)
            .map_or(false, |b| b.phase == BorrowPhase::Active)
    }

    /// Get the place being borrowed
    pub fn get_place(&self, id: TwoPhaseBorrowId) -> Option<&Place> {
        self.borrows.get(&id).map(|b| &b.place)
    }

    /// End a two-phase borrow (remove from tracking)
    pub fn end_borrow(&mut self, id: TwoPhaseBorrowId) {
        self.borrows.remove(&id);
    }

    /// Get all reserved borrows for a given place
    pub fn get_reserved_for_place(&self, place: &Place) -> Vec<TwoPhaseBorrowId> {
        self.borrows
            .iter()
            .filter(|(_, b)| &b.place == place && b.phase == BorrowPhase::Reserved)
            .map(|(id, _)| *id)
            .collect()
    }
}
