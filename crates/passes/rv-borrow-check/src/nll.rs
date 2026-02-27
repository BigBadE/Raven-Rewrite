//! Non-Lexical Lifetimes (NLL) support
//!
//! This module implements flow-sensitive region inference for more precise
//! borrow checking. Unlike lexical lifetimes (which end at the end of a scope),
//! NLL allows borrows to end at their last use, enabling more code to compile.
//!
//! # Example
//!
//! ```rust
//! let mut x = 5;
//! let y = &x;      // Borrow starts
//! println!("{}", y); // Last use of y — borrow can end here
//! x = 6;           // OK! Borrow ended at last use, not at scope end
//! ```
//!
//! # Implementation
//!
//! NLL tracks:
//! - Borrow lifetimes as regions in the CFG
//! - Last use points for each borrow
//! - Flow-sensitive loan expiration

use rv_mir::{BasicBlockId, Place};
use rv_span::FileSpan;
use std::collections::{HashMap, HashSet};

/// Region ID for tracking borrow lifetimes
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RegionId(pub u32);

/// Tracks the lifetime of a loan through the control flow graph
#[derive(Debug, Clone)]
pub struct LoanLifetime {
    /// The region this loan belongs to
    pub region: RegionId,
    /// The place being borrowed
    pub place: Place,
    /// Basic blocks where this loan is live
    pub live_blocks: HashSet<BasicBlockId>,
    /// Span where the borrow was created
    pub origin: FileSpan,
}

/// NLL context for tracking regions and loan lifetimes
#[derive(Debug, Default)]
pub struct NllContext {
    /// Map from region ID to loan lifetime info
    lifetimes: HashMap<RegionId, LoanLifetime>,
    /// Next available region ID
    next_region: u32,
    /// Map from places to their active regions per block
    active_regions: HashMap<BasicBlockId, HashMap<Place, Vec<RegionId>>>,
}

impl NllContext {
    /// Create a new NLL context
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocate a fresh region ID
    pub fn fresh_region(&mut self) -> RegionId {
        let id = RegionId(self.next_region);
        self.next_region += 1;
        id
    }

    /// Record a new loan with its region
    pub fn record_loan(&mut self, region: RegionId, place: Place, origin: FileSpan) {
        self.lifetimes.insert(
            region,
            LoanLifetime {
                region,
                place,
                live_blocks: HashSet::new(),
                origin,
            },
        );
    }

    /// Mark a region as live in a basic block
    pub fn mark_live(&mut self, region: RegionId, block: BasicBlockId) {
        if let Some(lifetime) = self.lifetimes.get_mut(&region) {
            lifetime.live_blocks.insert(block);
        }
    }

    /// Check if a region is live in a given block
    pub fn is_live(&self, region: RegionId, block: BasicBlockId) -> bool {
        self.lifetimes
            .get(&region)
            .map_or(false, |lt| lt.live_blocks.contains(&block))
    }

    /// Get all active regions for a place in a block
    pub fn get_active_regions(&self, place: &Place, block: BasicBlockId) -> Vec<RegionId> {
        self.active_regions
            .get(&block)
            .and_then(|map| map.get(place))
            .cloned()
            .unwrap_or_default()
    }

    /// Add an active region for a place in a block
    pub fn add_active_region(&mut self, place: Place, block: BasicBlockId, region: RegionId) {
        self.active_regions
            .entry(block)
            .or_default()
            .entry(place)
            .or_default()
            .push(region);
    }

    /// Remove an active region for a place in a block (on last use)
    pub fn remove_active_region(&mut self, place: &Place, block: BasicBlockId, region: RegionId) {
        if let Some(block_regions) = self.active_regions.get_mut(&block) {
            if let Some(regions) = block_regions.get_mut(place) {
                regions.retain(|r| *r != region);
            }
        }
    }
}
