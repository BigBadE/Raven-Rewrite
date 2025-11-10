//! Borrow checker for the Raven compiler.
//!
//! This crate implements memory safety analysis through borrow checking,
//! ensuring that references do not outlive the data they point to and that
//! mutable and immutable borrows follow Rust's aliasing rules.
//!
//! # Architecture
//!
//! - [`BorrowChecker`]: Main borrow checking analysis
//! - [`LoanSet`]: Tracks active loans (borrows) at each program point
//! - [`Loan`]: Represents a single borrow with its kind and region
//! - [`BorrowKind`]: Classifies borrows (shared, mutable, move)
//!
//! # Borrow Rules
//!
//! The borrow checker enforces these fundamental rules:
//! 1. You can have either one mutable reference OR any number of immutable references
//! 2. References must not outlive the data they refer to
//! 3. Moved values cannot be used after the move
//!
//! # Limitations
//!
//! This is a simplified implementation:
//! - No flow-sensitive analysis (Polonius)
//! - Simplified move checking
//! - Basic place overlap detection
//!
//! # Examples
//!
//! ```rust
//! use rv_borrow_check::BorrowChecker;
//! use rv_mir::MirFunction;
//!
//! // Check a MIR function for borrow errors
//! let mir = MirFunction { /* ... */ };
//! let result = BorrowChecker::check(&mir);
//! ```

mod checker;
mod error;
mod loans;

pub use checker::BorrowChecker;
pub use error::{BorrowError, BorrowResult};
pub use loans::{BorrowKind, Loan, LoanSet};
