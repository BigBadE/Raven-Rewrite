//! Compile-time constant evaluation
//!
//! This crate provides compile-time evaluation of constant expressions.
//! Used for:
//! - Array sizes: `[T; N]` where N is a const expression
//! - Const generic parameters
//! - Const item initializers: `const FOO: i64 = expr;`
//! - Static initializers: `static BAR: i64 = expr;`

mod error;
mod evaluator;
mod value;

pub use error::ConstError;
pub use evaluator::ConstEvaluator;
pub use value::ConstValue;
