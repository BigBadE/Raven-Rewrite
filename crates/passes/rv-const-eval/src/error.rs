//! Const evaluation errors

use rv_span::FileSpan;
use thiserror::Error;

/// Errors that can occur during const evaluation
#[derive(Debug, Clone, Error)]
pub enum ConstError {
    /// Expression is not a constant expression
    #[error("expression is not a constant expression")]
    NonConstExpr {
        /// Location of the non-const expression
        span: FileSpan,
    },

    /// Division by zero
    #[error("division by zero")]
    DivisionByZero {
        /// Location of the division operation
        span: FileSpan,
    },

    /// Integer overflow
    #[error("integer overflow in const evaluation")]
    OverflowError {
        /// Location of the overflow
        span: FileSpan,
    },

    /// Type mismatch in const operation
    #[error("type mismatch: expected {expected}, got {got}")]
    TypeMismatch {
        /// Expected type description
        expected: String,
        /// Got type description
        got: String,
        /// Location of the mismatch
        span: FileSpan,
    },

    /// Unsupported operation in const context
    #[error("unsupported operation in const context: {operation}")]
    UnsupportedOperation {
        /// Description of the unsupported operation
        operation: String,
        /// Location of the operation
        span: FileSpan,
    },

    /// Invalid binary operation on const values
    #[error("invalid binary operation: {left_type} {op} {right_type}")]
    InvalidBinaryOp {
        /// Left operand type
        left_type: String,
        /// Operator
        op: String,
        /// Right operand type
        right_type: String,
        /// Location of the operation
        span: FileSpan,
    },

    /// Invalid unary operation on const value
    #[error("invalid unary operation: {op} {operand_type}")]
    InvalidUnaryOp {
        /// Operator
        op: String,
        /// Operand type
        operand_type: String,
        /// Location of the operation
        span: FileSpan,
    },
}

impl ConstError {
    /// Returns the span where the error occurred
    #[must_use]
    pub fn span(&self) -> FileSpan {
        match self {
            Self::NonConstExpr { span }
            | Self::DivisionByZero { span }
            | Self::OverflowError { span }
            | Self::TypeMismatch { span, .. }
            | Self::UnsupportedOperation { span, .. }
            | Self::InvalidBinaryOp { span, .. }
            | Self::InvalidUnaryOp { span, .. } => *span,
        }
    }
}
