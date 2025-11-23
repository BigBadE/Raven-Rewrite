//! Const expression evaluator

use crate::{ConstError, ConstValue};
use rv_hir::{BinaryOp, Body, Expr, LiteralKind, UnaryOp};
use rv_span::FileSpan;
use std::collections::HashMap;

/// Const expression evaluator
///
/// Evaluates HIR expressions at compile-time to produce const values.
/// Used for array sizes, const generics, and const/static initializers.
#[derive(Debug)]
pub struct ConstEvaluator {
    /// Known const values (for const items)
    const_values: HashMap<String, ConstValue>,
}

impl ConstEvaluator {
    /// Creates a new const evaluator
    #[must_use]
    pub fn new() -> Self {
        Self {
            const_values: HashMap::new(),
        }
    }

    /// Registers a const value by name
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the const item
    /// * `value` - The const value
    pub fn register_const(&mut self, name: String, value: ConstValue) {
        self.const_values.insert(name, value);
    }

    /// Evaluates a HIR expression to a const value
    ///
    /// # Arguments
    ///
    /// * `expr` - The expression to evaluate
    /// * `body` - The body containing the expression
    ///
    /// # Errors
    ///
    /// Returns `ConstError` if:
    /// - The expression is not a constant expression
    /// - Division by zero occurs
    /// - Integer overflow occurs
    /// - Type mismatch in operations
    /// - Unsupported operation in const context
    pub fn eval_expr(&self, expr: &Expr, body: &Body) -> Result<ConstValue, ConstError> {
        match expr {
            Expr::Literal { kind, .. } => self.eval_literal(kind),

            Expr::BinaryOp {
                op,
                left,
                right,
                span,
            } => {
                let left_val = self.eval_expr(&body.exprs[*left], body)?;
                let right_val = self.eval_expr(&body.exprs[*right], body)?;
                self.eval_binary_op(*op, left_val, right_val, *span)
            }

            Expr::UnaryOp {
                op, operand, span, ..
            } => {
                let operand_val = self.eval_expr(&body.exprs[*operand], body)?;
                self.eval_unary_op(*op, operand_val, *span)
            }

            Expr::If {
                condition,
                then_branch,
                else_branch,
                span,
            } => {
                let cond_val = self.eval_expr(&body.exprs[*condition], body)?;

                let cond_bool = cond_val.as_bool().ok_or_else(|| ConstError::TypeMismatch {
                    expected: "bool".to_string(),
                    got: self.type_name(&cond_val),
                    span: *span,
                })?;

                if cond_bool {
                    self.eval_expr(&body.exprs[*then_branch], body)
                } else if let Some(else_expr) = else_branch {
                    self.eval_expr(&body.exprs[*else_expr], body)
                } else {
                    Ok(ConstValue::Unit)
                }
            }

            Expr::Block {
                statements,
                expr,
                span,
            } => {
                if !statements.is_empty() {
                    return Err(ConstError::UnsupportedOperation {
                        operation: "block with statements".to_string(),
                        span: *span,
                    });
                }

                if let Some(expr_id) = expr {
                    self.eval_expr(&body.exprs[*expr_id], body)
                } else {
                    Ok(ConstValue::Unit)
                }
            }

            Expr::Variable { span, .. }
            | Expr::Call { span, .. }
            | Expr::Match { span, .. }
            | Expr::Field { span, .. }
            | Expr::MethodCall { span, .. }
            | Expr::StructConstruct { span, .. }
            | Expr::EnumVariant { span, .. }
            | Expr::Closure { span, .. } => Err(ConstError::NonConstExpr { span: *span }),
        }
    }

    /// Evaluates a literal to a const value
    fn eval_literal(&self, kind: &LiteralKind) -> Result<ConstValue, ConstError> {
        Ok(match kind {
            LiteralKind::Integer(value) => ConstValue::Int(*value),
            LiteralKind::Float(value) => ConstValue::Float(*value),
            LiteralKind::String(value) => ConstValue::String(value.clone()),
            LiteralKind::Bool(value) => ConstValue::Bool(*value),
            LiteralKind::Unit => ConstValue::Unit,
        })
    }

    /// Evaluates a binary operation
    #[allow(clippy::too_many_lines, reason = "Comprehensive operator handling required")]
    fn eval_binary_op(
        &self,
        op: BinaryOp,
        left: ConstValue,
        right: ConstValue,
        span: FileSpan,
    ) -> Result<ConstValue, ConstError> {
        match (op, &left, &right) {
            // Integer arithmetic
            (BinaryOp::Add, ConstValue::Int(left_val), ConstValue::Int(right_val)) => {
                left_val.checked_add(*right_val).map_or_else(
                    || Err(ConstError::OverflowError { span }),
                    |result| Ok(ConstValue::Int(result)),
                )
            }
            (BinaryOp::Sub, ConstValue::Int(left_val), ConstValue::Int(right_val)) => {
                left_val.checked_sub(*right_val).map_or_else(
                    || Err(ConstError::OverflowError { span }),
                    |result| Ok(ConstValue::Int(result)),
                )
            }
            (BinaryOp::Mul, ConstValue::Int(left_val), ConstValue::Int(right_val)) => {
                left_val.checked_mul(*right_val).map_or_else(
                    || Err(ConstError::OverflowError { span }),
                    |result| Ok(ConstValue::Int(result)),
                )
            }
            (BinaryOp::Div, ConstValue::Int(left_val), ConstValue::Int(right_val)) => {
                if *right_val == 0 {
                    Err(ConstError::DivisionByZero { span })
                } else {
                    left_val.checked_div(*right_val).map_or_else(
                        || Err(ConstError::OverflowError { span }),
                        |result| Ok(ConstValue::Int(result)),
                    )
                }
            }
            (BinaryOp::Mod, ConstValue::Int(left_val), ConstValue::Int(right_val)) => {
                if *right_val == 0 {
                    Err(ConstError::DivisionByZero { span })
                } else {
                    left_val.checked_rem(*right_val).map_or_else(
                        || Err(ConstError::OverflowError { span }),
                        |result| Ok(ConstValue::Int(result)),
                    )
                }
            }

            // Float arithmetic
            (BinaryOp::Add, ConstValue::Float(left_val), ConstValue::Float(right_val)) => {
                Ok(ConstValue::Float(left_val + right_val))
            }
            (BinaryOp::Sub, ConstValue::Float(left_val), ConstValue::Float(right_val)) => {
                Ok(ConstValue::Float(left_val - right_val))
            }
            (BinaryOp::Mul, ConstValue::Float(left_val), ConstValue::Float(right_val)) => {
                Ok(ConstValue::Float(left_val * right_val))
            }
            (BinaryOp::Div, ConstValue::Float(left_val), ConstValue::Float(right_val)) => {
                if *right_val == 0.0 {
                    Err(ConstError::DivisionByZero { span })
                } else {
                    Ok(ConstValue::Float(left_val / right_val))
                }
            }

            // Integer comparisons
            (BinaryOp::Eq, ConstValue::Int(left_val), ConstValue::Int(right_val)) => {
                Ok(ConstValue::Bool(left_val == right_val))
            }
            (BinaryOp::Ne, ConstValue::Int(left_val), ConstValue::Int(right_val)) => {
                Ok(ConstValue::Bool(left_val != right_val))
            }
            (BinaryOp::Lt, ConstValue::Int(left_val), ConstValue::Int(right_val)) => {
                Ok(ConstValue::Bool(left_val < right_val))
            }
            (BinaryOp::Le, ConstValue::Int(left_val), ConstValue::Int(right_val)) => {
                Ok(ConstValue::Bool(left_val <= right_val))
            }
            (BinaryOp::Gt, ConstValue::Int(left_val), ConstValue::Int(right_val)) => {
                Ok(ConstValue::Bool(left_val > right_val))
            }
            (BinaryOp::Ge, ConstValue::Int(left_val), ConstValue::Int(right_val)) => {
                Ok(ConstValue::Bool(left_val >= right_val))
            }

            // Float comparisons
            (BinaryOp::Eq, ConstValue::Float(left_val), ConstValue::Float(right_val)) => {
                Ok(ConstValue::Bool((left_val - right_val).abs() < f64::EPSILON))
            }
            (BinaryOp::Ne, ConstValue::Float(left_val), ConstValue::Float(right_val)) => {
                Ok(ConstValue::Bool((left_val - right_val).abs() >= f64::EPSILON))
            }
            (BinaryOp::Lt, ConstValue::Float(left_val), ConstValue::Float(right_val)) => {
                Ok(ConstValue::Bool(left_val < right_val))
            }
            (BinaryOp::Le, ConstValue::Float(left_val), ConstValue::Float(right_val)) => {
                Ok(ConstValue::Bool(left_val <= right_val))
            }
            (BinaryOp::Gt, ConstValue::Float(left_val), ConstValue::Float(right_val)) => {
                Ok(ConstValue::Bool(left_val > right_val))
            }
            (BinaryOp::Ge, ConstValue::Float(left_val), ConstValue::Float(right_val)) => {
                Ok(ConstValue::Bool(left_val >= right_val))
            }

            // Boolean comparisons
            (BinaryOp::Eq, ConstValue::Bool(left_val), ConstValue::Bool(right_val)) => {
                Ok(ConstValue::Bool(left_val == right_val))
            }
            (BinaryOp::Ne, ConstValue::Bool(left_val), ConstValue::Bool(right_val)) => {
                Ok(ConstValue::Bool(left_val != right_val))
            }

            // Logical operations
            (BinaryOp::And, ConstValue::Bool(left_val), ConstValue::Bool(right_val)) => {
                Ok(ConstValue::Bool(*left_val && *right_val))
            }
            (BinaryOp::Or, ConstValue::Bool(left_val), ConstValue::Bool(right_val)) => {
                Ok(ConstValue::Bool(*left_val || *right_val))
            }

            // Bitwise operations on integers
            (BinaryOp::BitAnd, ConstValue::Int(left_val), ConstValue::Int(right_val)) => {
                Ok(ConstValue::Int(left_val & right_val))
            }
            (BinaryOp::BitOr, ConstValue::Int(left_val), ConstValue::Int(right_val)) => {
                Ok(ConstValue::Int(left_val | right_val))
            }
            (BinaryOp::BitXor, ConstValue::Int(left_val), ConstValue::Int(right_val)) => {
                Ok(ConstValue::Int(left_val ^ right_val))
            }
            (BinaryOp::Shl, ConstValue::Int(left_val), ConstValue::Int(right_val)) => {
                if *right_val < 0 || *right_val >= 64 {
                    Err(ConstError::OverflowError { span })
                } else {
                    left_val.checked_shl(u32::try_from(*right_val).map_err(|_| {
                        ConstError::OverflowError { span }
                    })?).map_or_else(
                        || Err(ConstError::OverflowError { span }),
                        |result| Ok(ConstValue::Int(result)),
                    )
                }
            }
            (BinaryOp::Shr, ConstValue::Int(left_val), ConstValue::Int(right_val)) => {
                if *right_val < 0 || *right_val >= 64 {
                    Err(ConstError::OverflowError { span })
                } else {
                    left_val.checked_shr(u32::try_from(*right_val).map_err(|_| {
                        ConstError::OverflowError { span }
                    })?).map_or_else(
                        || Err(ConstError::OverflowError { span }),
                        |result| Ok(ConstValue::Int(result)),
                    )
                }
            }

            // Invalid operations
            _ => Err(ConstError::InvalidBinaryOp {
                left_type: self.type_name(&left),
                op: format!("{op:?}"),
                right_type: self.type_name(&right),
                span,
            }),
        }
    }

    /// Evaluates a unary operation
    fn eval_unary_op(
        &self,
        op: UnaryOp,
        operand: ConstValue,
        span: FileSpan,
    ) -> Result<ConstValue, ConstError> {
        match (op, &operand) {
            // Integer negation
            (UnaryOp::Neg, ConstValue::Int(value)) => {
                value.checked_neg().map_or_else(
                    || Err(ConstError::OverflowError { span }),
                    |result| Ok(ConstValue::Int(result)),
                )
            }

            // Float negation
            (UnaryOp::Neg, ConstValue::Float(value)) => Ok(ConstValue::Float(-value)),

            // Logical NOT
            (UnaryOp::Not, ConstValue::Bool(value)) => Ok(ConstValue::Bool(!value)),

            // Bitwise NOT
            (UnaryOp::BitNot, ConstValue::Int(value)) => Ok(ConstValue::Int(!value)),

            // References and dereferencing are not const operations
            (UnaryOp::Ref | UnaryOp::RefMut | UnaryOp::Deref, _) => {
                Err(ConstError::UnsupportedOperation {
                    operation: format!("{op:?}"),
                    span,
                })
            }

            // Invalid operations
            _ => Err(ConstError::InvalidUnaryOp {
                op: format!("{op:?}"),
                operand_type: self.type_name(&operand),
                span,
            }),
        }
    }

    /// Returns a human-readable type name for a const value
    fn type_name(&self, value: &ConstValue) -> String {
        match value {
            ConstValue::Int(_) => "i64".to_string(),
            ConstValue::Float(_) => "f64".to_string(),
            ConstValue::Bool(_) => "bool".to_string(),
            ConstValue::String(_) => "String".to_string(),
            ConstValue::Unit => "()".to_string(),
            ConstValue::Tuple(_) => "tuple".to_string(),
            ConstValue::Struct { .. } => "struct".to_string(),
            ConstValue::Array(_) => "array".to_string(),
        }
    }
}

impl Default for ConstEvaluator {
    fn default() -> Self {
        Self::new()
    }
}
