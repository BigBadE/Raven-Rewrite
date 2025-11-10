//! Code metrics and complexity analysis
//!
//! Provides code quality metrics for HIR functions

use rv_hir::{Body, Expr, ExprId, Function, Stmt, StmtId};
use serde::{Deserialize, Serialize};

/// Metrics for a single function
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionMetrics {
    /// Function name
    pub name: String,

    /// Cyclomatic complexity
    pub cyclomatic_complexity: usize,

    /// Cognitive complexity
    pub cognitive_complexity: usize,

    /// Number of parameters
    pub parameter_count: usize,

    /// Maximum nesting depth
    pub max_nesting_depth: usize,
}

/// Calculates cyclomatic complexity
pub fn cyclomatic_complexity(body: &Body) -> usize {
    cyclomatic_complexity_expr(body, body.root_expr)
}

fn cyclomatic_complexity_expr(body: &Body, expr_id: ExprId) -> usize {
    let expr = &body.exprs[expr_id];
    let mut complexity = 1;

    match expr {
        Expr::If { condition, then_branch, else_branch, .. } => {
            complexity += 1;
            complexity += cyclomatic_complexity_expr(body, *condition);
            complexity += cyclomatic_complexity_expr(body, *then_branch);
            if let Some(else_id) = else_branch {
                complexity += cyclomatic_complexity_expr(body, *else_id);
            }
        }
        Expr::Match { scrutinee, arms, .. } => {
            complexity += arms.len().saturating_sub(1);
            complexity += cyclomatic_complexity_expr(body, *scrutinee);
            for arm in arms {
                complexity += cyclomatic_complexity_expr(body, arm.body);
            }
        }
        Expr::BinaryOp { op, left, right, .. } => {
            if matches!(op, rv_hir::BinaryOp::And | rv_hir::BinaryOp::Or) {
                complexity += 1;
            }
            complexity += cyclomatic_complexity_expr(body, *left);
            complexity += cyclomatic_complexity_expr(body, *right);
        }
        Expr::UnaryOp { operand, .. } => {
            complexity += cyclomatic_complexity_expr(body, *operand);
        }
        Expr::Block { statements, expr, .. } => {
            for stmt_id in statements {
                complexity += cyclomatic_complexity_stmt(body, *stmt_id);
            }
            if let Some(expr_id) = expr {
                complexity += cyclomatic_complexity_expr(body, *expr_id);
            }
        }
        Expr::Call { callee, args, .. } => {
            complexity += cyclomatic_complexity_expr(body, *callee);
            for arg_id in args {
                complexity += cyclomatic_complexity_expr(body, *arg_id);
            }
        }
        Expr::Field { base, .. } => {
            complexity += cyclomatic_complexity_expr(body, *base);
        }
        Expr::MethodCall { receiver, args, .. } => {
            complexity += cyclomatic_complexity_expr(body, *receiver);
            for arg_id in args {
                complexity += cyclomatic_complexity_expr(body, *arg_id);
            }
        }
        Expr::StructConstruct { fields, .. } => {
            for (_, field_expr) in fields {
                complexity += cyclomatic_complexity_expr(body, *field_expr);
            }
        }
        Expr::EnumVariant { fields, .. } => {
            for field_expr in fields {
                complexity += cyclomatic_complexity_expr(body, *field_expr);
            }
        }
        Expr::Closure { body: closure_body, .. } => {
            complexity += cyclomatic_complexity_expr(body, *closure_body);
        }
        Expr::Literal { .. } | Expr::Variable { .. } => {}
    }

    complexity
}

fn cyclomatic_complexity_stmt(body: &Body, stmt_id: StmtId) -> usize {
    let stmt = &body.stmts[stmt_id];
    match stmt {
        Stmt::Let { initializer, .. } => {
            initializer.map_or(0, |expr_id| cyclomatic_complexity_expr(body, expr_id))
        }
        Stmt::Expr { expr, .. } => cyclomatic_complexity_expr(body, *expr),
        Stmt::Return { value, .. } => value.map_or(0, |expr_id| cyclomatic_complexity_expr(body, expr_id)),
    }
}

/// Calculates cognitive complexity
pub fn cognitive_complexity(body: &Body) -> usize {
    cognitive_complexity_expr(body, body.root_expr, 0)
}

fn cognitive_complexity_expr(body: &Body, expr_id: ExprId, nesting: usize) -> usize {
    let expr = &body.exprs[expr_id];
    let mut complexity = 0;

    match expr {
        Expr::If { condition, then_branch, else_branch, .. } => {
            complexity += 1 + nesting;
            complexity += cognitive_complexity_expr(body, *condition, nesting);
            complexity += cognitive_complexity_expr(body, *then_branch, nesting + 1);
            if let Some(else_id) = else_branch {
                let else_expr = &body.exprs[*else_id];
                if matches!(else_expr, Expr::If { .. }) {
                    complexity += cognitive_complexity_expr(body, *else_id, nesting);
                } else {
                    complexity += cognitive_complexity_expr(body, *else_id, nesting + 1);
                }
            }
        }
        Expr::Match { scrutinee, arms, .. } => {
            complexity += 1 + nesting;
            complexity += cognitive_complexity_expr(body, *scrutinee, nesting);
            for arm in arms {
                complexity += cognitive_complexity_expr(body, arm.body, nesting + 1);
            }
        }
        Expr::BinaryOp { op, left, right, .. } => {
            if matches!(op, rv_hir::BinaryOp::And | rv_hir::BinaryOp::Or) {
                complexity += 1;
            }
            complexity += cognitive_complexity_expr(body, *left, nesting);
            complexity += cognitive_complexity_expr(body, *right, nesting);
        }
        Expr::UnaryOp { operand, .. } => {
            complexity += cognitive_complexity_expr(body, *operand, nesting);
        }
        Expr::Block { statements, expr, .. } => {
            for stmt_id in statements {
                complexity += cognitive_complexity_stmt(body, *stmt_id, nesting);
            }
            if let Some(expr_id) = expr {
                complexity += cognitive_complexity_expr(body, *expr_id, nesting);
            }
        }
        Expr::Call { callee, args, .. } => {
            complexity += cognitive_complexity_expr(body, *callee, nesting);
            for arg_id in args {
                complexity += cognitive_complexity_expr(body, *arg_id, nesting);
            }
        }
        Expr::Field { base, .. } => {
            complexity += cognitive_complexity_expr(body, *base, nesting);
        }
        Expr::MethodCall { receiver, args, .. } => {
            complexity += cognitive_complexity_expr(body, *receiver, nesting);
            for arg_id in args {
                complexity += cognitive_complexity_expr(body, *arg_id, nesting);
            }
        }
        Expr::StructConstruct { fields, .. } => {
            for (_, field_expr) in fields {
                complexity += cognitive_complexity_expr(body, *field_expr, nesting);
            }
        }
        Expr::EnumVariant { fields, .. } => {
            for field_expr in fields {
                complexity += cognitive_complexity_expr(body, *field_expr, nesting);
            }
        }
        Expr::Closure { body: closure_body, .. } => {
            complexity += cognitive_complexity_expr(body, *closure_body, nesting + 1);
        }
        Expr::Literal { .. } | Expr::Variable { .. } => {}
    }

    complexity
}

fn cognitive_complexity_stmt(body: &Body, stmt_id: StmtId, nesting: usize) -> usize {
    let stmt = &body.stmts[stmt_id];
    match stmt {
        Stmt::Let { initializer, .. } => {
            initializer.map_or(0, |expr_id| cognitive_complexity_expr(body, expr_id, nesting))
        }
        Stmt::Expr { expr, .. } => cognitive_complexity_expr(body, *expr, nesting),
        Stmt::Return { value, .. } => value.map_or(0, |expr_id| cognitive_complexity_expr(body, expr_id, nesting)),
    }
}

/// Calculates maximum nesting depth
pub fn max_nesting_depth(body: &Body) -> usize {
    max_nesting_depth_expr(body, body.root_expr, 0)
}

fn max_nesting_depth_expr(body: &Body, expr_id: ExprId, current_depth: usize) -> usize {
    let expr = &body.exprs[expr_id];
    let mut max_depth = current_depth;

    match expr {
        Expr::If { condition, then_branch, else_branch, .. } => {
            max_depth = max_depth.max(max_nesting_depth_expr(body, *condition, current_depth));
            max_depth = max_depth.max(max_nesting_depth_expr(body, *then_branch, current_depth + 1));
            if let Some(else_id) = else_branch {
                max_depth = max_depth.max(max_nesting_depth_expr(body, *else_id, current_depth + 1));
            }
        }
        Expr::Match { scrutinee, arms, .. } => {
            max_depth = max_depth.max(max_nesting_depth_expr(body, *scrutinee, current_depth));
            for arm in arms {
                max_depth = max_depth.max(max_nesting_depth_expr(body, arm.body, current_depth + 1));
            }
        }
        Expr::BinaryOp { left, right, .. } => {
            max_depth = max_depth.max(max_nesting_depth_expr(body, *left, current_depth));
            max_depth = max_depth.max(max_nesting_depth_expr(body, *right, current_depth));
        }
        Expr::UnaryOp { operand, .. } => {
            max_depth = max_depth.max(max_nesting_depth_expr(body, *operand, current_depth));
        }
        Expr::Block { statements, expr, .. } => {
            for stmt_id in statements {
                max_depth = max_depth.max(max_nesting_depth_stmt(body, *stmt_id, current_depth + 1));
            }
            if let Some(expr_id) = expr {
                max_depth = max_depth.max(max_nesting_depth_expr(body, *expr_id, current_depth + 1));
            }
        }
        Expr::Call { callee, args, .. } => {
            max_depth = max_depth.max(max_nesting_depth_expr(body, *callee, current_depth));
            for arg_id in args {
                max_depth = max_depth.max(max_nesting_depth_expr(body, *arg_id, current_depth));
            }
        }
        Expr::Field { base, .. } => {
            max_depth = max_depth.max(max_nesting_depth_expr(body, *base, current_depth));
        }
        Expr::MethodCall { receiver, args, .. } => {
            max_depth = max_depth.max(max_nesting_depth_expr(body, *receiver, current_depth));
            for arg_id in args {
                max_depth = max_depth.max(max_nesting_depth_expr(body, *arg_id, current_depth));
            }
        }
        Expr::StructConstruct { fields, .. } => {
            for (_, field_expr) in fields {
                max_depth = max_depth.max(max_nesting_depth_expr(body, *field_expr, current_depth));
            }
        }
        Expr::EnumVariant { fields, .. } => {
            for field_expr in fields {
                max_depth = max_depth.max(max_nesting_depth_expr(body, *field_expr, current_depth));
            }
        }
        Expr::Closure { body: closure_body, .. } => {
            max_depth = max_depth.max(max_nesting_depth_expr(body, *closure_body, current_depth + 1));
        }
        Expr::Literal { .. } | Expr::Variable { .. } => {}
    }

    max_depth
}

fn max_nesting_depth_stmt(body: &Body, stmt_id: StmtId, current_depth: usize) -> usize {
    let stmt = &body.stmts[stmt_id];
    match stmt {
        Stmt::Let { initializer, .. } => {
            initializer.map_or(current_depth, |expr_id| max_nesting_depth_expr(body, expr_id, current_depth))
        }
        Stmt::Expr { expr, .. } => max_nesting_depth_expr(body, *expr, current_depth),
        Stmt::Return { value, .. } => value.map_or(current_depth, |expr_id| max_nesting_depth_expr(body, expr_id, current_depth)),
    }
}

/// Analyzes a function and returns its metrics
pub fn analyze_function(func: &Function) -> FunctionMetrics {
    let name = format!("fn_{}", func.id.0);
    let parameter_count = func.parameters.len();

    let cyclomatic = cyclomatic_complexity(&func.body);
    let cognitive = cognitive_complexity(&func.body);
    let max_depth = max_nesting_depth(&func.body);

    FunctionMetrics {
        name,
        cyclomatic_complexity: cyclomatic,
        cognitive_complexity: cognitive,
        parameter_count,
        max_nesting_depth: max_depth,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rv_hir::LiteralKind;
    use rv_span::{FileId, FileSpan, Span};

    fn make_span() -> FileSpan {
        FileSpan::new(FileId(0), Span::new(0, 0))
    }

    #[test]
    fn test_cyclomatic_simple() {
        let body = Body::new();
        assert_eq!(cyclomatic_complexity(&body), 1);
    }

    #[test]
    fn test_cognitive_simple() {
        let body = Body::new();
        assert_eq!(cognitive_complexity(&body), 0);
    }

    #[test]
    fn test_max_nesting_simple() {
        let body = Body::new();
        assert_eq!(max_nesting_depth(&body), 0);
    }

    #[test]
    fn test_cyclomatic_if() {
        let mut body = Body::new();

        let condition = body.exprs.alloc(Expr::Literal {
            kind: LiteralKind::Bool(true),
            span: make_span(),
        });
        let then_branch = body.exprs.alloc(Expr::Literal {
            kind: LiteralKind::Integer(1),
            span: make_span(),
        });

        let if_expr = body.exprs.alloc(Expr::If {
            condition,
            then_branch,
            else_branch: None,
            span: make_span(),
        });

        body.root_expr = if_expr;

        assert_eq!(cyclomatic_complexity(&body), 4);
    }
}
