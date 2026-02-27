//! Duplicate code detection
//!
//! AST-based detection of copy-pasted or similar code

use rustc_hash::FxHashMap;
use rv_hir::{Body, Expr, ExprId, Function};
use rv_span::FileSpan;
use serde::{Deserialize, Serialize};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// A detected code duplicate
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Duplicate {
    /// First occurrence
    pub first: FileSpan,
    /// Second occurrence
    pub second: FileSpan,
    /// Similarity score (0-100)
    pub similarity: u8,
    /// Number of similar expressions
    pub expression_count: usize,
}

/// Duplicate detector
pub struct DuplicateDetector {
    /// Minimum number of expressions to consider
    min_expressions: usize,
    /// Minimum similarity threshold (0-100)
    min_similarity: u8,
}

impl Default for DuplicateDetector {
    fn default() -> Self {
        Self::new()
    }
}

impl DuplicateDetector {
    /// Create a new duplicate detector with default settings
    #[must_use]
    pub fn new() -> Self {
        Self {
            min_expressions: 3,
            min_similarity: 80,
        }
    }

    /// Set minimum number of expressions
    #[must_use]
    pub fn with_min_expressions(mut self, min: usize) -> Self {
        self.min_expressions = min;
        self
    }

    /// Set minimum similarity threshold
    #[must_use]
    pub fn with_min_similarity(mut self, min: u8) -> Self {
        self.min_similarity = min.min(100);
        self
    }

    /// Detect duplicates in a function
    pub fn detect_in_function(&self, function: &Function) -> Vec<Duplicate> {
        let mut duplicates = Vec::new();
        let mut expr_hashes: FxHashMap<u64, Vec<(ExprId, FileSpan)>> = FxHashMap::default();

        // Collect all expressions and their hashes
        for (expr_id, expr) in function.body.exprs.iter() {
            if let Some(span) = get_expr_span(expr) {
                let hash = hash_expr(&function.body, expr_id);
                expr_hashes.entry(hash).or_default().push((expr_id, span));
            }
        }

        // Find duplicates
        for (_hash, occurrences) in expr_hashes {
            if occurrences.len() >= 2 {
                // Compare each pair
                for i in 0..occurrences.len() {
                    for j in (i + 1)..occurrences.len() {
                        let (expr1, span1) = occurrences[i];
                        let (expr2, span2) = occurrences[j];

                        let similarity = calculate_similarity(&function.body, expr1, expr2);

                        if similarity >= self.min_similarity {
                            duplicates.push(Duplicate {
                                first: span1,
                                second: span2,
                                similarity,
                                expression_count: 1,
                            });
                        }
                    }
                }
            }
        }

        duplicates
    }

    /// Detect duplicates across multiple functions
    pub fn detect_across_functions(&self, functions: &[&Function]) -> Vec<Duplicate> {
        let mut duplicates = Vec::new();

        // Simple pairwise comparison
        for i in 0..functions.len() {
            for j in (i + 1)..functions.len() {
                let func_duplicates = self.compare_functions(functions[i], functions[j]);
                duplicates.extend(func_duplicates);
            }
        }

        duplicates
    }

    fn compare_functions(&self, func1: &Function, func2: &Function) -> Vec<Duplicate> {
        let mut duplicates = Vec::new();

        // Compare root expressions
        let similarity =
            calculate_similarity(&func1.body, func1.body.root_expr, func2.body.root_expr);

        if similarity >= self.min_similarity {
            duplicates.push(Duplicate {
                first: func1.span,
                second: func2.span,
                similarity,
                expression_count: 1,
            });
        }

        duplicates
    }
}

/// Get the span of an expression
fn get_expr_span(expr: &Expr) -> Option<FileSpan> {
    match expr {
        Expr::Literal { span, .. }
        | Expr::Variable { span, .. }
        | Expr::Call { span, .. }
        | Expr::BinaryOp { span, .. }
        | Expr::UnaryOp { span, .. }
        | Expr::Block { span, .. }
        | Expr::If { span, .. }
        | Expr::Match { span, .. }
        | Expr::Field { span, .. }
        | Expr::MethodCall { span, .. }
        | Expr::StructConstruct { span, .. }
        | Expr::EnumVariant { span, .. }
        | Expr::Closure { span, .. }
        | Expr::PathCall { span, .. }
        | Expr::Assign { span, .. }
        | Expr::CompoundAssign { span, .. }
        | Expr::WhileLoop { span, .. }
        | Expr::Loop { span, .. }
        | Expr::Break { span, .. }
        | Expr::Continue { span, .. }
        | Expr::Array { span, .. }
        | Expr::Tuple { span, .. }
        | Expr::Index { span, .. }
        | Expr::Cast { span, .. }
        | Expr::UnsafeBlock { span, .. }
        | Expr::Error { span, .. }
        | Expr::WhileLet { span, .. }
        | Expr::IfLet { span, .. }
        | Expr::Range { span, .. }
        | Expr::Try { span, .. }
        | Expr::ForLoop { span, .. }
        | Expr::Box { span, .. } => Some(*span),
    }
}

/// Hash an expression structurally
fn hash_expr(body: &Body, expr_id: ExprId) -> u64 {
    let expr = &body.exprs[expr_id];
    let mut hasher = DefaultHasher::new();

    match expr {
        Expr::Literal { kind, .. } => {
            "Literal".hash(&mut hasher);
            format!("{:?}", kind).hash(&mut hasher);
        }
        Expr::Variable { name, .. } => {
            "Variable".hash(&mut hasher);
            format!("{:?}", name).hash(&mut hasher);
        }
        Expr::Call { callee, args, .. } => {
            "Call".hash(&mut hasher);
            hash_expr(body, *callee).hash(&mut hasher);
            for arg in args {
                hash_expr(body, *arg).hash(&mut hasher);
            }
        }
        Expr::BinaryOp {
            op, left, right, ..
        } => {
            "BinaryOp".hash(&mut hasher);
            format!("{:?}", op).hash(&mut hasher);
            hash_expr(body, *left).hash(&mut hasher);
            hash_expr(body, *right).hash(&mut hasher);
        }
        Expr::UnaryOp { op, operand, .. } => {
            "UnaryOp".hash(&mut hasher);
            format!("{:?}", op).hash(&mut hasher);
            hash_expr(body, *operand).hash(&mut hasher);
        }
        Expr::Block {
            statements, expr, ..
        } => {
            "Block".hash(&mut hasher);
            statements.len().hash(&mut hasher);
            if let Some(e) = expr {
                hash_expr(body, *e).hash(&mut hasher);
            }
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            "If".hash(&mut hasher);
            hash_expr(body, *condition).hash(&mut hasher);
            hash_expr(body, *then_branch).hash(&mut hasher);
            if let Some(e) = else_branch {
                hash_expr(body, *e).hash(&mut hasher);
            }
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            "Match".hash(&mut hasher);
            hash_expr(body, *scrutinee).hash(&mut hasher);
            arms.len().hash(&mut hasher);
        }
        Expr::Field { base, field, .. } => {
            "Field".hash(&mut hasher);
            hash_expr(body, *base).hash(&mut hasher);
            format!("{:?}", field).hash(&mut hasher);
        }
        Expr::MethodCall {
            receiver,
            method,
            args,
            ..
        } => {
            "MethodCall".hash(&mut hasher);
            hash_expr(body, *receiver).hash(&mut hasher);
            format!("{:?}", method).hash(&mut hasher);
            for arg in args {
                hash_expr(body, *arg).hash(&mut hasher);
            }
        }
        Expr::StructConstruct {
            struct_name,
            fields,
            ..
        } => {
            "StructConstruct".hash(&mut hasher);
            format!("{:?}", struct_name).hash(&mut hasher);
            for (field_name, field_expr) in fields {
                format!("{:?}", field_name).hash(&mut hasher);
                hash_expr(body, *field_expr).hash(&mut hasher);
            }
        }
        Expr::EnumVariant {
            enum_name,
            variant,
            fields,
            ..
        } => {
            "EnumVariant".hash(&mut hasher);
            format!("{:?}", enum_name).hash(&mut hasher);
            format!("{:?}", variant).hash(&mut hasher);
            for field_expr in fields {
                hash_expr(body, *field_expr).hash(&mut hasher);
            }
        }
        Expr::Closure {
            params,
            body: closure_body,
            ..
        } => {
            "Closure".hash(&mut hasher);
            params.len().hash(&mut hasher);
            hash_expr(body, *closure_body).hash(&mut hasher);
        }
        Expr::PathCall {
            path,
            function,
            args,
            ..
        } => {
            "PathCall".hash(&mut hasher);
            for segment in path {
                format!("{:?}", segment).hash(&mut hasher);
            }
            format!("{:?}", function).hash(&mut hasher);
            for arg in args {
                hash_expr(body, *arg).hash(&mut hasher);
            }
        }
        Expr::Assign { target, value, .. } => {
            "Assign".hash(&mut hasher);
            hash_expr(body, *target).hash(&mut hasher);
            hash_expr(body, *value).hash(&mut hasher);
        }
        Expr::CompoundAssign {
            target, op, value, ..
        } => {
            "CompoundAssign".hash(&mut hasher);
            hash_expr(body, *target).hash(&mut hasher);
            format!("{:?}", op).hash(&mut hasher);
            hash_expr(body, *value).hash(&mut hasher);
        }
        Expr::WhileLoop {
            condition,
            body: loop_body,
            ..
        } => {
            "WhileLoop".hash(&mut hasher);
            hash_expr(body, *condition).hash(&mut hasher);
            hash_expr(body, *loop_body).hash(&mut hasher);
        }
        Expr::Loop {
            body: loop_body, ..
        } => {
            "Loop".hash(&mut hasher);
            hash_expr(body, *loop_body).hash(&mut hasher);
        }
        Expr::Break { value, .. } => {
            "Break".hash(&mut hasher);
            if let Some(v) = value {
                hash_expr(body, *v).hash(&mut hasher);
            }
        }
        Expr::Continue { .. } => {
            "Continue".hash(&mut hasher);
        }
        Expr::Array { elements, .. } => {
            "Array".hash(&mut hasher);
            for elem in elements {
                hash_expr(body, *elem).hash(&mut hasher);
            }
        }
        Expr::Tuple { elements, .. } => {
            "Tuple".hash(&mut hasher);
            for elem in elements {
                hash_expr(body, *elem).hash(&mut hasher);
            }
        }
        Expr::Index { base, index, .. } => {
            "Index".hash(&mut hasher);
            hash_expr(body, *base).hash(&mut hasher);
            hash_expr(body, *index).hash(&mut hasher);
        }
        Expr::Cast {
            expr: cast_expr, ..
        } => {
            "Cast".hash(&mut hasher);
            hash_expr(body, *cast_expr).hash(&mut hasher);
        }
        Expr::UnsafeBlock { body: inner, .. } => {
            "UnsafeBlock".hash(&mut hasher);
            hash_expr(body, *inner).hash(&mut hasher);
        }
        Expr::Error { .. } => {
            "Error".hash(&mut hasher);
        }
        Expr::WhileLet { value, body: while_body, .. } => {
            "WhileLet".hash(&mut hasher);
            hash_expr(body, *value).hash(&mut hasher);
            hash_expr(body, *while_body).hash(&mut hasher);
        }
        Expr::IfLet { value, then_branch, else_branch, .. } => {
            "IfLet".hash(&mut hasher);
            hash_expr(body, *value).hash(&mut hasher);
            hash_expr(body, *then_branch).hash(&mut hasher);
            if let Some(else_expr) = else_branch {
                hash_expr(body, *else_expr).hash(&mut hasher);
            }
        }
        Expr::Range { start, end, inclusive, .. } => {
            "Range".hash(&mut hasher);
            inclusive.hash(&mut hasher);
            if let Some(s) = start {
                hash_expr(body, *s).hash(&mut hasher);
            }
            if let Some(e) = end {
                hash_expr(body, *e).hash(&mut hasher);
            }
        }
        Expr::Try { expr: try_expr, .. } => {
            "Try".hash(&mut hasher);
            hash_expr(body, *try_expr).hash(&mut hasher);
        }
        Expr::ForLoop { iterator, body: loop_body, .. } => {
            "ForLoop".hash(&mut hasher);
            hash_expr(body, *iterator).hash(&mut hasher);
            hash_expr(body, *loop_body).hash(&mut hasher);
        }
        Expr::Box { value, .. } => {
            "Box".hash(&mut hasher);
            hash_expr(body, *value).hash(&mut hasher);
        }
    }

    hasher.finish()
}

/// Calculate structural similarity between two expressions (0-100).
///
/// Compares two expression trees by walking their structure recursively and
/// counting how many nodes match vs differ. Returns a percentage score.
fn calculate_similarity(body: &Body, expr1: ExprId, expr2: ExprId) -> u8 {
    let mut matching = 0u32;
    let mut total = 0u32;
    count_similarity(body, expr1, expr2, &mut matching, &mut total);
    if total == 0 {
        return 100; // Two empty/leaf expressions are identical
    }
    ((matching as u64 * 100) / total as u64) as u8
}

/// Recursively count matching and total nodes between two expression trees.
fn count_similarity(
    body: &Body,
    expr1: ExprId,
    expr2: ExprId,
    matching: &mut u32,
    total: &mut u32,
) {
    let e1 = &body.exprs[expr1];
    let e2 = &body.exprs[expr2];
    *total += 1;

    match (e1, e2) {
        (Expr::Literal { kind: k1, .. }, Expr::Literal { kind: k2, .. }) => {
            if format!("{k1:?}") == format!("{k2:?}") {
                *matching += 1;
            }
        }
        (Expr::Variable { name: n1, .. }, Expr::Variable { name: n2, .. }) => {
            if n1 == n2 {
                *matching += 1;
            }
        }
        (
            Expr::BinaryOp {
                op: op1,
                left: l1,
                right: r1,
                ..
            },
            Expr::BinaryOp {
                op: op2,
                left: l2,
                right: r2,
                ..
            },
        ) => {
            if op1 == op2 {
                *matching += 1;
            }
            count_similarity(body, *l1, *l2, matching, total);
            count_similarity(body, *r1, *r2, matching, total);
        }
        (
            Expr::UnaryOp {
                op: op1,
                operand: o1,
                ..
            },
            Expr::UnaryOp {
                op: op2,
                operand: o2,
                ..
            },
        ) => {
            if op1 == op2 {
                *matching += 1;
            }
            count_similarity(body, *o1, *o2, matching, total);
        }
        (
            Expr::Call {
                callee: c1,
                args: a1,
                ..
            },
            Expr::Call {
                callee: c2,
                args: a2,
                ..
            },
        ) => {
            *matching += 1; // Same node kind
            count_similarity(body, *c1, *c2, matching, total);
            let min_args = a1.len().min(a2.len());
            for i in 0..min_args {
                count_similarity(body, a1[i], a2[i], matching, total);
            }
            // Count extra args as non-matching
            *total += (a1.len().max(a2.len()) - min_args) as u32;
        }
        (
            Expr::If {
                condition: c1,
                then_branch: t1,
                else_branch: e1,
                ..
            },
            Expr::If {
                condition: c2,
                then_branch: t2,
                else_branch: e2,
                ..
            },
        ) => {
            *matching += 1;
            count_similarity(body, *c1, *c2, matching, total);
            count_similarity(body, *t1, *t2, matching, total);
            match (e1, e2) {
                (Some(eb1), Some(eb2)) => count_similarity(body, *eb1, *eb2, matching, total),
                (None, None) => {}
                _ => *total += 1, // Structural mismatch
            }
        }
        (
            Expr::Block {
                statements: s1,
                expr: e1,
                ..
            },
            Expr::Block {
                statements: s2,
                expr: e2,
                ..
            },
        ) => {
            *matching += 1;
            // Statement comparison would require stmt similarity; count structural match
            if s1.len() == s2.len() {
                *matching += 1;
            }
            *total += 1;
            match (e1, e2) {
                (Some(eb1), Some(eb2)) => count_similarity(body, *eb1, *eb2, matching, total),
                (None, None) => {}
                _ => *total += 1,
            }
        }
        (
            Expr::MethodCall {
                receiver: r1,
                method: m1,
                args: a1,
                ..
            },
            Expr::MethodCall {
                receiver: r2,
                method: m2,
                args: a2,
                ..
            },
        ) => {
            if m1 == m2 {
                *matching += 1;
            }
            count_similarity(body, *r1, *r2, matching, total);
            let min_args = a1.len().min(a2.len());
            for i in 0..min_args {
                count_similarity(body, a1[i], a2[i], matching, total);
            }
            *total += (a1.len().max(a2.len()) - min_args) as u32;
        }
        _ => {
            // Different node kinds — no match at this level
        }
    }
}
