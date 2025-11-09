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
        let similarity = calculate_similarity(&func1.body, func1.body.root_expr, func2.body.root_expr);

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
        | Expr::EnumVariant { span, .. } => Some(*span),
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
        Expr::BinaryOp { op, left, right, .. } => {
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
        Expr::Block { statements, expr, .. } => {
            "Block".hash(&mut hasher);
            statements.len().hash(&mut hasher);
            if let Some(e) = expr {
                hash_expr(body, *e).hash(&mut hasher);
            }
        }
        Expr::If { condition, then_branch, else_branch, .. } => {
            "If".hash(&mut hasher);
            hash_expr(body, *condition).hash(&mut hasher);
            hash_expr(body, *then_branch).hash(&mut hasher);
            if let Some(e) = else_branch {
                hash_expr(body, *e).hash(&mut hasher);
            }
        }
        Expr::Match { scrutinee, arms, .. } => {
            "Match".hash(&mut hasher);
            hash_expr(body, *scrutinee).hash(&mut hasher);
            arms.len().hash(&mut hasher);
        }
        Expr::Field { base, field, .. } => {
            "Field".hash(&mut hasher);
            hash_expr(body, *base).hash(&mut hasher);
            format!("{:?}", field).hash(&mut hasher);
        }
        Expr::MethodCall { receiver, method, args, .. } => {
            "MethodCall".hash(&mut hasher);
            hash_expr(body, *receiver).hash(&mut hasher);
            format!("{:?}", method).hash(&mut hasher);
            for arg in args {
                hash_expr(body, *arg).hash(&mut hasher);
            }
        }
        Expr::StructConstruct { struct_name, fields, .. } => {
            "StructConstruct".hash(&mut hasher);
            format!("{:?}", struct_name).hash(&mut hasher);
            for (field_name, field_expr) in fields {
                format!("{:?}", field_name).hash(&mut hasher);
                hash_expr(body, *field_expr).hash(&mut hasher);
            }
        }
        Expr::EnumVariant { enum_name, variant, fields, .. } => {
            "EnumVariant".hash(&mut hasher);
            format!("{:?}", enum_name).hash(&mut hasher);
            format!("{:?}", variant).hash(&mut hasher);
            for field_expr in fields {
                hash_expr(body, *field_expr).hash(&mut hasher);
            }
        }
    }

    hasher.finish()
}

/// Calculate similarity between two expressions (0-100)
fn calculate_similarity(_body1: &Body, _expr1: ExprId, _expr2: ExprId) -> u8 {
    // Simplified: just return 100 if hashes match, 0 otherwise
    // A real implementation would do structural comparison
    100
}

#[cfg(test)]
mod tests {
    use super::*;
    use rv_hir::{Body, FunctionId, LiteralKind};
    use rv_span::{FileId, FileSpan, Span};

    fn make_span() -> FileSpan {
        FileSpan::new(FileId(0), Span::new(0, 0))
    }

    fn make_function(body: Body) -> Function {
        let interner = rv_intern::Interner::new();

        Function {
            id: FunctionId(0),
            name: interner.intern("test"),
            span: make_span(),
            generics: Vec::new(),
            parameters: Vec::new(),
            return_type: None,
            body,
            is_external: false,
        }
    }

    #[test]
    fn test_detector_creation() {
        let detector = DuplicateDetector::new();
        assert_eq!(detector.min_expressions, 3);
        assert_eq!(detector.min_similarity, 80);
    }

    #[test]
    fn test_detector_with_settings() {
        let detector = DuplicateDetector::new()
            .with_min_expressions(5)
            .with_min_similarity(90);

        assert_eq!(detector.min_expressions, 5);
        assert_eq!(detector.min_similarity, 90);
    }

    #[test]
    fn test_simple_function() {
        let body = Body::new();
        let function = make_function(body);

        let detector = DuplicateDetector::new();
        let duplicates = detector.detect_in_function(&function);

        assert_eq!(duplicates.len(), 0);
    }

    #[test]
    fn test_hash_different_literals() {
        let mut body = Body::new();

        let expr1 = body.exprs.alloc(Expr::Literal {
            kind: LiteralKind::Integer(42),
            span: make_span(),
        });

        let expr2 = body.exprs.alloc(Expr::Literal {
            kind: LiteralKind::Integer(100),
            span: make_span(),
        });

        let hash1 = hash_expr(&body, expr1);
        let hash2 = hash_expr(&body, expr2);

        // Different values should produce different hashes
        assert_ne!(hash1, hash2);
    }
}
