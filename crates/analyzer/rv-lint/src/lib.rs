//! Lint rule engine for code quality checks
//!
//! Provides extensible linting infrastructure with built-in rules

use rv_hir::{Body, Expr, ExprId, Function, Stmt};
use rv_span::FileSpan;
use serde::{Deserialize, Serialize};

/// Lint severity level
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum LintLevel {
    /// Informational message
    Info,
    /// Warning that should be addressed
    Warning,
    /// Error that must be fixed
    Error,
}

/// A lint diagnostic
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Diagnostic {
    /// Lint rule that triggered this diagnostic
    pub rule: String,
    /// Severity level
    pub level: LintLevel,
    /// Human-readable message
    pub message: String,
    /// Source location
    pub span: FileSpan,
    /// Optional suggestion for fixing
    pub suggestion: Option<String>,
}

/// Lint context for running rules
pub struct LintContext<'a> {
    /// Function being linted
    pub function: &'a Function,
    /// Collected diagnostics
    diagnostics: Vec<Diagnostic>,
}

impl<'a> LintContext<'a> {
    /// Create a new lint context
    #[must_use]
    pub fn new(function: &'a Function) -> Self {
        Self {
            function,
            diagnostics: Vec::new(),
        }
    }

    /// Report a diagnostic
    pub fn report(&mut self, diagnostic: Diagnostic) {
        self.diagnostics.push(diagnostic);
    }

    /// Get all diagnostics
    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    /// Take all diagnostics
    #[must_use]
    pub fn take_diagnostics(self) -> Vec<Diagnostic> {
        self.diagnostics
    }
}

/// Trait for lint rules
pub trait LintRule {
    /// Rule name
    fn name(&self) -> &str;

    /// Check a function
    fn check_function(&self, ctx: &mut LintContext);
}

/// Rule: Functions with high cyclomatic complexity
pub struct ComplexityRule {
    /// Maximum allowed complexity
    pub max_complexity: usize,
}

impl Default for ComplexityRule {
    fn default() -> Self {
        Self {
            max_complexity: 10,
        }
    }
}

impl LintRule for ComplexityRule {
    fn name(&self) -> &str {
        "complexity"
    }

    fn check_function(&self, ctx: &mut LintContext) {
        let complexity = rv_metrics::cyclomatic_complexity(&ctx.function.body);

        if complexity > self.max_complexity {
            ctx.report(Diagnostic {
                rule: self.name().to_string(),
                level: LintLevel::Warning,
                message: format!(
                    "Function has cyclomatic complexity of {} (max: {})",
                    complexity, self.max_complexity
                ),
                span: ctx.function.span,
                suggestion: Some("Consider breaking this function into smaller functions".to_string()),
            });
        }
    }
}

/// Rule: Functions with too many parameters
pub struct TooManyParametersRule {
    /// Maximum allowed parameters
    pub max_parameters: usize,
}

impl Default for TooManyParametersRule {
    fn default() -> Self {
        Self {
            max_parameters: 5,
        }
    }
}

impl LintRule for TooManyParametersRule {
    fn name(&self) -> &str {
        "too-many-parameters"
    }

    fn check_function(&self, ctx: &mut LintContext) {
        let param_count = ctx.function.parameters.len();

        if param_count > self.max_parameters {
            ctx.report(Diagnostic {
                rule: self.name().to_string(),
                level: LintLevel::Warning,
                message: format!(
                    "Function has {} parameters (max: {})",
                    param_count, self.max_parameters
                ),
                span: ctx.function.span,
                suggestion: Some("Consider using a struct to group related parameters".to_string()),
            });
        }
    }
}

/// Rule: Deep nesting
pub struct DeepNestingRule {
    /// Maximum allowed nesting depth
    pub max_depth: usize,
}

impl Default for DeepNestingRule {
    fn default() -> Self {
        Self {
            max_depth: 4,
        }
    }
}

impl LintRule for DeepNestingRule {
    fn name(&self) -> &str {
        "deep-nesting"
    }

    fn check_function(&self, ctx: &mut LintContext) {
        let max_depth = rv_metrics::max_nesting_depth(&ctx.function.body);

        if max_depth > self.max_depth {
            ctx.report(Diagnostic {
                rule: self.name().to_string(),
                level: LintLevel::Warning,
                message: format!(
                    "Function has nesting depth of {} (max: {})",
                    max_depth, self.max_depth
                ),
                span: ctx.function.span,
                suggestion: Some("Consider extracting nested logic into separate functions".to_string()),
            });
        }
    }
}

/// Rule: Unused variables
pub struct UnusedVariableRule;

impl LintRule for UnusedVariableRule {
    fn name(&self) -> &str {
        "unused-variable"
    }

    fn check_function(&self, ctx: &mut LintContext) {
        // Walk the body and find all let bindings
        let mut defined_vars: Vec<(ExprId, FileSpan)> = Vec::new();
        let mut used_vars: Vec<ExprId> = Vec::new();

        collect_let_bindings(&ctx.function.body, &mut defined_vars);
        collect_variable_uses(&ctx.function.body, &mut used_vars);

        // Report unused variables
        for (var_id, span) in defined_vars {
            if !used_vars.contains(&var_id) {
                ctx.report(Diagnostic {
                    rule: self.name().to_string(),
                    level: LintLevel::Warning,
                    message: "Variable is defined but never used".to_string(),
                    span,
                    suggestion: Some("Remove the unused variable or prefix with '_'".to_string()),
                });
            }
        }
    }
}

fn collect_let_bindings(body: &Body, vars: &mut Vec<(ExprId, FileSpan)>) {
    for (_stmt_id, stmt) in body.stmts.iter() {
        if let Stmt::Let { initializer, span, .. } = stmt {
            if let Some(init_id) = initializer {
                vars.push((*init_id, *span));
            }
        }
    }
}

fn collect_variable_uses(body: &Body, _vars: &mut Vec<ExprId>) {
    for (_expr_id, expr) in body.exprs.iter() {
        if let Expr::Variable { .. } = expr {
            // In a real implementation, would track the actual variable reference
            // For now, this is a placeholder
        }
    }
}

/// Rule: Cognitive complexity
pub struct CognitiveComplexityRule {
    /// Maximum allowed cognitive complexity
    pub max_complexity: usize,
}

impl Default for CognitiveComplexityRule {
    fn default() -> Self {
        Self {
            max_complexity: 15,
        }
    }
}

impl LintRule for CognitiveComplexityRule {
    fn name(&self) -> &str {
        "cognitive-complexity"
    }

    fn check_function(&self, ctx: &mut LintContext) {
        let complexity = rv_metrics::cognitive_complexity(&ctx.function.body);

        if complexity > self.max_complexity {
            ctx.report(Diagnostic {
                rule: self.name().to_string(),
                level: LintLevel::Warning,
                message: format!(
                    "Function has cognitive complexity of {} (max: {})",
                    complexity, self.max_complexity
                ),
                span: ctx.function.span,
                suggestion: Some("Simplify the logic or extract complex branches".to_string()),
            });
        }
    }
}

/// Linter with a collection of rules
pub struct Linter {
    rules: Vec<Box<dyn LintRule>>,
}

impl Linter {
    /// Create a new linter with default rules
    #[must_use]
    pub fn new() -> Self {
        Self::with_rules(vec![
            Box::new(ComplexityRule::default()),
            Box::new(TooManyParametersRule::default()),
            Box::new(DeepNestingRule::default()),
            Box::new(CognitiveComplexityRule::default()),
        ])
    }

    /// Create a linter with specific rules
    #[must_use]
    pub fn with_rules(rules: Vec<Box<dyn LintRule>>) -> Self {
        Self { rules }
    }

    /// Lint a function
    pub fn lint_function(&self, function: &Function) -> Vec<Diagnostic> {
        let mut ctx = LintContext::new(function);

        for rule in &self.rules {
            rule.check_function(&mut ctx);
        }

        ctx.take_diagnostics()
    }

    /// Add a rule
    pub fn add_rule(&mut self, rule: Box<dyn LintRule>) {
        self.rules.push(rule);
    }
}

impl Default for Linter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rv_hir::{Body, FunctionId, LiteralKind, Parameter};
    use rv_span::{FileId, FileSpan, Span};

    fn make_span() -> FileSpan {
        FileSpan::new(FileId(0), Span::new(0, 0))
    }

    fn make_test_function(body: Body, param_count: usize) -> Function {
        let interner = rv_intern::Interner::new();
        let name_symbol = interner.intern("test_function");
        let param_symbol = interner.intern("param");

        Function {
            id: FunctionId(0),
            name: name_symbol,
            span: make_span(),
            generics: Vec::new(),
            parameters: vec![Parameter {
                name: param_symbol,
                ty: rv_hir::TypeId::from_raw(0.into()),
                span: make_span(),
            }; param_count],
            return_type: None,
            body,
            is_external: false,
        }
    }

    #[test]
    fn test_complexity_rule_pass() {
        let body = Body::new();
        let function = make_test_function(body, 0);

        let rule = ComplexityRule::default();
        let mut ctx = LintContext::new(&function);
        rule.check_function(&mut ctx);

        assert_eq!(ctx.diagnostics().len(), 0);
    }

    #[test]
    fn test_too_many_parameters() {
        let body = Body::new();
        let function = make_test_function(body, 10);

        let rule = TooManyParametersRule::default();
        let mut ctx = LintContext::new(&function);
        rule.check_function(&mut ctx);

        assert_eq!(ctx.diagnostics().len(), 1);
        assert_eq!(ctx.diagnostics()[0].rule, "too-many-parameters");
        assert_eq!(ctx.diagnostics()[0].level, LintLevel::Warning);
    }

    #[test]
    fn test_linter() {
        let body = Body::new();
        let function = make_test_function(body, 0);

        let linter = Linter::new();
        let diagnostics = linter.lint_function(&function);

        // Simple function should have no warnings
        assert_eq!(diagnostics.len(), 0);
    }

    #[test]
    fn test_linter_with_complex_function() {
        let mut body = Body::new();

        // Create a complex if expression
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
        let function = make_test_function(body, 10);

        let linter = Linter::new();
        let diagnostics = linter.lint_function(&function);

        // Should trigger too-many-parameters rule
        assert!(diagnostics.len() > 0);
        assert!(diagnostics.iter().any(|d| d.rule == "too-many-parameters"));
    }
}
