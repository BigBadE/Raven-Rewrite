//! Name resolution pass

use crate::error::ResolutionError;
use crate::scope::{ScopeId, ScopeKind, ScopeTree};
use rv_hir::{
    Body, DefId, Expr, ExprId, Function, LocalId, Pattern, PatternId, Stmt, StmtId, Visibility,
};
use rv_intern::Interner;
use rustc_hash::FxHashMap;

/// Result of name resolution
#[derive(Debug, Clone)]
pub struct ResolutionResult {
    /// Scope tree built during resolution
    pub scopes: ScopeTree,
    /// Mapping from expression IDs to resolved definitions
    pub resolutions: FxHashMap<ExprId, DefId>,
    /// Mapping from pattern bindings to local IDs
    pub pattern_locals: FxHashMap<PatternId, LocalId>,
    /// Errors encountered during resolution
    pub errors: Vec<ResolutionError>,
}

/// Name resolver for a function body
pub struct NameResolver<'a> {
    /// Scope tree being built
    scopes: ScopeTree,
    /// Current scope
    current_scope: ScopeId,
    /// HIR body being resolved
    body: &'a Body,
    /// Function being resolved
    function: &'a Function,
    /// String interner for name lookups
    interner: &'a Interner,
    /// Variable expression -> DefId mapping
    resolutions: FxHashMap<ExprId, DefId>,
    /// Pattern binding -> LocalId mapping
    pattern_locals: FxHashMap<PatternId, LocalId>,
    /// Next local ID to allocate
    next_local_id: u32,
    /// Collected errors
    errors: Vec<ResolutionError>,
}

impl<'a> NameResolver<'a> {
    /// Create a new name resolver
    fn new(body: &'a Body, function: &'a Function, interner: &'a Interner) -> Self {
        Self {
            scopes: ScopeTree::new(),
            current_scope: ScopeTree::new().module_scope,
            body,
            function,
            interner,
            resolutions: FxHashMap::default(),
            pattern_locals: FxHashMap::default(),
            next_local_id: 0,
            errors: Vec::new(),
        }
    }

    /// Main entry point for name resolution
    ///
    /// Performs a two-pass resolution:
    /// 1. Define all function parameters
    /// 2. Resolve all expressions and statements
    pub fn resolve(
        body: &'a Body,
        function: &'a Function,
        interner: &'a Interner,
    ) -> ResolutionResult {
        let mut resolver = Self::new(body, function, interner);

        // Create function scope
        let function_scope =
            resolver
                .scopes
                .create_child(resolver.scopes.module_scope, ScopeKind::Function);
        resolver.current_scope = function_scope;

        // Pass 1: Define function parameters
        resolver.define_function_parameters();

        // Pass 2: Resolve all expressions in the body
        resolver.resolve_expressions();

        ResolutionResult {
            scopes: resolver.scopes,
            resolutions: resolver.resolutions,
            pattern_locals: resolver.pattern_locals,
            errors: resolver.errors,
        }
    }

    /// Define function parameters in the function scope
    fn define_function_parameters(&mut self) {
        for param in &self.function.parameters {
            let local_id = LocalId(self.next_local_id);
            self.next_local_id += 1;

            let def_id = DefId::Local(local_id);

            if let Err(error) = self.scopes.define(
                self.current_scope,
                param.name,
                def_id,
                Visibility::Private,
                false, // Parameters are immutable by default
                param.span,
            ) {
                self.errors.push(error);
            }
        }
    }

    /// Resolve all expressions in the function body
    fn resolve_expressions(&mut self) {
        self.resolve_expr(self.body.root_expr);
    }

    /// Resolve a single expression
    fn resolve_expr(&mut self, expr_id: ExprId) {
        let expr = self.body.exprs[expr_id].clone();

        match expr {
            Expr::Variable { name, span, .. } => {
                // Resolve variable to definition
                match self
                    .scopes
                    .resolve(self.current_scope, name, span, self.interner)
                {
                    Ok(resolution) => {
                        self.resolutions.insert(expr_id, resolution.def);
                    }
                    Err(error) => {
                        self.errors.push(error);
                    }
                }
            }

            Expr::Block {
                statements, expr, ..
            } => {
                // Create new scope for block
                let block_scope =
                    self.scopes
                        .create_child(self.current_scope, ScopeKind::Block);
                let previous_scope = self.current_scope;
                self.current_scope = block_scope;

                // Resolve all statements
                for stmt_id in statements {
                    self.resolve_stmt(stmt_id);
                }

                // Resolve trailing expression
                if let Some(expr_id) = expr {
                    self.resolve_expr(expr_id);
                }

                self.current_scope = previous_scope;
            }

            Expr::Call { callee, args, .. } => {
                // Resolve callee
                self.resolve_expr(callee);

                // Resolve arguments
                for arg in args {
                    self.resolve_expr(arg);
                }
            }

            Expr::BinaryOp { left, right, .. } => {
                self.resolve_expr(left);
                self.resolve_expr(right);
            }

            Expr::UnaryOp { operand, .. } => {
                self.resolve_expr(operand);
            }

            Expr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                self.resolve_expr(condition);
                self.resolve_expr(then_branch);
                if let Some(else_expr) = else_branch {
                    self.resolve_expr(else_expr);
                }
            }

            Expr::Match {
                scrutinee, arms, ..
            } => {
                self.resolve_expr(scrutinee);

                for arm in arms {
                    // Create new scope for match arm
                    let arm_scope =
                        self.scopes
                            .create_child(self.current_scope, ScopeKind::MatchArm);
                    let previous_scope = self.current_scope;
                    self.current_scope = arm_scope;

                    // Define pattern bindings
                    self.define_pattern_bindings(arm.pattern, false);

                    // Resolve guard
                    if let Some(guard_expr) = arm.guard {
                        self.resolve_expr(guard_expr);
                    }

                    // Resolve body
                    self.resolve_expr(arm.body);

                    self.current_scope = previous_scope;
                }
            }

            Expr::Field { base, .. } => {
                self.resolve_expr(base);
            }

            Expr::MethodCall {
                receiver, args, ..
            } => {
                self.resolve_expr(receiver);
                for arg in args {
                    self.resolve_expr(arg);
                }
            }

            Expr::StructConstruct { fields, .. } => {
                for (_, field_expr) in fields {
                    self.resolve_expr(field_expr);
                }
            }

            Expr::EnumVariant { fields, .. } => {
                for field_expr in fields {
                    self.resolve_expr(field_expr);
                }
            }

            Expr::Closure {
                params, body, .. // captures handled by closure analysis
            } => {
                // Create new scope for closure
                let closure_scope =
                    self.scopes
                        .create_child(self.current_scope, ScopeKind::Closure);
                let previous_scope = self.current_scope;
                self.current_scope = closure_scope;

                // Define closure parameters
                for param in params {
                    let local_id = LocalId(self.next_local_id);
                    self.next_local_id += 1;
                    let def_id = DefId::Local(local_id);

                    if let Err(error) = self.scopes.define(
                        self.current_scope,
                        param.name,
                        def_id,
                        Visibility::Private,
                        false,
                        param.span,
                    ) {
                        self.errors.push(error);
                    }
                }

                // Resolve closure body
                self.resolve_expr(body);

                self.current_scope = previous_scope;
            }

            Expr::Literal { .. } => {
                // Literals have no names to resolve
            }
        }
    }

    /// Resolve a statement
    fn resolve_stmt(&mut self, stmt_id: StmtId) {
        let stmt = self.body.stmts[stmt_id].clone();

        match stmt {
            Stmt::Let {
                pattern,
                initializer,
                mutable,
                ..
            } => {
                // Resolve initializer first (before pattern bindings are visible)
                if let Some(init_expr) = initializer {
                    self.resolve_expr(init_expr);
                }

                // Define pattern bindings (now visible in subsequent statements)
                self.define_pattern_bindings(pattern, mutable);
            }

            Stmt::Expr { expr, .. } => {
                self.resolve_expr(expr);
            }

            Stmt::Return { value, .. } => {
                if let Some(expr) = value {
                    self.resolve_expr(expr);
                }
            }
        }
    }

    /// Define bindings from a pattern
    fn define_pattern_bindings(&mut self, pattern_id: PatternId, mutable: bool) {
        let pattern = self.body.patterns[pattern_id].clone();

        match pattern {
            Pattern::Binding { name, span, .. } => {
                // Create a new local
                let local_id = LocalId(self.next_local_id);
                self.next_local_id += 1;
                let def_id = DefId::Local(local_id);

                // Record the mapping from pattern to local
                self.pattern_locals.insert(pattern_id, local_id);

                // Define in current scope
                if let Err(error) = self.scopes.define(
                    self.current_scope,
                    name,
                    def_id,
                    Visibility::Private,
                    mutable,
                    span,
                ) {
                    self.errors.push(error);
                }
            }

            Pattern::Tuple { patterns, .. } => {
                // Recurse on tuple elements
                for sub_pattern in patterns {
                    self.define_pattern_bindings(sub_pattern, mutable);
                }
            }

            Pattern::Struct { fields, .. } => {
                // Recurse on field patterns
                for (_, field_pattern) in fields {
                    self.define_pattern_bindings(field_pattern, mutable);
                }
            }

            Pattern::Enum { sub_patterns, .. } => {
                // Recurse on enum sub-patterns
                for sub_pattern in sub_patterns {
                    self.define_pattern_bindings(sub_pattern, mutable);
                }
            }

            Pattern::Or { patterns, .. } => {
                // All alternatives must bind the same variables
                // For simplicity, we process each alternative
                for sub_pattern in patterns {
                    self.define_pattern_bindings(sub_pattern, mutable);
                }
            }

            Pattern::Wildcard { .. } | Pattern::Literal { .. } | Pattern::Range { .. } => {
                // These patterns don't bind any variables
            }
        }
    }
}
