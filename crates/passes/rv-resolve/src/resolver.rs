//! Name resolution pass

use crate::error::ResolutionError;
use crate::module::{ImportKind, ModuleResolver, ResolvedImport};
use crate::scope::{ScopeId, ScopeKind, ScopeTree};
use rustc_hash::FxHashMap;
use rv_hir::{
    Body, DefId, Expr, ExprId, Function, LocalId, ModuleId, Pattern, PatternId, Stmt, StmtId,
    Visibility,
};
use rv_intern::{Interner, Symbol};

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
    /// Optional module resolver for cross-module lookups (used by resolve_path)
    module_resolver: Option<&'a ModuleResolver>,
    /// Current module ID for cross-module resolution (used by resolve_path)
    current_module: Option<ModuleId>,
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
            module_resolver: None,
            current_module: None,
        }
    }

    /// Create a new name resolver with module-level resolution support
    fn new_with_modules(
        body: &'a Body,
        function: &'a Function,
        interner: &'a Interner,
        module_resolver: &'a ModuleResolver,
        module_id: ModuleId,
    ) -> Self {
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
            module_resolver: Some(module_resolver),
            current_module: Some(module_id),
        }
    }

    /// Main entry point for name resolution
    ///
    /// Performs a two-pass resolution:
    /// 1. Define all function parameters
    /// 2. Resolve all expressions and statements
    ///
    /// # Parameters
    /// - `available_functions`: Functions available for resolution (name -> DefId)
    ///   These will be registered in the module scope before resolution begins
    pub fn resolve(
        body: &'a Body,
        function: &'a Function,
        interner: &'a Interner,
        available_functions: FxHashMap<rv_intern::Symbol, DefId>,
    ) -> ResolutionResult {
        let mut resolver = Self::new(body, function, interner);

        // Register all available functions in module scope
        // This allows function calls to be resolved
        for (name, def_id) in available_functions {
            match resolver.scopes.define(
                resolver.scopes.module_scope,
                name,
                def_id,
                Visibility::Public,
                false, // Functions are not mutable
                rv_span::FileSpan {
                    file: rv_span::FileId(0),
                    span: rv_span::Span::new(0, 0),
                },
            ) {
                Ok(()) => {}
                Err(ResolutionError::DuplicateDefinition { .. }) => {
                    // Expected when a function appears in both available_functions
                    // and the current scope (e.g., recursive calls)
                }
                Err(other) => {
                    panic!(
                        "ICE: Unexpected error registering function in module scope: {:?}",
                        other
                    );
                }
            }
        }

        // Create function scope
        let function_scope = resolver
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

    /// Entry point for name resolution with module-level resolution support
    ///
    /// This method uses the `ModuleResolver` to resolve names that are:
    /// - Imported via `use` declarations
    /// - Defined in the same module
    /// - Accessible through module paths
    ///
    /// # Parameters
    /// - `body`: The function body to resolve
    /// - `function`: The function definition
    /// - `interner`: String interner for name lookups
    /// - `module_resolver`: Module-level resolver for cross-file resolution
    /// - `module_id`: The module containing this function
    pub fn resolve_with_modules(
        body: &'a Body,
        function: &'a Function,
        interner: &'a Interner,
        module_resolver: &'a ModuleResolver,
        module_id: ModuleId,
    ) -> ResolutionResult {
        let mut resolver = Self::new_with_modules(body, function, interner, module_resolver, module_id);

        // Register all items from the module's scope (exports + imports) in the resolver's module scope
        // This includes:
        // - Items defined in this module
        // - Items imported via `use` declarations
        if let Some(imports) = module_resolver.get_imports(module_id) {
            for (name, resolved) in imports {
                let def_id = resolved.def;
                if resolver.scopes.define(
                    resolver.scopes.module_scope,
                    *name,
                    def_id,
                    resolved.visibility,
                    false,
                    rv_span::FileSpan {
                        file: rv_span::FileId(0),
                        span: rv_span::Span::new(0, 0),
                    },
                ).is_err() {
                    // Duplicate definition from imports - this can happen with glob imports
                    // We silently ignore as the first import wins
                }
            }
        }

        // Also register exports from this module
        if let Some(exports) = module_resolver.get_exports(module_id) {
            for (name, resolved) in exports.functions.iter() {
                let def_id = DefId::Function(resolved.0);
                drop(resolver.scopes.define(
                    resolver.scopes.module_scope,
                    *name,
                    def_id,
                    resolved.1,
                    false,
                    rv_span::FileSpan {
                        file: rv_span::FileId(0),
                        span: rv_span::Span::new(0, 0),
                    },
                ));
            }
            for (name, resolved) in exports.structs.iter() {
                let def_id = DefId::Type(resolved.0);
                drop(resolver.scopes.define(
                    resolver.scopes.module_scope,
                    *name,
                    def_id,
                    resolved.1,
                    false,
                    rv_span::FileSpan {
                        file: rv_span::FileId(0),
                        span: rv_span::Span::new(0, 0),
                    },
                ));
            }
            for (name, resolved) in exports.enums.iter() {
                let def_id = DefId::Type(resolved.0);
                drop(resolver.scopes.define(
                    resolver.scopes.module_scope,
                    *name,
                    def_id,
                    resolved.1,
                    false,
                    rv_span::FileSpan {
                        file: rv_span::FileId(0),
                        span: rv_span::Span::new(0, 0),
                    },
                ));
            }
            for (name, resolved) in exports.traits.iter() {
                let def_id = DefId::Trait(resolved.0);
                drop(resolver.scopes.define(
                    resolver.scopes.module_scope,
                    *name,
                    def_id,
                    resolved.1,
                    false,
                    rv_span::FileSpan {
                        file: rv_span::FileId(0),
                        span: rv_span::Span::new(0, 0),
                    },
                ));
            }
        }

        // Create function scope
        let function_scope = resolver
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

    /// Resolve a qualified path (e.g., `module::item`)
    ///
    /// This uses the module resolver to look up items by path.
    /// Note: Currently unused but provides infrastructure for path-based resolution
    /// in expressions like `foo::bar::baz()`.
    #[expect(dead_code)]
    fn resolve_path(&self, path: &[Symbol], span: rv_span::FileSpan) -> Result<ResolvedImport, ResolutionError> {
        match (&self.module_resolver, &self.current_module) {
            (Some(resolver), Some(module_id)) => {
                resolver.resolve_path(*module_id, path, span)
            }
            _ => {
                // No module resolver available, try to resolve as a local name
                if path.len() == 1 {
                    match self.scopes.resolve(self.current_scope, path[0], span, self.interner) {
                        Ok(resolution) => Ok(ResolvedImport {
                            def: resolution.def,
                            visibility: Visibility::Public,
                            kind: ImportKind::Function, // Best guess
                        }),
                        Err(e) => Err(e),
                    }
                } else {
                    Err(ResolutionError::Undefined {
                        name: path[0],
                        use_site: span,
                        suggestions: vec![],
                    })
                }
            }
        }
    }

    /// Define function parameters in the function scope
    fn define_function_parameters(&mut self) {
        for param in &self.function.parameters {
            let local_id = LocalId(self.next_local_id);
            self.next_local_id += 1;

            let def_id = DefId::Local {
                func: self.function.id,
                local: local_id,
            };

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
                // Resolve variable to definition (parameters, let bindings, functions)
                match self
                    .scopes
                    .resolve(self.current_scope, name, span, self.interner)
                {
                    Ok(resolution) => {
                        self.resolutions.insert(expr_id, resolution.def);
                    }
                    Err(error) => {
                        // Resolution failed - report error
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

            Expr::PathCall { args, .. } => {
                // Resolve arguments (path resolution is handled separately)
                for arg in args {
                    self.resolve_expr(arg);
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
                    let def_id = DefId::Local {
                        func: self.function.id,
                        local: local_id,
                    };

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

            Expr::Assign { target, value, .. } => {
                self.resolve_expr(target);
                self.resolve_expr(value);
            }

            Expr::CompoundAssign { target, value, .. } => {
                self.resolve_expr(target);
                self.resolve_expr(value);
            }

            Expr::WhileLoop { condition, body, .. } => {
                self.resolve_expr(condition);
                self.resolve_expr(body);
            }

            Expr::Loop { body, .. } => {
                self.resolve_expr(body);
            }

            Expr::Break { value, .. } => {
                if let Some(val) = value {
                    self.resolve_expr(val);
                }
            }

            Expr::Continue { .. } => {
                // Nothing to resolve
            }

            Expr::Array { elements, .. } => {
                for elem in elements {
                    self.resolve_expr(elem);
                }
            }

            Expr::Tuple { elements, .. } => {
                for elem in elements {
                    self.resolve_expr(elem);
                }
            }

            Expr::Index { base, index, .. } => {
                self.resolve_expr(base);
                self.resolve_expr(index);
            }

            Expr::Cast { expr, .. } => {
                self.resolve_expr(expr);
            }

            Expr::Literal { .. } => {
                // Literals have no names to resolve
            }
            Expr::UnsafeBlock { body, .. } => {
                self.resolve_expr(body);
            }
            Expr::Error { .. } => {
                // Error expressions have no names to resolve
            }
            Expr::WhileLet { pattern, value, body, .. } => {
                self.resolve_expr(value);
                // Create scope for the pattern bindings
                let let_scope = self.scopes.create_child(self.current_scope, ScopeKind::Block);
                let previous_scope = self.current_scope;
                self.current_scope = let_scope;
                self.define_pattern_bindings(pattern, false);
                self.resolve_expr(body);
                self.current_scope = previous_scope;
            }
            Expr::IfLet { pattern, value, then_branch, else_branch, .. } => {
                self.resolve_expr(value);
                // Create scope for the pattern bindings in the then branch
                let let_scope = self.scopes.create_child(self.current_scope, ScopeKind::Block);
                let previous_scope = self.current_scope;
                self.current_scope = let_scope;
                self.define_pattern_bindings(pattern, false);
                self.resolve_expr(then_branch);
                self.current_scope = previous_scope;
                // Else branch doesn't have the pattern bindings
                if let Some(else_expr) = else_branch {
                    self.resolve_expr(else_expr);
                }
            }
            Expr::Range { start, end, .. } => {
                if let Some(s) = start {
                    self.resolve_expr(s);
                }
                if let Some(e) = end {
                    self.resolve_expr(e);
                }
            }
            Expr::Try { expr, .. } => {
                self.resolve_expr(expr);
            }
            Expr::ForLoop { pattern, iterator, body, .. } => {
                self.resolve_expr(iterator);
                // Create scope for the pattern bindings
                let loop_scope = self.scopes.create_child(self.current_scope, ScopeKind::Block);
                let previous_scope = self.current_scope;
                self.current_scope = loop_scope;
                self.define_pattern_bindings(pattern, false);
                self.resolve_expr(body);
                self.current_scope = previous_scope;
            }
            Expr::Box { value, .. } => {
                self.resolve_expr(value);
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
            Stmt::Box { value, .. } => {
                self.resolve_expr(value);
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
                let def_id = DefId::Local {
                    func: self.function.id,
                    local: local_id,
                };

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

            Pattern::Slice {
                prefix,
                rest,
                suffix,
                ..
            } => {
                // Recurse on slice pattern elements
                for sub_pattern in prefix {
                    self.define_pattern_bindings(sub_pattern, mutable);
                }
                if let Some(rest_pattern) = rest {
                    self.define_pattern_bindings(rest_pattern, mutable);
                }
                for sub_pattern in suffix {
                    self.define_pattern_bindings(sub_pattern, mutable);
                }
            }
        }
    }
}
