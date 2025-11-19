//! Type inference
#![allow(
    clippy::min_ident_chars,
    reason = "Ty and TyId are conventional names in type system implementations"
)]

use crate::bounds::{BoundChecker, BoundError};
use crate::constraint::{ConstraintSource, Constraints};
use crate::context::TyContext;
use crate::module_context::ModuleTypeContext;
use crate::ty::{TyId, TyKind};
use crate::unify::{UnificationError, Unifier};
use rv_hir::{Body, Expr, ExprId, Function, LiteralKind, Stmt, StmtId, TraitDef, TraitId};

/// Type inference result
pub struct InferenceResult {
    /// Type context with inferred types
    pub ctx: TyContext,
    /// Errors encountered during inference
    pub errors: Vec<TypeError>,
}

/// Type error
#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    /// Unification error
    Unification {
        /// Unification error
        error: UnificationError,
        /// Expression where error occurred
        expr: Option<ExprId>,
    },
    /// Undefined variable
    UndefinedVariable {
        /// Expression
        expr: ExprId,
    },
    /// Trait bound not satisfied
    BoundError {
        /// The bound error details
        error: BoundError,
        /// Expression where error occurred
        expr: Option<ExprId>,
    },
}

/// Type inference engine
pub struct TypeInference<'a> {
    ctx: TyContext,
    errors: Vec<TypeError>,
    /// Stack of scopes, each mapping variable names to their inferred types
    /// Inner scopes shadow outer scopes
    scope_stack: Vec<rustc_hash::FxHashMap<rv_intern::Symbol, TyId>>,
    /// Reference to impl blocks for method resolution
    impl_blocks: Option<&'a std::collections::HashMap<rv_hir::ImplId, rv_hir::ImplBlock>>,
    /// Reference to functions for method resolution
    functions: Option<&'a std::collections::HashMap<rv_hir::FunctionId, rv_hir::Function>>,
    /// Reference to HIR types for type conversion
    hir_types: Option<&'a la_arena::Arena<rv_hir::Type>>,
    /// Reference to struct definitions for type conversion
    structs: Option<&'a std::collections::HashMap<rv_hir::TypeDefId, rv_hir::StructDef>>,
    /// Reference to enum definitions for variant type lookup
    enums: Option<&'a std::collections::HashMap<rv_hir::TypeDefId, rv_hir::EnumDef>>,
    /// Reference to trait definitions for bound checking
    #[allow(dead_code, reason = "Will be used for bound checking at monomorphization time")]
    traits: Option<&'a std::collections::HashMap<TraitId, TraitDef>>,
    /// Reference to interner for resolving type names
    interner: Option<&'a rv_intern::Interner>,
    /// Cache for HIR TypeId → TyId conversions to prevent infinite recursion
    type_conversion_cache: rustc_hash::FxHashMap<rv_hir::TypeId, TyId>,
    /// Bound checker for validating trait constraints (created once we have all context)
    #[allow(dead_code, reason = "Will be used for bound checking at monomorphization time")]
    bound_checker: Option<BoundChecker>,
    /// Expected return type for the current function being inferred
    current_function_return_ty: Option<TyId>,
    /// Stack tracking variable mutability (variable name → is_mutable)
    var_mutability: Vec<rustc_hash::FxHashMap<rv_intern::Symbol, bool>>,
    /// Receiver mutability for method calls (ExprId → is_mutable)
    receiver_mutability: rustc_hash::FxHashMap<ExprId, bool>,
    /// Constraint generation mode (generate constraints instead of immediate unification)
    generate_mode: bool,
    /// Constraints collected during constraint generation mode
    constraints: Constraints,
    /// Reference to module context for constraint generation
    module_ctx: Option<&'a mut ModuleTypeContext>,
}

impl<'a> TypeInference<'a> {
    /// Create a new type inference engine
    pub fn new() -> Self {
        Self {
            ctx: TyContext::new(),
            errors: vec![],
            scope_stack: vec![rustc_hash::FxHashMap::default()], // Start with one global scope
            impl_blocks: None,
            functions: None,
            hir_types: None,
            structs: None,
            enums: None,
            traits: None,
            interner: None,
            type_conversion_cache: rustc_hash::FxHashMap::default(),
            bound_checker: None,
            current_function_return_ty: None,
            var_mutability: vec![rustc_hash::FxHashMap::default()],
            receiver_mutability: rustc_hash::FxHashMap::default(),
            generate_mode: false,
            constraints: Constraints::new(),
            module_ctx: None,
        }
    }

    /// Create a new type inference engine with HIR context for method resolution
    pub fn with_hir_context(
        impl_blocks: &'a std::collections::HashMap<rv_hir::ImplId, rv_hir::ImplBlock>,
        functions: &'a std::collections::HashMap<rv_hir::FunctionId, rv_hir::Function>,
        hir_types: &'a la_arena::Arena<rv_hir::Type>,
        structs: &'a std::collections::HashMap<rv_hir::TypeDefId, rv_hir::StructDef>,
        enums: &'a std::collections::HashMap<rv_hir::TypeDefId, rv_hir::EnumDef>,
        traits: &'a std::collections::HashMap<TraitId, TraitDef>,
        interner: &'a rv_intern::Interner,
    ) -> Self {
        // Create bound checker with trait and impl information
        let bound_checker = BoundChecker::new(
            traits.clone(),
            impl_blocks,
            hir_types.clone(),
        );

        Self {
            ctx: TyContext::new(),
            errors: vec![],
            scope_stack: vec![rustc_hash::FxHashMap::default()], // Start with one global scope
            impl_blocks: Some(impl_blocks),
            functions: Some(functions),
            hir_types: Some(hir_types),
            structs: Some(structs),
            enums: Some(enums),
            traits: Some(traits),
            interner: Some(interner),
            type_conversion_cache: rustc_hash::FxHashMap::default(),
            bound_checker: Some(bound_checker),
            current_function_return_ty: None,
            var_mutability: vec![rustc_hash::FxHashMap::default()],
            receiver_mutability: rustc_hash::FxHashMap::default(),
            generate_mode: false,
            constraints: Constraints::new(),
            module_ctx: None,
        }
    }

    /// Enable constraint generation mode
    pub fn enable_constraint_generation(&mut self, module_ctx: &'a mut ModuleTypeContext) {
        self.generate_mode = true;
        self.module_ctx = Some(module_ctx);
    }

    /// Get the collected constraints
    #[must_use]
    pub fn take_constraints(&mut self) -> Constraints {
        std::mem::take(&mut self.constraints)
    }

    /// Get the type context
    #[must_use]
    pub fn context(&self) -> &TyContext {
        &self.ctx
    }

    /// Get a mutable reference to the type context
    #[must_use]
    pub fn context_mut(&mut self) -> &mut TyContext {
        &mut self.ctx
    }

    /// Bind a variable name to a concrete type in the global scope
    /// This is used for monomorphization to bind generic type parameters to concrete types
    pub fn bind_type_in_global_scope(&mut self, name: rv_intern::Symbol, ty: TyId) {
        if let Some(global_scope) = self.scope_stack.first_mut() {
            global_scope.insert(name, ty);
        }
    }

    /// Push a new scope onto the scope stack
    fn push_scope(&mut self) {
        self.scope_stack.push(rustc_hash::FxHashMap::default());
        self.var_mutability.push(rustc_hash::FxHashMap::default());
    }

    /// Pop the current scope from the scope stack
    fn pop_scope(&mut self) {
        if self.scope_stack.len() > 1 {
            self.scope_stack.pop();
            self.var_mutability.pop();
        }
    }

    /// Insert a variable into the current scope
    fn insert_var(&mut self, name: rv_intern::Symbol, ty: TyId) {
        if let Some(current_scope) = self.scope_stack.last_mut() {
            current_scope.insert(name, ty);
        }
    }

    /// Look up a variable by name, searching from innermost to outermost scope
    fn lookup_var(&self, name: rv_intern::Symbol) -> Option<TyId> {
        // Search from innermost scope (last in vec) to outermost (first in vec)
        for scope in self.scope_stack.iter().rev() {
            if let Some(&ty) = scope.get(&name) {
                return Some(ty);
            }
        }
        None
    }

    /// Insert variable mutability into the current scope
    fn insert_var_mutability(&mut self, name: rv_intern::Symbol, is_mutable: bool) {
        if let Some(current_scope) = self.var_mutability.last_mut() {
            current_scope.insert(name, is_mutable);
        }
    }

    /// Check if a local variable is mutable
    fn is_local_mutable(&self, name: rv_intern::Symbol) -> bool {
        // Search from innermost scope to outermost
        for scope in self.var_mutability.iter().rev() {
            if let Some(&is_mut) = scope.get(&name) {
                return is_mut;
            }
        }
        false // Default to immutable if not found
    }

    /// Recursively check if an expression is mutable
    fn is_expr_mutable(&self, body: &Body, expr_id: ExprId) -> bool {
        let expr = &body.exprs[expr_id];

        match expr {
            Expr::Variable { name, .. } => {
                // Check if the variable was declared mutable
                self.is_local_mutable(*name)
            }
            Expr::Field { base, .. } => {
                // Field access is mutable if base is mutable
                self.is_expr_mutable(body, *base)
            }
            _ => {
                // Other expressions (temporaries, literals) are not mutable
                false
            }
        }
    }

    /// Clear expression types (used between functions to avoid ExprId conflicts)
    pub fn clear_expr_types(&mut self) {
        self.ctx.expr_types.clear();
    }

    /// Infer types for a function
    pub fn infer_function(&mut self, function: &Function) {
        // Set expected return type
        self.current_function_return_ty = function.return_type.and_then(|return_ty_id| {
            if let (Some(hir_types), Some(structs), Some(interner)) =
                (self.hir_types, self.structs, self.interner)
            {
                Some(self.hir_type_to_ty_id(return_ty_id, hir_types, structs, interner))
            } else {
                None
            }
        });

        // Initialize parameter types from HIR type annotations using resolution results
        if function.body.resolution.is_some() {
            // Use resolved LocalIds from name resolution
            for (param_idx, param) in function.parameters.iter().enumerate() {
                // Convert HIR TypeId to inference TyId
                let param_ty = if let (Some(hir_types), Some(structs), Some(interner)) =
                    (self.hir_types, self.structs, self.interner)
                {
                    self.hir_type_to_ty_id(param.ty, hir_types, structs, interner)
                } else {
                    // Fallback to fresh type variable if no HIR context
                    self.ctx.fresh_ty_var()
                };

                // Store type by LocalId (from resolution) instead of by name
                let local_id = rv_hir::LocalId(param_idx as u32);
                let def_id = rv_hir::DefId::Local(local_id);
                self.ctx.set_def_type(def_id, param_ty);

                // Keep name-based lookup for backward compatibility
                self.insert_var(param.name, param_ty);
                self.ctx.var_types.insert(param.name, param_ty);
            }
        } else {
            // Fallback: old behavior if no resolution available
            for param in &function.parameters {
                let param_ty = if let (Some(hir_types), Some(structs), Some(interner)) =
                    (self.hir_types, self.structs, self.interner)
                {
                    self.hir_type_to_ty_id(param.ty, hir_types, structs, interner)
                } else {
                    self.ctx.fresh_ty_var()
                };

                self.insert_var(param.name, param_ty);
                self.ctx.var_types.insert(param.name, param_ty);
            }
        }

        // Infer body
        self.infer_body(&function.body);

        // Clear expected return type after function
        self.current_function_return_ty = None;
    }

    /// Convert HIR TypeId to type inference TyId
    fn hir_type_to_ty_id(
        &mut self,
        hir_ty_id: rv_hir::TypeId,
        hir_types: &la_arena::Arena<rv_hir::Type>,
        structs: &std::collections::HashMap<rv_hir::TypeDefId, rv_hir::StructDef>,
        interner: &rv_intern::Interner,
    ) -> TyId {
        self.hir_type_to_ty_id_impl(hir_ty_id, hir_types, structs, interner, 0)
    }

    fn hir_type_to_ty_id_impl(
        &mut self,
        hir_ty_id: rv_hir::TypeId,
        hir_types: &la_arena::Arena<rv_hir::Type>,
        structs: &std::collections::HashMap<rv_hir::TypeDefId, rv_hir::StructDef>,
        interner: &rv_intern::Interner,
        depth: usize,
    ) -> TyId {
        // Prevent infinite recursion with depth limit
        if depth > 50 {
            // Too deep - likely a cycle, return a type variable
            return self.ctx.fresh_ty_var();
        }

        // Check cache first to prevent redundant conversions
        if let Some(&cached_ty) = self.type_conversion_cache.get(&hir_ty_id) {
            return cached_ty;
        }

        let hir_type = &hir_types[hir_ty_id];

        let result_ty = match hir_type {
            rv_hir::Type::Named { name, def, .. } => {
                // If it's a struct with resolved definition, create proper struct type
                if let Some(type_def_id) = def {
                    if let Some(struct_def) = structs.get(type_def_id) {
                        // Create struct type with fields
                        let field_types: Vec<(rv_intern::Symbol, TyId)> = struct_def
                            .fields
                            .iter()
                            .map(|field| {
                                let field_ty = self.hir_type_to_ty_id_impl(field.ty, hir_types, structs, interner, depth + 1);
                                (field.name, field_ty)
                            })
                            .collect();

                        self.ctx.types.alloc(TyKind::Struct {
                            def_id: *type_def_id,
                            fields: field_types,
                        })
                    } else {
                        // Struct definition not found, use type variable
                        self.ctx.fresh_ty_var()
                    }
                } else {
                    // Check if it's a primitive type
                    let type_name = interner.resolve(name);
                    match type_name.as_str() {
                        "i64" | "i32" | "int" => self.ctx.types.int(),
                        "f64" | "f32" | "float" => self.ctx.types.float(),
                        "bool" => self.ctx.types.bool(),
                        "str" | "String" => self.ctx.types.string(),
                        "()" => self.ctx.types.unit(),
                        _ => {
                            // Unknown named type, use type variable
                            self.ctx.fresh_ty_var()
                        }
                    }
                }
            }

            rv_hir::Type::Generic { .. } => {
                // Generic type parameters become type variables
                self.ctx.fresh_ty_var()
            }

            rv_hir::Type::Function { params, ret, .. } => {
                let param_tys: Vec<TyId> = params
                    .iter()
                    .map(|p| self.hir_type_to_ty_id_impl(*p, hir_types, structs, interner, depth + 1))
                    .collect();
                let ret_ty = self.hir_type_to_ty_id_impl(**ret, hir_types, structs, interner, depth + 1);

                self.ctx.types.alloc(TyKind::Function {
                    params: param_tys,
                    ret: Box::new(ret_ty),
                })
            }

            rv_hir::Type::Tuple { elements, .. } => {
                let elem_tys: Vec<TyId> = elements
                    .iter()
                    .map(|e| self.hir_type_to_ty_id_impl(*e, hir_types, structs, interner, depth + 1))
                    .collect();

                self.ctx.types.alloc(TyKind::Tuple {
                    elements: elem_tys,
                })
            }

            // Fallback for other type kinds
            _ => self.ctx.fresh_ty_var(),
        };

        // Update cache with the computed type
        self.type_conversion_cache.insert(hir_ty_id, result_ty);
        result_ty
    }

    /// Infer types for a function body
    fn infer_body(&mut self, body: &Body) {
        // Infer root expression with expected return type
        let expected = self.current_function_return_ty;
        self.infer_expr(body, body.root_expr, expected);
    }

    /// Check trait bounds for a generic parameter usage
    /// This checks that a type satisfies the trait bounds declared on a generic parameter
    #[allow(dead_code, reason = "Will be called during monomorphization-time bound checking")]
    fn check_generic_param_bounds(
        &mut self,
        type_def_id: rv_hir::TypeDefId,
        generic_param: &rv_hir::GenericParam,
        expr_id: ExprId,
    ) {
        // Only check if we have a bound checker
        let Some(bound_checker) = &self.bound_checker else {
            return;
        };

        // Check all bounds on this generic parameter
        let errors = bound_checker.check_generic_bounds(type_def_id, generic_param);
        for error in errors {
            self.errors.push(TypeError::BoundError {
                error,
                expr: Some(expr_id),
            });
        }
    }

    /// Infer type of an expression
    ///
    /// # Parameters
    /// - `body`: The function body containing the expression
    /// - `expr_id`: The ID of the expression to infer
    /// - `expected`: Optional expected type (for bidirectional type flow)
    #[allow(clippy::too_many_lines, reason = "Type inference requires comprehensive pattern matching")]
    fn infer_expr(&mut self, body: &Body, expr_id: ExprId, expected: Option<TyId>) -> TyId {
        let expr = &body.exprs[expr_id];

        let inferred_ty = match expr {
            Expr::Literal { kind, .. } => self.infer_literal(kind),

            Expr::Variable { name, def, .. } => {
                // Prefer using resolved DefId from name resolution
                let result_ty = if let Some(def_id) = def {
                    // Look up definition type by DefId
                    if let Some(def_ty) = self.ctx.get_def_type(*def_id) {
                        def_ty
                    } else {
                        // DefId not yet typed, try name-based lookup (for parameters)
                        if let Some(var_ty) = self.lookup_var(*name) {
                            var_ty
                        } else {
                            // Unknown definition, create fresh variable
                            self.ctx.fresh_ty_var()
                        }
                    }
                } else if let Some(var_ty) = self.lookup_var(*name) {
                    // Fallback to name-based lookup if no DefId (old behavior)
                    var_ty
                } else {
                    // Unresolved variable - name resolution should have caught this
                    self.errors.push(TypeError::UndefinedVariable { expr: expr_id });
                    self.ctx.types.error()
                };

                result_ty
            }

            Expr::Call { callee, args, .. } => {
                // Infer callee type (no expected type for callee)
                let callee_ty = self.infer_expr(body, *callee, None);

                // Extract parameter types from callee to pass as expected types to arguments
                let callee_ty_normalized = self.ctx.types.get(callee_ty);
                let param_expected_types = if let TyKind::Function { params, .. } = &callee_ty_normalized.kind {
                    params.clone()
                } else {
                    vec![]
                };

                // Infer argument types with expected types from function signature
                let arg_tys: Vec<_> = args.iter().enumerate().map(|(idx, arg)| {
                    let expected_arg_ty = param_expected_types.get(idx).copied();
                    self.infer_expr(body, *arg, expected_arg_ty)
                }).collect();

                // Create fresh type variable for return type
                let ret_ty = self.ctx.fresh_ty_var();

                // Unify callee with function type
                let func_ty = self.ctx.types.alloc(TyKind::Function {
                    params: arg_tys,
                    ret: Box::new(ret_ty),
                });

                if self.generate_mode {
                    // Generate constraint instead of immediate unification
                    let source = ConstraintSource::new(
                        rv_span::FileId(0),
                        rv_span::Span::new(0, 0),
                        "function call".to_string(),
                    );
                    self.constraints.add_equality(callee_ty, func_ty, source);
                } else if let Err(error) = Unifier::new(&mut self.ctx).unify(callee_ty, func_ty) {
                    self.errors.push(TypeError::Unification {
                        error,
                        expr: Some(expr_id),
                    });
                }

                ret_ty
            }

            Expr::BinaryOp { op, left, right, .. } => {
                // Infer left operand first (no expected type)
                let left_ty = self.infer_expr(body, *left, None);

                // Right operand should match left operand type
                let right_ty = self.infer_expr(body, *right, Some(left_ty));

                // Unify both operands to ensure they have the same type
                if self.generate_mode {
                    // Generate constraint instead of immediate unification
                    let source = ConstraintSource::binary_op(
                        rv_span::FileId(0), // TODO: get from expr span
                        rv_span::Span::new(0, 0), // TODO: get from expr span
                        &format!("{op:?}"),
                    );
                    self.constraints.add_equality(left_ty, right_ty, source);
                } else if let Err(error) = Unifier::new(&mut self.ctx).unify(left_ty, right_ty) {
                    self.errors.push(TypeError::Unification {
                        error,
                        expr: Some(expr_id),
                    });
                }

                // Comparison and logical operators return Bool, others return operand type
                match op {
                    rv_hir::BinaryOp::Eq | rv_hir::BinaryOp::Ne
                    | rv_hir::BinaryOp::Lt | rv_hir::BinaryOp::Le
                    | rv_hir::BinaryOp::Gt | rv_hir::BinaryOp::Ge
                    | rv_hir::BinaryOp::And | rv_hir::BinaryOp::Or => {
                        self.ctx.types.bool()
                    }
                    _ => left_ty
                }
            }

            Expr::UnaryOp { operand, .. } => {
                // Unary op returns same type as operand
                // Pass expected type down to operand
                self.infer_expr(body, *operand, expected)
            }

            Expr::Block { statements, expr, .. } => {
                // Push a new scope for the block
                self.push_scope();

                // Infer statement types
                for stmt_id in statements {
                    self.infer_stmt(body, *stmt_id);
                }

                // Block type is trailing expression type or unit
                // Pass expected type down to trailing expression
                let block_ty = if let Some(trailing) = expr {
                    self.infer_expr(body, *trailing, expected)
                } else {
                    self.ctx.types.unit()
                };

                // Pop the block scope
                self.pop_scope();

                block_ty
            }

            Expr::If { condition, then_branch, else_branch, .. } => {
                // Condition must be bool (no expected type for condition)
                let cond_ty = self.infer_expr(body, *condition, None);
                let bool_ty = self.ctx.types.bool();

                if self.generate_mode {
                    let source = ConstraintSource::new(
                        rv_span::FileId(0),
                        rv_span::Span::new(0, 0),
                        "if condition".to_string(),
                    );
                    self.constraints.add_equality(cond_ty, bool_ty, source);
                } else if let Err(error) = Unifier::new(&mut self.ctx).unify(cond_ty, bool_ty) {
                    self.errors.push(TypeError::Unification {
                        error,
                        expr: Some(*condition),
                    });
                }

                // Both branches should have the expected type
                let then_ty = self.infer_expr(body, *then_branch, expected);

                if let Some(else_expr) = else_branch {
                    let else_ty = self.infer_expr(body, *else_expr, expected);

                    if self.generate_mode {
                        let source = ConstraintSource::new(
                            rv_span::FileId(0),
                            rv_span::Span::new(0, 0),
                            "if branches".to_string(),
                        );
                        self.constraints.add_equality(then_ty, else_ty, source);
                    } else if let Err(error) = Unifier::new(&mut self.ctx).unify(then_ty, else_ty) {
                        self.errors.push(TypeError::Unification {
                            error,
                            expr: Some(expr_id),
                        });
                    }

                    then_ty
                } else {
                    // No else branch, result is unit
                    self.ctx.types.unit()
                }
            }

            Expr::Match { scrutinee, arms, .. } => {
                // Infer scrutinee type (no expected type for scrutinee)
                let _scrutinee_ty = self.infer_expr(body, *scrutinee, None);

                // All arms should produce the expected type
                // Use expected type as the initial result type if provided
                let mut result_ty = expected;

                #[allow(clippy::excessive_nesting, reason = "Match arm unification requires nested checks")]
                for arm in arms {
                    // Pass expected type down to each arm body
                    let arm_ty = self.infer_expr(body, arm.body, expected);

                    result_ty = if let Some(expected_arm_ty) = result_ty {
                        if self.generate_mode {
                            let source = ConstraintSource::new(
                                rv_span::FileId(0),
                                rv_span::Span::new(0, 0),
                                "match arms".to_string(),
                            );
                            self.constraints.add_equality(expected_arm_ty, arm_ty, source);
                        } else if let Err(error) = Unifier::new(&mut self.ctx).unify(expected_arm_ty, arm_ty) {
                            self.errors.push(TypeError::Unification {
                                error,
                                expr: Some(arm.body),
                            });
                        }
                        Some(expected_arm_ty)
                    } else {
                        Some(arm_ty)
                    };
                }

                result_ty.unwrap_or_else(|| self.ctx.types.never())
            }

            Expr::Field { base, field, .. } => {
                // Infer base type (no expected type for base)
                let base_ty = self.infer_expr(body, *base, None);

                // Look up the field type from the struct DEFINITION, not the inferred type
                // This ensures we get concrete types, not type variables from struct construction
                let base_ty_kind = &self.ctx.types.get(base_ty).kind;
                match base_ty_kind {
                    TyKind::Struct { def_id, .. } => {
                        // Look up the struct definition to get field types
                        if let Some(structs) = self.structs {
                            if let Some(struct_def) = structs.get(def_id) {
                                // Find the field in the struct definition
                                if let Some(field_def) = struct_def.fields.iter().find(|f| f.name == *field) {
                                    // Convert HIR TypeId to TyId
                                    if let (Some(hir_types), Some(interner)) = (self.hir_types, self.interner) {
                                        self.hir_type_to_ty_id(field_def.ty, hir_types, structs, interner)
                                    } else {
                                        self.ctx.fresh_ty_var()
                                    }
                                } else {
                                    // Field not found in struct definition
                                    self.ctx.fresh_ty_var()
                                }
                            } else {
                                // Struct definition not found
                                self.ctx.fresh_ty_var()
                            }
                        } else {
                            // No struct context available
                            self.ctx.fresh_ty_var()
                        }
                    }
                    _ => {
                        // Not a struct type, return type variable
                        self.ctx.fresh_ty_var()
                    }
                }
            }

            Expr::MethodCall { receiver, method, args, .. } => {
                // Infer receiver type (no expected type for receiver)
                let receiver_ty = self.infer_expr(body, *receiver, None);

                // Check receiver mutability and store it for MIR lowering
                let receiver_is_mutable = self.is_expr_mutable(body, *receiver);
                self.receiver_mutability.insert(expr_id, receiver_is_mutable);

                // Infer argument types (no expected types for now - could be improved)
                for arg in args {
                    self.infer_expr(body, *arg, None);
                }

                // Look up the method return type from impl blocks
                let receiver_ty_kind = &self.ctx.types.get(receiver_ty).kind;
                let type_def_id = match receiver_ty_kind {
                    TyKind::Struct { def_id, .. } => Some(*def_id),
                    _ => None,
                };

                // Try to find the method and get its return type
                let method_return_ty = if let (Some(impl_blocks), Some(functions), Some(def_id)) =
                    (self.impl_blocks, self.functions, type_def_id)
                {
                    let mut found_ty = None;
                    // Find impl blocks for this type
                    'outer: for impl_block in impl_blocks.values() {
                        if impl_block.self_ty == rv_hir::TypeId::from_raw(la_arena::RawIdx::from(def_id.0)) {
                            // Check methods in this impl block
                            for &func_id in &impl_block.methods {
                                if let Some(func) = functions.get(&func_id) {
                                    if func.name == *method {
                                        // Found the method! Use its return type
                                        if let Some(return_type_id) = func.return_type {
                                            // Convert HIR TypeId to inference TyId
                                            if let (Some(hir_types), Some(structs), Some(interner)) =
                                                (self.hir_types, self.structs, self.interner)
                                            {
                                                found_ty = Some(self.hir_type_to_ty_id(
                                                    return_type_id,
                                                    hir_types,
                                                    structs,
                                                    interner,
                                                ));
                                            }
                                        } else {
                                            found_ty = Some(self.ctx.fresh_ty_var());
                                        }
                                        break 'outer;
                                    }
                                }
                            }
                        }
                    }
                    found_ty
                } else {
                    None
                };

                // Return the method type or a fresh type variable if not found
                method_return_ty.unwrap_or_else(|| self.ctx.fresh_ty_var())
            }

            Expr::StructConstruct { def, fields, .. } => {
                // Create struct type if we have a type definition
                if let Some(type_def_id) = def {
                    // Look up the struct definition to get declared field types
                    if let Some(structs) = self.structs {
                        if let Some(struct_def) = structs.get(type_def_id) {
                            // Build field types from the struct definition
                            let mut field_tys: Vec<(rv_intern::Symbol, TyId)> = Vec::new();

                            for (field_name, field_expr) in fields {
                                // Look up the declared field type in the struct definition
                                let declared_ty = if let Some(field_def) = struct_def.fields.iter().find(|f| f.name == *field_name) {
                                    // Convert HIR TypeId to inference TyId
                                    if let (Some(hir_types), Some(interner)) = (self.hir_types, self.interner) {
                                        self.hir_type_to_ty_id(field_def.ty, hir_types, structs, interner)
                                    } else {
                                        self.ctx.fresh_ty_var()
                                    }
                                } else {
                                    self.ctx.fresh_ty_var()
                                };

                                // Infer the expression type with expected type from field declaration
                                let expr_ty = self.infer_expr(body, *field_expr, Some(declared_ty));

                                // Unify expression type with declared type
                                if self.generate_mode {
                                    let source = ConstraintSource::new(
                                        rv_span::FileId(0),
                                        rv_span::Span::new(0, 0),
                                        format!("struct field '{field_name:?}'"),
                                    );
                                    self.constraints.add_equality(expr_ty, declared_ty, source);
                                } else if let Err(error) = Unifier::new(&mut self.ctx).unify(expr_ty, declared_ty) {
                                    self.errors.push(TypeError::Unification {
                                        error,
                                        expr: Some(*field_expr),
                                    });
                                }

                                // After unification, follow the substitution chain to get the most resolved type
                                // Prefer expr_ty since it comes from actual expression inference
                                let field_ty = self.ctx.follow_var(expr_ty);
                                field_tys.push((*field_name, field_ty));
                            }

                            return self.ctx.types.alloc(TyKind::Struct {
                                def_id: *type_def_id,
                                fields: field_tys,
                            });
                        }
                    }

                    // Fallback: infer field types from expressions if struct def not available
                    let field_tys: Vec<(rv_intern::Symbol, TyId)> = fields
                        .iter()
                        .map(|(name, field_expr)| {
                            let ty = self.infer_expr(body, *field_expr, None);
                            (*name, ty)
                        })
                        .collect();

                    self.ctx.types.alloc(TyKind::Struct {
                        def_id: *type_def_id,
                        fields: field_tys,
                    })
                } else {
                    // No type definition resolved, create type variable
                    self.ctx.fresh_ty_var()
                }
            }

            Expr::EnumVariant { def, fields, .. } => {
                // Infer variant field types (no expected types for now - could be improved)
                for field_expr in fields {
                    self.infer_expr(body, *field_expr, None);
                }

                // Return a Named type referencing the enum if we have the type definition
                // Enums are nominal types, so we use Named with the TypeDefId
                if let Some(type_def_id) = def {
                    // Look up the enum name
                    if let Some(enums) = self.enums {
                        if let Some(enum_def) = enums.get(type_def_id) {
                            return self.ctx.types.alloc(TyKind::Named {
                                name: enum_def.name,
                                def: *type_def_id,
                                args: vec![],
                            });
                        }
                    }
                }

                // Fallback to type variable if enum def not resolved
                self.ctx.fresh_ty_var()
            }

            Expr::Closure { params, return_type, body: closure_body, captures, .. } => {
                // Push a new scope for the closure
                self.push_scope();

                // Infer parameter types - use annotations if available, otherwise create type variables
                let mut param_tys = vec![];
                for param in params {
                    let param_ty = if let (Some(hir_types), Some(structs), Some(interner)) =
                        (self.hir_types, self.structs, self.interner)
                    {
                        // Use annotated type if available
                        self.hir_type_to_ty_id(param.ty, hir_types, structs, interner)
                    } else {
                        // Create a fresh type variable for parameter
                        self.ctx.fresh_ty_var()
                    };

                    // Register parameter in current scope
                    self.insert_var(param.name, param_ty);
                    self.ctx.var_types.insert(param.name, param_ty);
                    param_tys.push(param_ty);
                }

                // Add captured variables to closure scope with their types from parent scope
                for capture in captures {
                    if let Some(capture_ty) = self.lookup_var(*capture) {
                        self.insert_var(*capture, capture_ty);
                    }
                }

                // Infer closure body with expected return type if annotated
                let expected_return_ty = return_type.and_then(|rt_id| {
                    if let (Some(hir_types), Some(structs), Some(interner)) =
                        (self.hir_types, self.structs, self.interner)
                    {
                        Some(self.hir_type_to_ty_id(rt_id, hir_types, structs, interner))
                    } else {
                        None
                    }
                });

                let body_ty = self.infer_expr(body, *closure_body, expected_return_ty);

                // Unify with expected return type if provided
                if let Some(expected_ret_ty) = expected_return_ty {
                    if self.generate_mode {
                        let source = ConstraintSource::return_type(
                            rv_span::FileId(0),
                            rv_span::Span::new(0, 0),
                        );
                        self.constraints.add_equality(body_ty, expected_ret_ty, source);
                    } else if let Err(error) = Unifier::new(&mut self.ctx).unify(body_ty, expected_ret_ty) {
                        self.errors.push(TypeError::Unification {
                            error,
                            expr: Some(*closure_body),
                        });
                    }
                }

                // Pop the closure scope
                self.pop_scope();

                // Create function type for the closure
                self.ctx.types.alloc(TyKind::Function {
                    params: param_tys,
                    ret: Box::new(body_ty),
                })
            }
        };

        // Bidirectional unification: unify inferred type with expected type
        if let Some(expected_ty) = expected {
            if self.generate_mode {
                let source = ConstraintSource::new(
                    rv_span::FileId(0),
                    rv_span::Span::new(0, 0),
                    "expected type".to_string(),
                );
                self.constraints.add_equality(inferred_ty, expected_ty, source);
            } else if let Err(error) = Unifier::new(&mut self.ctx).unify(inferred_ty, expected_ty) {
                self.errors.push(TypeError::Unification {
                    error,
                    expr: Some(expr_id),
                });
            }
        }

        // Record expression type
        self.ctx.set_expr_type(expr_id, inferred_ty);

        // Debug: log when storing types for Variable expressions
        inferred_ty
    }

    /// Infer type of a literal
    fn infer_literal(&mut self, kind: &LiteralKind) -> TyId {
        match kind {
            LiteralKind::Integer(_) => self.ctx.types.int(),
            LiteralKind::Float(_) => self.ctx.types.float(),
            LiteralKind::String(_) => self.ctx.types.string(),
            LiteralKind::Bool(_) => self.ctx.types.bool(),
            LiteralKind::Unit => self.ctx.types.unit(),
        }
    }

    /// Infer statement
    fn infer_stmt(&mut self, body: &Body, stmt_id: StmtId) {
        let stmt = &body.stmts[stmt_id];

        match stmt {
            Stmt::Let { pattern, ty, initializer, mutable, .. } => {
                if let Some(init_expr) = initializer {
                    // If there's a type annotation, use it as expected type
                    let expected_ty = ty.and_then(|type_id| {
                        if let (Some(hir_types), Some(structs), Some(interner)) =
                            (self.hir_types, self.structs, self.interner)
                        {
                            Some(self.hir_type_to_ty_id(type_id, hir_types, structs, interner))
                        } else {
                            None
                        }
                    });

                    // Infer initializer with expected type from annotation
                    let init_ty = self.infer_expr(body, *init_expr, expected_ty);

                    // Record the type for the variable name in the current scope
                    let pat = &body.patterns[*pattern];
                    if let rv_hir::Pattern::Binding { name, mutable: pat_mutable, .. } = pat {
                        self.insert_var(*name, init_ty);
                        // Also store in context for MIR lowering
                        self.ctx.var_types.insert(*name, init_ty);
                        // Track variable mutability (from either let mut or pattern)
                        let is_mutable = *mutable || *pat_mutable;
                        self.insert_var_mutability(*name, is_mutable);
                    }
                }
            }

            Stmt::Expr { expr, .. } => {
                // Expression statements don't have expected types
                self.infer_expr(body, *expr, None);
            }

            Stmt::Return { value, .. } => {
                if let Some(val_expr) = value {
                    // Use function return type as expected type
                    let val_ty = self.infer_expr(body, *val_expr, self.current_function_return_ty);

                    // Unify with expected function return type
                    if let Some(expected_return_ty) = self.current_function_return_ty {
                        if self.generate_mode {
                            let source = ConstraintSource::return_type(
                                rv_span::FileId(0),
                                rv_span::Span::new(0, 0),
                            );
                            self.constraints.add_equality(val_ty, expected_return_ty, source);
                        } else {
                            let mut unifier = Unifier::new(&mut self.ctx);
                            if let Err(error) = unifier.unify(val_ty, expected_return_ty) {
                                self.errors.push(TypeError::Unification {
                                    error,
                                    expr: Some(*val_expr),
                                });
                            }
                        }
                    }
                }
            }
        }
    }

    /// Finish inference and return result
    pub fn finish(mut self) -> InferenceResult {
        // Transfer receiver mutability to context
        self.ctx.receiver_mutability = self.receiver_mutability;

        InferenceResult {
            ctx: self.ctx,
            errors: self.errors,
        }
    }
}

impl<'a> Default for TypeInference<'a> {
    fn default() -> Self {
        Self::new()
    }
}
