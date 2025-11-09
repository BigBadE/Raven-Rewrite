//! Type inference
#![allow(
    clippy::min_ident_chars,
    reason = "Ty and TyId are conventional names in type system implementations"
)]

use crate::context::TyContext;
use crate::ty::{TyId, TyKind};
use crate::unify::{UnificationError, Unifier};
use rv_hir::{Body, Expr, ExprId, Function, LiteralKind, Stmt, StmtId};

/// Type inference result
pub struct InferenceResult {
    /// Type context with inferred types
    pub ctx: TyContext,
    /// Errors encountered during inference
    pub errors: Vec<TypeError>,
}

/// Type error
#[derive(Debug, Clone)]
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
}

/// Type inference engine
pub struct TypeInference<'a> {
    ctx: TyContext,
    errors: Vec<TypeError>,
    /// Map from variable names to their inferred types
    var_types: rustc_hash::FxHashMap<rv_intern::Symbol, TyId>,
    /// Reference to impl blocks for method resolution
    impl_blocks: Option<&'a std::collections::HashMap<rv_hir::ImplId, rv_hir::ImplBlock>>,
    /// Reference to functions for method resolution
    functions: Option<&'a std::collections::HashMap<rv_hir::FunctionId, rv_hir::Function>>,
    /// Reference to HIR types for type conversion
    hir_types: Option<&'a la_arena::Arena<rv_hir::Type>>,
    /// Reference to struct definitions for type conversion
    structs: Option<&'a std::collections::HashMap<rv_hir::TypeDefId, rv_hir::StructDef>>,
    /// Reference to interner for resolving type names
    interner: Option<&'a rv_intern::Interner>,
    /// Cache for HIR TypeId → TyId conversions to prevent infinite recursion
    type_conversion_cache: rustc_hash::FxHashMap<rv_hir::TypeId, TyId>,
}

impl<'a> TypeInference<'a> {
    /// Create a new type inference engine
    pub fn new() -> Self {
        Self {
            ctx: TyContext::new(),
            errors: vec![],
            var_types: rustc_hash::FxHashMap::default(),
            impl_blocks: None,
            functions: None,
            hir_types: None,
            structs: None,
            interner: None,
            type_conversion_cache: rustc_hash::FxHashMap::default(),
        }
    }

    /// Create a new type inference engine with HIR context for method resolution
    pub fn with_hir_context(
        impl_blocks: &'a std::collections::HashMap<rv_hir::ImplId, rv_hir::ImplBlock>,
        functions: &'a std::collections::HashMap<rv_hir::FunctionId, rv_hir::Function>,
        hir_types: &'a la_arena::Arena<rv_hir::Type>,
        structs: &'a std::collections::HashMap<rv_hir::TypeDefId, rv_hir::StructDef>,
        interner: &'a rv_intern::Interner,
    ) -> Self {
        Self {
            ctx: TyContext::new(),
            errors: vec![],
            var_types: rustc_hash::FxHashMap::default(),
            impl_blocks: Some(impl_blocks),
            functions: Some(functions),
            hir_types: Some(hir_types),
            structs: Some(structs),
            interner: Some(interner),
            type_conversion_cache: rustc_hash::FxHashMap::default(),
        }
    }

    /// Get the type context
    #[must_use]
    pub fn context(&self) -> &TyContext {
        &self.ctx
    }

    /// Infer types for a function
    pub fn infer_function(&mut self, function: &Function) {
        // Initialize parameter types from HIR type annotations
        for param in &function.parameters {
            // Convert HIR TypeId to inference TyId
            let param_ty = if let (Some(hir_types), Some(structs), Some(interner)) =
                (self.hir_types, self.structs, self.interner)
            {
                self.hir_type_to_ty_id(param.ty, hir_types, structs, interner)
            } else {
                // Fallback to fresh type variable if no HIR context
                self.ctx.fresh_ty_var()
            };

            self.var_types.insert(param.name, param_ty);
            // Also store in context for MIR lowering
            self.ctx.var_types.insert(param.name, param_ty);
        }

        // Infer body
        self.infer_body(&function.body);
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
        // Check cache first to prevent infinite recursion from cyclic types
        if let Some(&cached_ty) = self.type_conversion_cache.get(&hir_ty_id) {
            return cached_ty;
        }

        // For recursive types, insert a type variable first to break the cycle
        // We'll update it later if needed
        let placeholder = self.ctx.fresh_ty_var();
        self.type_conversion_cache.insert(hir_ty_id, placeholder);

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
        // Infer root expression
        self.infer_expr(body, body.root_expr);
    }

    /// Infer type of an expression
    #[allow(clippy::too_many_lines, reason = "Type inference requires comprehensive pattern matching")]
    fn infer_expr(&mut self, body: &Body, expr_id: ExprId) -> TyId {
        let expr = &body.exprs[expr_id];

        let inferred_ty = match expr {
            Expr::Literal { kind, .. } => self.infer_literal(kind),

            Expr::Variable { name, def, .. } => {
                // First try to look up by name in var_types
                if let Some(&var_ty) = self.var_types.get(name) {
                    var_ty
                } else if let Some(def_id) = def {
                    // Look up definition type
                    if let Some(def_ty) = self.ctx.get_def_type(*def_id) {
                        def_ty
                    } else {
                        // Unknown definition, create fresh variable
                        self.ctx.fresh_ty_var()
                    }
                } else {
                    // Unresolved variable
                    self.errors.push(TypeError::UndefinedVariable { expr: expr_id });
                    self.ctx.types.error()
                }
            }

            Expr::Call { callee, args, .. } => {
                // Infer callee type
                let callee_ty = self.infer_expr(body, *callee);

                // Infer argument types
                let arg_tys: Vec<_> = args.iter().map(|arg| self.infer_expr(body, *arg)).collect();

                // Create fresh type variable for return type
                let ret_ty = self.ctx.fresh_ty_var();

                // Unify callee with function type
                let func_ty = self.ctx.types.alloc(TyKind::Function {
                    params: arg_tys,
                    ret: Box::new(ret_ty),
                });

                if let Err(error) = Unifier::new(&mut self.ctx).unify(callee_ty, func_ty) {
                    self.errors.push(TypeError::Unification {
                        error,
                        expr: Some(expr_id),
                    });
                }

                ret_ty
            }

            Expr::BinaryOp { left, right, .. } => {
                let left_ty = self.infer_expr(body, *left);
                let right_ty = self.infer_expr(body, *right);

                // For now, assume binary ops work on same types and return that type
                if let Err(error) = Unifier::new(&mut self.ctx).unify(left_ty, right_ty) {
                    self.errors.push(TypeError::Unification {
                        error,
                        expr: Some(expr_id),
                    });
                }

                left_ty
            }

            Expr::UnaryOp { operand, .. } => {
                // Unary op returns same type as operand
                self.infer_expr(body, *operand)
            }

            Expr::Block { statements, expr, .. } => {
                // Infer statement types
                for stmt_id in statements {
                    self.infer_stmt(body, *stmt_id);
                }

                // Block type is trailing expression type or unit
                if let Some(trailing) = expr {
                    self.infer_expr(body, *trailing)
                } else {
                    self.ctx.types.unit()
                }
            }

            Expr::If { condition, then_branch, else_branch, .. } => {
                // Condition must be bool
                let cond_ty = self.infer_expr(body, *condition);
                let bool_ty = self.ctx.types.bool();

                if let Err(error) = Unifier::new(&mut self.ctx).unify(cond_ty, bool_ty) {
                    self.errors.push(TypeError::Unification {
                        error,
                        expr: Some(*condition),
                    });
                }

                // Both branches must have same type
                let then_ty = self.infer_expr(body, *then_branch);

                if let Some(else_expr) = else_branch {
                    let else_ty = self.infer_expr(body, *else_expr);

                    if let Err(error) = Unifier::new(&mut self.ctx).unify(then_ty, else_ty) {
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
                let _scrutinee_ty = self.infer_expr(body, *scrutinee);

                // All arms must have same type
                let mut result_ty = None;

                #[allow(clippy::excessive_nesting, reason = "Match arm unification requires nested checks")]
                for arm in arms {
                    let arm_ty = self.infer_expr(body, arm.body);

                    result_ty = if let Some(expected_ty) = result_ty {
                        if let Err(error) = Unifier::new(&mut self.ctx).unify(expected_ty, arm_ty) {
                            self.errors.push(TypeError::Unification {
                                error,
                                expr: Some(arm.body),
                            });
                        }
                        Some(expected_ty)
                    } else {
                        Some(arm_ty)
                    };
                }

                result_ty.unwrap_or_else(|| self.ctx.types.never())
            }

            Expr::Field { base, field, .. } => {
                let base_ty = self.infer_expr(body, *base);

                // Look up the field type from the struct definition
                let base_ty_kind = &self.ctx.types.get(base_ty).kind;
                match base_ty_kind {
                    TyKind::Struct { fields, .. } => {
                        // Find the field by name
                        if let Some((_, field_ty)) = fields.iter().find(|(name, _)| name == field) {
                            *field_ty
                        } else {
                            // Field not found, return type variable
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
                let receiver_ty = self.infer_expr(body, *receiver);

                for arg in args {
                    self.infer_expr(body, *arg);
                }

                // Look up the method return type from impl blocks
                let receiver_ty_kind = &self.ctx.types.get(receiver_ty).kind;
                let type_def_id = match receiver_ty_kind {
                    TyKind::Struct { def_id, .. } => Some(*def_id),
                    _ => None,
                };

                // Try to find the method and get its return type
                if let (Some(impl_blocks), Some(functions), Some(def_id)) =
                    (self.impl_blocks, self.functions, type_def_id)
                {
                    // Find impl blocks for this type
                    for impl_block in impl_blocks.values() {
                        if impl_block.self_ty == rv_hir::TypeId::from_raw(la_arena::RawIdx::from(def_id.0)) {
                            // Check methods in this impl block
                            for &func_id in &impl_block.methods {
                                if let Some(func) = functions.get(&func_id) {
                                    if func.name == *method {
                                        // Found the method! Use its return type
                                        if func.return_type.is_some() {
                                            // For now, just return Int since we don't have full type lowering
                                            // TODO: Properly lower the TypeId to TyId
                                            return self.ctx.types.int();
                                        }
                                        return self.ctx.fresh_ty_var();
                                    }
                                }
                            }
                        }
                    }
                }

                // Method not found or no context available
                self.ctx.fresh_ty_var()
            }

            Expr::StructConstruct { def, fields, .. } => {
                // Infer field types
                let field_tys: Vec<(rv_intern::Symbol, TyId)> = fields
                    .iter()
                    .map(|(name, field_expr)| {
                        let ty = self.infer_expr(body, *field_expr);
                        (*name, ty)
                    })
                    .collect();

                // Create struct type if we have a type definition
                if let Some(type_def_id) = def {
                    self.ctx.types.alloc(TyKind::Struct {
                        def_id: *type_def_id,
                        fields: field_tys,
                    })
                } else {
                    // No type definition resolved, create type variable
                    self.ctx.fresh_ty_var()
                }
            }

            Expr::EnumVariant { fields, .. } => {
                // Infer variant field types
                for field_expr in fields {
                    self.infer_expr(body, *field_expr);
                }

                // TODO: Proper enum variant type lookup
                self.ctx.fresh_ty_var()
            }
        };

        // Record expression type
        self.ctx.set_expr_type(expr_id, inferred_ty);
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
            Stmt::Let { pattern, initializer, .. } => {
                if let Some(init_expr) = initializer {
                    let init_ty = self.infer_expr(body, *init_expr);

                    // Record the type for the variable name
                    let pat = &body.patterns[*pattern];
                    if let rv_hir::Pattern::Binding { name, .. } = pat {
                        self.var_types.insert(*name, init_ty);
                    }
                }
            }

            Stmt::Expr { expr, .. } => {
                self.infer_expr(body, *expr);
            }

            Stmt::Return { value, .. } => {
                if let Some(val_expr) = value {
                    let _val_ty = self.infer_expr(body, *val_expr);
                    // TODO: Unify with function return type
                }
            }
        }
    }

    /// Finish inference and return result
    pub fn finish(self) -> InferenceResult {
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
