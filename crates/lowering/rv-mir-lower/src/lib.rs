//! HIR → MIR lowering

use la_arena::Arena;
use rustc_hash::FxHashMap;
use rv_const_eval::ConstValue;
use rv_hir::{
    Body, ConstId, DefId, EnumDef, Expr, ExprId, Function, FunctionId, ImplBlock, ImplId,
    LiteralKind, Parameter, Pattern, SelfParam, StaticId, Stmt, StmtId, StructDef, TraitDef,
    TraitId, Type, TypeDefId,
};
use rv_intern::{Interner, Symbol};
// Note: rv_intrinsics removed due to permission issues with crate directory
use rv_hir::{IntWidth, Signedness};
use rv_mir::{
    AggregateKind, AssertMessage, BasicBlockId, BinaryOp, Constant, LocalId, MirBuilder,
    MirFunction, MirType, MirVariant, Operand, Place, PlaceElem, RValue, Statement, Terminator,
    UnaryOp,
};
use rv_span::FileSpan;
use rv_ty::{TyContext, TyId, TyKind};
use std::collections::HashMap;

/// Create a default span for compiler-generated MIR locals (temporaries, return slots)
fn compiler_generated_span() -> FileSpan {
    FileSpan::new(rv_span::FileId(0), rv_span::Span::new(0, 0))
}

/// Severity level for MIR lowering diagnostics
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MirDiagnosticSeverity {
    /// Warning — non-fatal issue detected during lowering
    Warning,
    /// Error — serious issue detected during lowering
    Error,
}

/// A diagnostic produced during MIR lowering
#[derive(Debug, Clone)]
pub struct MirDiagnostic {
    /// Severity
    pub severity: MirDiagnosticSeverity,
    /// Human-readable message
    pub message: String,
    /// Source location
    pub span: FileSpan,
}

/// Result of MIR lowering: the MIR function plus any diagnostics
#[derive(Debug)]
pub struct MirLoweringResult {
    /// The lowered MIR function
    pub function: MirFunction,
    /// Diagnostics produced during lowering
    pub diagnostics: Vec<MirDiagnostic>,
}

/// Errors during method resolution
#[derive(Debug, Clone)]
pub enum MethodResolutionError {
    /// Method not found on type
    MethodNotFound,
    /// Mutability mismatch between receiver and method requirement
    MutabilityMismatch {
        /// What the method requires
        required: SelfParam,
        /// What the receiver provides
        provided_mutable: bool,
    },
}

/// Context for lowering HIR to MIR
pub struct LoweringContext<'ctx> {
    /// MIR builder
    builder: MirBuilder,
    /// Type context (mutable for normalize())
    ty_ctx: &'ctx mut TyContext,
    /// Map from HIR ExprId to MIR LocalId
    expr_locals: FxHashMap<ExprId, LocalId>,
    /// Return local (for storing return value)
    return_local: Option<LocalId>,
    /// Struct definitions from HIR (for field name resolution)
    structs: &'ctx HashMap<TypeDefId, StructDef>,
    /// Enum definitions from HIR (for variant index resolution)
    enums: &'ctx HashMap<TypeDefId, EnumDef>,
    /// Impl blocks from HIR (for method resolution)
    impl_blocks: &'ctx HashMap<ImplId, ImplBlock>,
    /// Function definitions from HIR (for method name matching)
    functions: &'ctx HashMap<FunctionId, Function>,
    /// HIR type arena (for resolving impl block types)
    hir_types: &'ctx Arena<Type>,
    /// Trait definitions from HIR (for trait method resolution)
    traits: &'ctx HashMap<TraitId, TraitDef>,
    /// Map from variable names to their locals (for let bindings)
    var_locals: FxHashMap<Symbol, LocalId>,
    /// String interner (for resolving primitive type names)
    interner: &'ctx Interner,
    /// Cross-module function resolution: maps (module_path, func_name) → FunctionId
    cross_module_functions: Option<&'ctx HashMap<(Vec<String>, String), FunctionId>>,
    /// Stack of (break_block, result_local) for nested loops
    loop_break_targets: Vec<(BasicBlockId, LocalId)>,
    /// Stack of continue target blocks for nested loops
    loop_continue_targets: Vec<BasicBlockId>,
    /// Closure info: maps variable name → (params, captures, body ExprId)
    /// Used to inline closure calls at call sites.
    closure_info: FxHashMap<Symbol, ClosureInfo>,
    /// Evaluated const item values: maps ConstId → compile-time evaluated value
    const_values: &'ctx HashMap<ConstId, ConstValue>,
    /// Evaluated static item initializer values: maps StaticId → compile-time evaluated value
    static_values: &'ctx HashMap<StaticId, ConstValue>,
    /// Diagnostics produced during lowering
    diagnostics: Vec<MirDiagnostic>,
    /// Lang item registry for trait-based operator dispatch
    lang_items: &'ctx rv_hir::LangItemRegistry,
    /// Stack of scopes tracking locals declared in each scope.
    /// Used to emit StorageDead in reverse declaration order at scope exit.
    scope_locals: Vec<Vec<LocalId>>,
}

/// Information about a closure needed for inlining at call sites.
#[derive(Clone)]
struct ClosureInfo {
    /// Closure parameter names
    params: Vec<Parameter>,
    /// Closure body expression ID (in the same HIR Body)
    body_expr: ExprId,
}

impl<'ctx> LoweringContext<'ctx> {
    /// Create a new lowering context
    pub fn new(
        builder: MirBuilder,
        ty_ctx: &'ctx mut TyContext,
        structs: &'ctx HashMap<TypeDefId, StructDef>,
        enums: &'ctx HashMap<TypeDefId, EnumDef>,
        impl_blocks: &'ctx HashMap<ImplId, ImplBlock>,
        functions: &'ctx HashMap<FunctionId, Function>,
        hir_types: &'ctx Arena<Type>,
        traits: &'ctx HashMap<TraitId, TraitDef>,
        interner: &'ctx Interner,
        lang_items: &'ctx rv_hir::LangItemRegistry,
        const_values: &'ctx HashMap<ConstId, ConstValue>,
        static_values: &'ctx HashMap<StaticId, ConstValue>,
    ) -> Self {
        Self {
            builder,
            ty_ctx,
            expr_locals: FxHashMap::default(),
            return_local: None,
            structs,
            enums,
            impl_blocks,
            functions,
            hir_types,
            traits,
            var_locals: FxHashMap::default(),
            interner,
            cross_module_functions: None,
            loop_break_targets: Vec::new(),
            loop_continue_targets: Vec::new(),
            closure_info: FxHashMap::default(),
            const_values,
            static_values,
            diagnostics: Vec::new(),
            lang_items,
            scope_locals: vec![Vec::new()],
        }
    }

    /// Report a diagnostic during MIR lowering
    fn report_diagnostic(
        &mut self,
        severity: MirDiagnosticSeverity,
        message: String,
        span: FileSpan,
    ) {
        self.diagnostics.push(MirDiagnostic {
            severity,
            message,
            span,
        });
    }

    /// Lower a HIR function to MIR
    pub fn lower_function(
        function: &Function,
        ty_ctx: &'ctx mut TyContext,
        structs: &'ctx HashMap<TypeDefId, StructDef>,
        enums: &'ctx HashMap<TypeDefId, EnumDef>,
        impl_blocks: &'ctx HashMap<ImplId, ImplBlock>,
        functions: &'ctx HashMap<FunctionId, Function>,
        hir_types: &'ctx Arena<Type>,
        traits: &'ctx HashMap<TraitId, TraitDef>,
        interner: &'ctx Interner,
        lang_items: &'ctx rv_hir::LangItemRegistry,
        const_values: &'ctx HashMap<ConstId, ConstValue>,
        static_values: &'ctx HashMap<StaticId, ConstValue>,
    ) -> MirLoweringResult {
        let mut builder = MirBuilder::new(function.id);
        builder.set_param_count(function.parameters.len());
        let mut ctx = Self::new(
            builder,
            ty_ctx,
            structs,
            enums,
            impl_blocks,
            functions,
            hir_types,
            traits,
            interner,
            lang_items,
            const_values,
            static_values,
        );

        // Register function parameters FIRST so they get LocalId(0), LocalId(1), etc.
        // This matches the interpreter's expectation for parameter locals
        for (param_idx, param) in function.parameters.iter().enumerate() {
            // ARCHITECTURE: Use DefId for type lookup (not Symbol name)
            // This eliminates HashMap<Symbol, TyId> dependency
            let local_id = rv_hir::LocalId(param_idx as u32);
            let def_id = rv_hir::DefId::Local {
                func: function.id,
                local: local_id,
            };

            // ARCHITECTURE: STRICT - No fallbacks, DefId lookup only
            let ty_id = ctx.ty_ctx.get_def_type(def_id).unwrap_or_else(|| {
                panic!(
                    "ICE: Parameter '{}' (function '{}', DefId={:?}) has no inferred type. \
                         Type inference MUST populate def_types before MIR lowering.",
                    ctx.interner.resolve(&param.name),
                    ctx.interner.resolve(&function.name),
                    def_id
                )
            });

            // Normalize to resolve type variables
            let normalized_ty = match ctx.ty_ctx.normalize(ty_id) {
                Ok(n) => n,
                Err(e) => {
                    panic!(
                        "ICE: Type normalization failed for parameter '{}' (function '{}', DefId={:?}). \
                         TyId: {:?}. Error: {:?}. \
                         Type inference MUST fully resolve all parameter types before MIR lowering.",
                        ctx.interner.resolve(&param.name),
                        ctx.interner.resolve(&function.name),
                        def_id,
                        ty_id,
                        e,
                    )
                }
            };

            let mir_ty = ctx.lower_type(normalized_ty);
            let param_local = ctx
                .builder
                .new_local(Some(param.name), mir_ty, false, param.span);
            ctx.var_locals.insert(param.name, param_local);
        }

        // Create return local AFTER parameters
        let return_ty = if let Some(ty_id) = ctx.ty_ctx.get_expr_type(function.body.root_expr) {
            match ctx.ty_ctx.normalize(ty_id) {
                Ok(normalized_ty) => ctx.lower_type(normalized_ty),
                Err(e) => {
                    panic!(
                        "ICE: Return type normalization failed for function '{}'. \
                         TyId: {:?}. Error: {:?}. \
                         Type inference MUST fully resolve the return type before MIR lowering.",
                        ctx.interner.resolve(&function.name),
                        ty_id,
                        e,
                    )
                }
            }
        } else {
            MirType::Unit
        };
        ctx.builder.set_return_type(return_ty.clone());
        let return_local = ctx
            .builder
            .new_local(None, return_ty, false, compiler_generated_span());
        ctx.return_local = Some(return_local);

        // Lower function body
        ctx.lower_body(&function.body);

        // Set return terminator
        ctx.builder.set_terminator(Terminator::Return {
            value: Some(Operand::Copy(Place::from_local(return_local))),
            span: compiler_generated_span(),
        });

        let diagnostics = ctx.diagnostics;
        MirLoweringResult {
            function: ctx.builder.finish(),
            diagnostics,
        }
    }

    /// Lower a HIR function to MIR with cross-module function resolution.
    ///
    /// This is used for multi-file compilation where `PathCall` expressions need
    /// to resolve functions from other modules.
    pub fn lower_function_cross_module(
        function: &Function,
        ty_ctx: &'ctx mut TyContext,
        structs: &'ctx HashMap<TypeDefId, StructDef>,
        enums: &'ctx HashMap<TypeDefId, EnumDef>,
        impl_blocks: &'ctx HashMap<ImplId, ImplBlock>,
        functions: &'ctx HashMap<FunctionId, Function>,
        hir_types: &'ctx Arena<Type>,
        traits: &'ctx HashMap<TraitId, TraitDef>,
        interner: &'ctx Interner,
        cross_module_functions: &'ctx HashMap<(Vec<String>, String), FunctionId>,
        lang_items: &'ctx rv_hir::LangItemRegistry,
        const_values: &'ctx HashMap<ConstId, ConstValue>,
        static_values: &'ctx HashMap<StaticId, ConstValue>,
    ) -> MirLoweringResult {
        // Delegate to lower_function then set cross_module_functions
        // We need to duplicate the setup since lower_function consumes ctx
        let mut builder = MirBuilder::new(function.id);
        builder.set_param_count(function.parameters.len());
        let mut ctx = Self::new(
            builder,
            ty_ctx,
            structs,
            enums,
            impl_blocks,
            functions,
            hir_types,
            traits,
            interner,
            lang_items,
            const_values,
            static_values,
        );
        ctx.cross_module_functions = Some(cross_module_functions);

        // Register function parameters
        for (param_idx, param) in function.parameters.iter().enumerate() {
            let local_id = rv_hir::LocalId(param_idx as u32);
            let def_id = rv_hir::DefId::Local {
                func: function.id,
                local: local_id,
            };

            let ty_id = ctx.ty_ctx.get_def_type(def_id).unwrap_or_else(|| {
                panic!(
                    "ICE: Parameter '{}' (function '{}', DefId={:?}) has no inferred type.",
                    ctx.interner.resolve(&param.name),
                    ctx.interner.resolve(&function.name),
                    def_id
                )
            });

            let normalized_ty = ctx.ty_ctx.normalize(ty_id).unwrap_or_else(|_| {
                use rv_ty::NormalizedTy;
                NormalizedTy::wrap_child(ctx.ty_ctx.types.int())
            });

            let mir_ty = ctx.lower_type(normalized_ty);
            let param_local = ctx
                .builder
                .new_local(Some(param.name), mir_ty, false, param.span);
            ctx.var_locals.insert(param.name, param_local);
        }

        // Create return local
        let return_ty = if let Some(ty_id) = ctx.ty_ctx.get_expr_type(function.body.root_expr) {
            match ctx.ty_ctx.normalize(ty_id) {
                Ok(normalized_ty) => ctx.lower_type(normalized_ty),
                Err(e) => {
                    panic!(
                        "ICE: Return type normalization failed for function '{}' (cross-module). \
                         TyId: {:?}. Error: {:?}. \
                         Type inference MUST fully resolve the return type before MIR lowering.",
                        ctx.interner.resolve(&function.name),
                        ty_id,
                        e,
                    )
                }
            }
        } else {
            MirType::Unit
        };
        let return_local = ctx
            .builder
            .new_local(None, return_ty, false, compiler_generated_span());
        ctx.return_local = Some(return_local);

        ctx.lower_body(&function.body);

        ctx.builder.set_terminator(Terminator::Return {
            value: Some(Operand::Copy(Place::from_local(return_local))),
            span: compiler_generated_span(),
        });

        let diagnostics = ctx.diagnostics;
        MirLoweringResult {
            function: ctx.builder.finish(),
            diagnostics,
        }
    }

    /// Lower a HIR function to MIR with type substitution for generic parameters
    pub fn lower_function_with_subst(
        function: &Function,
        ty_ctx: &'ctx mut TyContext,
        structs: &'ctx HashMap<TypeDefId, StructDef>,
        enums: &'ctx HashMap<TypeDefId, EnumDef>,
        impl_blocks: &'ctx HashMap<ImplId, ImplBlock>,
        functions: &'ctx HashMap<FunctionId, Function>,
        hir_types: &'ctx Arena<Type>,
        traits: &'ctx HashMap<TraitId, TraitDef>,
        type_subst: &HashMap<Symbol, MirType>,
        instance_id: FunctionId,
        interner: &'ctx Interner,
        lang_items: &'ctx rv_hir::LangItemRegistry,
        const_values: &'ctx HashMap<ConstId, ConstValue>,
        static_values: &'ctx HashMap<StaticId, ConstValue>,
    ) -> MirLoweringResult {
        let mut builder = MirBuilder::new(instance_id);
        builder.set_param_count(function.parameters.len());
        let mut ctx = Self::new(
            builder,
            ty_ctx,
            structs,
            enums,
            impl_blocks,
            functions,
            hir_types,
            traits,
            interner,
            lang_items,
            const_values,
            static_values,
        );

        // ARCHITECTURE: Register parameters with types from DefId lookup + substitution
        for (param_idx, param) in function.parameters.iter().enumerate() {
            // Get the HIR type to check if it's a generic parameter
            let hir_ty = &hir_types[param.ty];

            // Determine the MIR type for this parameter
            let param_ty: MirType = match hir_ty {
                // Generic parameter (e.g., T in fn foo<T>(x: T)) - use substitution
                Type::Generic { name, .. } => {
                    if let Some(concrete_ty) = type_subst.get(name) {
                        // Use the concrete type from substitution (e.g., T -> Int)
                        concrete_ty.clone()
                    } else {
                        panic!(
                            "Generic parameter '{}' missing from type_subst map",
                            ctx.interner.resolve(name)
                        );
                    }
                }
                // Non-generic type - use DefId lookup
                _ => {
                    let local_id = rv_hir::LocalId(param_idx as u32);
                    let def_id = rv_hir::DefId::Local {
                        func: function.id,
                        local: local_id,
                    };

                    let ty_id = ctx.ty_ctx.get_def_type(def_id).unwrap_or_else(|| {
                        panic!(
                            "ICE: Parameter '{:?}' (index {}, DefId={:?}) has no inferred type. \
                                 Type inference should have assigned a type to all parameters.",
                            param.name, param_idx, def_id
                        )
                    });

                    // Try to normalize, but if it fails (unresolved type variable), use Int as default
                    // This can happen for generic parameters without concrete substitutions
                    let normalized_ty = ctx.ty_ctx.normalize(ty_id).unwrap_or_else(|_| {
                        // Use Int type as default for unresolved type variables
                        use rv_ty::NormalizedTy;
                        NormalizedTy::wrap_child(ctx.ty_ctx.types.int())
                    });

                    ctx.lower_type(normalized_ty)
                }
            };

            let param_local = ctx
                .builder
                .new_local(Some(param.name), param_ty, false, param.span);
            ctx.var_locals.insert(param.name, param_local);
        }

        // Create return local AFTER parameters
        // Check if return type is a generic parameter that needs substitution
        let return_ty = if let Some(return_type_id) = function.return_type {
            let hir_ret_ty = &hir_types[return_type_id];
            match hir_ret_ty {
                // Generic type parameter (e.g., T in fn foo<T>() -> T)
                Type::Generic { name, .. } => {
                    if let Some(concrete_ty) = type_subst.get(name) {
                        concrete_ty.clone()
                    } else {
                        panic!(
                            "Generic return type '{}' missing from type_subst map",
                            ctx.interner.resolve(name)
                        );
                    }
                }
                // Named type that might be a generic parameter
                Type::Named { name, .. } => {
                    // Check if this is a generic parameter with a substitution
                    if let Some(concrete_ty) = type_subst.get(&name) {
                        concrete_ty.clone()
                    } else {
                        // Not a generic parameter, use type inference
                        if let Some(ty_id) = ctx.ty_ctx.get_expr_type(function.body.root_expr) {
                            match ctx.ty_ctx.normalize(ty_id) {
                                Ok(normalized_ty) => ctx.lower_type(normalized_ty),
                                Err(e) => panic!(
                                    "ICE: Return type normalization failed for generic function '{}' (Named branch). \
                                     TyId: {:?}. Error: {:?}.",
                                    ctx.interner.resolve(&function.name),
                                    ty_id,
                                    e,
                                ),
                            }
                        } else {
                            MirType::Unit
                        }
                    }
                }
                // Reference to generic (e.g., &T in fn foo<T>() -> &T)
                Type::Reference { inner, mutable, .. } => {
                    let inner_hir_ty = &hir_types[**inner];
                    let inner_mir_ty = match inner_hir_ty {
                        Type::Generic { name, .. } => {
                            if let Some(concrete_ty) = type_subst.get(name) {
                                concrete_ty.clone()
                            } else {
                                panic!(
                                    "Generic return type '{}' missing from type_subst map",
                                    ctx.interner.resolve(name)
                                );
                            }
                        }
                        _ => {
                            // Non-generic inner type, use type inference
                            if let Some(ty_id) = ctx.ty_ctx.get_expr_type(function.body.root_expr) {
                                match ctx.ty_ctx.normalize(ty_id) {
                                    Ok(normalized_ty) => ctx.lower_type(normalized_ty),
                                    Err(e) => panic!(
                                        "ICE: Return type normalization failed for generic function '{}' (Ref inner branch). \
                                         TyId: {:?}. Error: {:?}.",
                                        ctx.interner.resolve(&function.name),
                                        ty_id,
                                        e,
                                    ),
                                }
                            } else {
                                MirType::Unit
                            }
                        }
                    };
                    MirType::Ref {
                        mutable: *mutable,
                        inner: Box::new(inner_mir_ty),
                        lifetime: None,
                    }
                }
                // Other types, use type inference
                _ => {
                    if let Some(ty_id) = ctx.ty_ctx.get_expr_type(function.body.root_expr) {
                        match ctx.ty_ctx.normalize(ty_id) {
                            Ok(normalized_ty) => ctx.lower_type(normalized_ty),
                            Err(e) => panic!(
                                "ICE: Return type normalization failed for generic function '{}' (other types branch). \
                                 TyId: {:?}. Error: {:?}.",
                                ctx.interner.resolve(&function.name),
                                ty_id,
                                e,
                            ),
                        }
                    } else {
                        MirType::Unit
                    }
                }
            }
        } else {
            // No return type annotation, use type inference
            if let Some(ty_id) = ctx.ty_ctx.get_expr_type(function.body.root_expr) {
                match ctx.ty_ctx.normalize(ty_id) {
                    Ok(normalized_ty) => ctx.lower_type(normalized_ty),
                    Err(e) => panic!(
                        "ICE: Return type normalization failed for generic function '{}' (no annotation branch). \
                         TyId: {:?}. Error: {:?}.",
                        ctx.interner.resolve(&function.name),
                        ty_id,
                        e,
                    ),
                }
            } else {
                MirType::Unit
            }
        };
        let return_local = ctx
            .builder
            .new_local(None, return_ty, false, compiler_generated_span());
        ctx.return_local = Some(return_local);

        // Lower function body
        ctx.lower_body(&function.body);

        // Set return terminator
        ctx.builder.set_terminator(Terminator::Return {
            value: Some(Operand::Copy(Place::from_local(return_local))),
            span: compiler_generated_span(),
        });

        let diagnostics = ctx.diagnostics;
        MirLoweringResult {
            function: ctx.builder.finish(),
            diagnostics,
        }
    }

    /// Lower function body
    fn lower_body(&mut self, body: &Body) {
        // Lower root expression
        let root_local = self.lower_expr(body, body.root_expr);

        // Copy root to return local
        if let Some(return_local) = self.return_local {
            let span = get_expr_span(&body.exprs[body.root_expr]);
            self.builder.add_statement(Statement::Assign {
                place: Place::from_local(return_local),
                rvalue: RValue::Use(Operand::Copy(Place::from_local(root_local))),
                span,
            });
        }
    }

    /// Lower an expression to MIR, returning the local containing the result
    fn lower_expr(&mut self, body: &Body, expr_id: ExprId) -> LocalId {
        // Check if we already lowered this expression
        if let Some(local) = self.expr_locals.get(&expr_id) {
            return *local;
        }

        let expr = &body.exprs[expr_id];
        let ty_id = self.ty_ctx.get_expr_type(expr_id).unwrap_or_else(|| {
            panic!(
                "Type inference failed to produce a type for expression: {:?} at {:?}. \
                This indicates a bug in type inference - all expressions must have resolved types \
                before MIR lowering.",
                expr, expr_id
            )
        });

        // Normalize the type to resolve type variables
        let mir_ty = match self.ty_ctx.normalize(ty_id) {
            Ok(normalized_ty) => self.lower_type(normalized_ty),
            Err(e) => {
                panic!(
                    "ICE: Type normalization failed for expression {:?} with type {:?}. \
                    Error: {:?}. This indicates unresolved type variables that should have been \
                    resolved by type inference.",
                    expr, ty_id, e
                )
            }
        };

        // Create a temporary for the result
        let result_local =
            self.builder
                .new_local(None, mir_ty.clone(), false, compiler_generated_span());

        match expr {
            Expr::WhileLet { .. } | Expr::IfLet { .. } => {
                panic!("ICE: WhileLet and IfLet expressions should be desugared before MIR lowering")
            }

            Expr::Literal { kind, span } => {
                let constant = Constant {
                    kind: kind.clone(),
                    ty: mir_ty.clone(),
                };
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Constant(constant)),
                    span: *span,
                });
            }

            Expr::Variable { name, def, span } => {
                // Check if this variable references a const or static item
                // Const/static values are inlined as constants at the MIR level
                if let Some(DefId::Const(const_id)) = def {
                    let value = self.const_values.get(const_id).unwrap_or_else(|| {
                        panic!(
                            "ICE: Const item '{:?}' referenced but not evaluated. \
                             Const evaluation must run before MIR lowering.",
                            const_id
                        )
                    });
                    let literal = value.to_literal_kind().unwrap_or_else(|| {
                        panic!(
                            "ICE: Const value for '{:?}' not convertible to literal. \
                             Aggregate const values (tuple/struct/array) are not yet supported.",
                            const_id
                        )
                    });
                    let constant = Constant {
                        kind: literal,
                        ty: mir_ty.clone(),
                    };
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Use(Operand::Constant(constant)),
                        span: *span,
                    });
                } else if let Some(DefId::Static(static_id)) = def {
                    let value = self.static_values.get(static_id).unwrap_or_else(|| {
                        panic!(
                            "ICE: Static item '{:?}' referenced but not evaluated. \
                             Const evaluation must run before MIR lowering.",
                            static_id
                        )
                    });
                    let literal = value.to_literal_kind().unwrap_or_else(|| {
                        panic!(
                            "ICE: Static value for '{:?}' not convertible to literal. \
                             Aggregate static values (tuple/struct/array) are not yet supported.",
                            static_id
                        )
                    });
                    let constant = Constant {
                        kind: literal,
                        ty: mir_ty.clone(),
                    };
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Use(Operand::Constant(constant)),
                        span: *span,
                    });
                } else {
                    // Look up variable in var_locals (set by let bindings and parameters)
                    let var_local = self.var_locals.get(name).copied();

                    if let Some(var_local) = var_local {
                        // Use Copy or Move based on whether the type is Copy
                        self.builder.add_statement(Statement::Assign {
                            place: Place::from_local(result_local),
                            rvalue: RValue::Use(self.operand_for_local(var_local)),
                            span: *span,
                        });
                    } else {
                        let var_name = self.interner.resolve(name);
                        panic!(
                            "ICE: Variable '{}' not found in var_locals during MIR lowering at {:?}. \
                             Name resolution should have caught undefined variables before MIR lowering.",
                            var_name, span
                        );
                    }
                }
            }

            Expr::BinaryOp {
                op,
                left,
                right,
                span,
            } => {
                let left_local = self.lower_expr(body, *left);
                let right_local = self.lower_expr(body, *right);

                // Try operator trait dispatch for non-primitive types
                let trait_func =
                    Self::binary_op_trait_method(op).and_then(|(trait_name, method_name)| {
                        self.resolve_operator_trait(*left, trait_name, method_name)
                    });

                if let Some(func_id) = trait_func {
                    // Operator overloaded via trait — emit method call
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Call {
                            func: func_id,
                            args: vec![
                                Operand::Copy(Place::from_local(left_local)),
                                Operand::Copy(Place::from_local(right_local)),
                            ],
                        },
                        span: *span,
                    });
                } else {
                    // Primitive type — use built-in binary op
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::BinaryOp {
                            op: BinaryOp::from(*op),
                            left: Operand::Copy(Place::from_local(left_local)),
                            right: Operand::Copy(Place::from_local(right_local)),
                        },
                        span: *span,
                    });
                }
            }

            Expr::UnaryOp { op, operand, span } => {
                let operand_local = self.lower_expr(body, *operand);

                // References should use RValue::Ref, not RValue::UnaryOp
                use rv_hir::UnaryOp as HirUnaryOp;
                let rvalue = match op {
                    HirUnaryOp::Ref => RValue::Ref {
                        mutable: false,
                        place: Place::from_local(operand_local),
                    },
                    HirUnaryOp::RefMut => RValue::Ref {
                        mutable: true,
                        place: Place::from_local(operand_local),
                    },
                    HirUnaryOp::Deref => {
                        // Check if the operand is a built-in reference/pointer type
                        let operand_mir_ty = self.get_local_type(operand_local);
                        let is_builtin = matches!(
                            operand_mir_ty,
                            MirType::Ref { .. } | MirType::Pointer { .. }
                        );

                        if is_builtin {
                            // Built-in dereference for references and raw pointers
                            let deref_place = Place {
                                local: operand_local,
                                projection: vec![PlaceElem::Deref],
                            };
                            RValue::Use(Operand::Copy(deref_place))
                        } else if let Some(func_id) =
                            self.resolve_operator_trait(*operand, "Deref", "deref")
                        {
                            // Trait dispatch: call Deref::deref(&self)
                            RValue::Call {
                                func: func_id,
                                args: vec![Operand::Copy(Place::from_local(operand_local))],
                            }
                        } else {
                            // Fallback: use PlaceElem::Deref for unresolved types
                            let deref_place = Place {
                                local: operand_local,
                                projection: vec![PlaceElem::Deref],
                            };
                            RValue::Use(Operand::Copy(deref_place))
                        }
                    }
                    _ => {
                        // Try operator trait dispatch for non-primitive types
                        let trait_func = Self::unary_op_trait_method(op).and_then(
                            |(trait_name, method_name)| {
                                self.resolve_operator_trait(*operand, trait_name, method_name)
                            },
                        );

                        if let Some(func_id) = trait_func {
                            RValue::Call {
                                func: func_id,
                                args: vec![Operand::Copy(Place::from_local(operand_local))],
                            }
                        } else {
                            RValue::UnaryOp {
                                op: UnaryOp::from(*op),
                                operand: Operand::Copy(Place::from_local(operand_local)),
                            }
                        }
                    }
                };

                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue,
                    span: *span,
                });
            }

            Expr::Block {
                statements,
                expr,
                span,
            } => {
                // Push a new scope for tracking locals declared in this block
                self.scope_locals.push(Vec::new());

                // Lower statements
                for stmt_id in statements {
                    self.lower_stmt(body, *stmt_id);
                }

                // Lower trailing expression if present
                if let Some(trailing_expr) = expr {
                    let trailing_local = self.lower_expr(body, *trailing_expr);
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Use(self.operand_for_local(trailing_local)),
                        span: *span,
                    });
                } else {
                    // No trailing expression, assign unit
                    let constant = Constant {
                        kind: LiteralKind::Unit,
                        ty: MirType::Unit,
                    };
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Use(Operand::Constant(constant)),
                        span: *span,
                    });
                }

                // Pop scope and emit drops/StorageDead for locals in reverse declaration order
                if let Some(scope) = self.scope_locals.pop() {
                    for local in scope.into_iter().rev() {
                        let needs_drop = self
                            .builder
                            .get_local_type(local)
                            .map(|ty| !self.is_copy_type(&ty))
                            .unwrap_or(false);

                        if needs_drop {
                            // Non-Copy type: emit Drop terminator and create continuation block
                            let continuation = self.builder.new_block();
                            self.builder.set_terminator(Terminator::Drop {
                                place: Place::from_local(local),
                                drop_flag: None,
                                target: continuation,
                                span: *span,
                            });
                            self.builder.set_current_block(continuation);
                        }
                        self.builder.add_statement(Statement::StorageDead(local));
                    }
                }
            }

            Expr::If {
                condition,
                then_branch,
                else_branch,
                span,
            } => {
                // Lower condition
                let cond_local = self.lower_expr(body, *condition);

                // Create blocks for then, else, and after
                let then_block = self.builder.new_block();
                let else_block = self.builder.new_block();
                let after_block = self.builder.new_block();

                // Branch on condition
                self.builder.set_terminator(Terminator::SwitchInt {
                    discriminant: Operand::Copy(Place::from_local(cond_local)),
                    targets: {
                        let mut map = indexmap::IndexMap::new();
                        map.insert(1, then_block);
                        map
                    },
                    otherwise: else_block,
                    span: *span,
                });

                // Lower then branch
                self.builder.set_current_block(then_block);
                let then_local = self.lower_expr(body, *then_branch);
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Copy(Place::from_local(then_local))),
                    span: *span,
                });
                self.builder.set_terminator(Terminator::Goto(after_block));

                // Lower else branch
                self.builder.set_current_block(else_block);
                if let Some(else_expr) = else_branch {
                    let else_local = self.lower_expr(body, *else_expr);
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Use(Operand::Copy(Place::from_local(else_local))),
                        span: *span,
                    });
                } else {
                    // No else branch, assign unit
                    let constant = Constant {
                        kind: LiteralKind::Unit,
                        ty: MirType::Unit,
                    };
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Use(Operand::Constant(constant)),
                        span: *span,
                    });
                }
                self.builder.set_terminator(Terminator::Goto(after_block));

                // Continue in after block
                self.builder.set_current_block(after_block);
            }

            Expr::Match {
                scrutinee,
                arms,
                span,
            } => {
                // Check exhaustiveness
                use rv_hir::exhaustiveness::{ExhaustivenessResult, is_exhaustive};
                let exhaustiveness = is_exhaustive(arms, body, self.structs, self.enums);
                if let ExhaustivenessResult::NonExhaustive { missing_patterns } = exhaustiveness {
                    self.report_diagnostic(
                        MirDiagnosticSeverity::Warning,
                        format!(
                            "match is not exhaustive. Missing patterns: {}",
                            missing_patterns.join(", ")
                        ),
                        *span,
                    );
                }

                // Lower scrutinee
                let scrutinee_local = self.lower_expr(body, *scrutinee);

                // Detect if any arm uses an enum pattern. If so, we need to
                // extract the discriminant from the scrutinee aggregate before
                // the SwitchInt.
                let has_enum_patterns = arms
                    .iter()
                    .any(|arm| matches!(&body.patterns[arm.pattern], Pattern::Enum { .. }));

                let switch_local = if has_enum_patterns {
                    let discr_local = self.builder.new_local(
                        None,
                        MirType::Int(rv_hir::IntWidth::I32, rv_hir::Signedness::Signed),
                        false,
                        compiler_generated_span(),
                    );
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(discr_local),
                        rvalue: RValue::Discriminant(Place::from_local(scrutinee_local)),
                        span: *span,
                    });
                    discr_local
                } else {
                    scrutinee_local
                };

                // Create blocks for each arm + after block
                let after_block = self.builder.new_block();
                let arm_blocks: Vec<_> = arms.iter().map(|_| self.builder.new_block()).collect();

                // Create otherwise block (unreachable for exhaustive matches)
                let otherwise_block = self.builder.new_block();

                // Build switch targets
                // Note: We must respect source order - stop adding targets after first wildcard
                let mut targets = indexmap::IndexMap::new();
                let mut found_wildcard = false;
                let mut wildcard_idx = None;

                for (arm_idx, arm) in arms.iter().enumerate() {
                    if found_wildcard {
                        // Skip arms after wildcard - they're unreachable
                        break;
                    }

                    let pattern = &body.patterns[arm.pattern];

                    // Handle different pattern types
                    match pattern {
                        Pattern::Literal { kind, .. } => {
                            // Map literal value to arm block
                            if let Some(value) = literal_to_u128(kind) {
                                targets.insert(value, arm_blocks[arm_idx]);
                            }
                        }
                        Pattern::Binding { sub_pattern, .. } => {
                            // For @ patterns with sub-patterns, match against the sub-pattern
                            if let Some(sub_pat_id) = sub_pattern {
                                let sub_pat = &body.patterns[**sub_pat_id];
                                // Recursively handle the sub-pattern
                                match sub_pat {
                                    Pattern::Literal { kind, .. } => {
                                        if let Some(value) = literal_to_u128(kind) {
                                            targets.insert(value, arm_blocks[arm_idx]);
                                        }
                                    }
                                    _ => {
                                        // Sub-pattern is complex, treat as wildcard
                                        found_wildcard = true;
                                        wildcard_idx = Some(arm_idx);
                                    }
                                }
                            } else {
                                // Simple binding without sub-pattern - matches everything
                                found_wildcard = true;
                                wildcard_idx = Some(arm_idx);
                            }
                        }
                        Pattern::Wildcard { .. } => {
                            // Wildcard patterns match everything
                            found_wildcard = true;
                            wildcard_idx = Some(arm_idx);
                        }
                        Pattern::Or {
                            patterns: or_patterns,
                            ..
                        } => {
                            // Or-pattern: map each alternative to the same block
                            for pat_id in or_patterns {
                                if let Pattern::Literal { kind, .. } = &body.patterns[*pat_id] {
                                    if let Some(value) = literal_to_u128(kind) {
                                        targets.insert(value, arm_blocks[arm_idx]);
                                    }
                                }
                            }
                        }
                        Pattern::Range {
                            start,
                            end,
                            inclusive,
                            ..
                        } => {
                            // Range pattern: map all values in range to arm block
                            if let (Some(start_val), Some(end_val)) =
                                (literal_to_u128(start), literal_to_u128(end))
                            {
                                let end_inclusive = if *inclusive {
                                    end_val
                                } else {
                                    end_val.saturating_sub(1)
                                };
                                for value in start_val..=end_inclusive {
                                    targets.insert(value, arm_blocks[arm_idx]);
                                }
                            }
                        }
                        Pattern::Enum { variant, def, .. } => {
                            // Map enum variant to its discriminant index
                            if let Some(type_def_id) = def {
                                if let Some(variant_idx) =
                                    self.resolve_variant_index(*type_def_id, *variant)
                                {
                                    targets.insert(variant_idx as u128, arm_blocks[arm_idx]);
                                }
                            }
                        }
                        _ => {
                            // Tuple, struct, and binding patterns are irrefutable —
                            // they always match. In the SwitchInt discriminant phase
                            // they act like wildcards. Field extraction and variable
                            // binding happen in the arm body lowering below.
                            found_wildcard = true;
                            wildcard_idx = Some(arm_idx);
                        }
                    }
                }

                // Determine otherwise target
                let otherwise_target = if let Some(idx) = wildcard_idx {
                    arm_blocks[idx]
                } else {
                    otherwise_block
                };

                // Emit switch
                self.builder.set_terminator(Terminator::SwitchInt {
                    discriminant: Operand::Copy(Place::from_local(switch_local)),
                    targets,
                    otherwise: otherwise_target,
                    span: *span,
                });

                // Lower each arm - each arm writes directly to result_local
                for (arm_idx, arm) in arms.iter().enumerate() {
                    self.builder.set_current_block(arm_blocks[arm_idx]);

                    // Handle pattern bindings
                    let saved_var_locals = self.var_locals.clone();
                    let pattern = &body.patterns[arm.pattern];
                    self.lower_pattern_bindings(pattern, scrutinee_local, body);

                    // Lower arm body
                    let arm_result = self.lower_expr(body, arm.body);

                    // Restore var_locals to avoid leaking bindings to other arms
                    self.var_locals = saved_var_locals;

                    // Assign arm result directly to result_local
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Use(Operand::Copy(Place::from_local(arm_result))),
                        span: *span,
                    });

                    // Jump to after block
                    self.builder.set_terminator(Terminator::Goto(after_block));
                }

                // Otherwise block (unreachable)
                self.builder.set_current_block(otherwise_block);
                self.builder.set_terminator(Terminator::Unreachable);

                // Continue in after block
                self.builder.set_current_block(after_block);
            }

            Expr::StructConstruct {
                struct_name,
                def: _,
                fields,
                span,
            } => {
                // Lower field initializers (use Copy or Move based on type)
                let field_operands: Vec<Operand> = fields
                    .iter()
                    .map(|(_, field_expr)| {
                        let field_local = self.lower_expr(body, *field_expr);
                        self.operand_for_local(field_local)
                    })
                    .collect();

                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Aggregate {
                        kind: AggregateKind::Struct { name: *struct_name },
                        operands: field_operands,
                    },
                    span: *span,
                });
            }

            Expr::Field { base, field, span } => {
                // Lower base expression
                let base_local = self.lower_expr(body, *base);

                // Get the type of the base expression from type inference
                let base_ty_id = self.ty_ctx.get_expr_type(*base).unwrap_or_else(|| {
                    panic!(
                        "ICE: Field access base expression has no inferred type. \
                             Type inference should have assigned a type to all expressions."
                    )
                });

                // Normalize the type to resolve type variables
                let normalized_ty = self.ty_ctx.normalize(base_ty_id).unwrap_or_else(|_| {
                    panic!(
                        "ICE: Failed to normalize type {:?} for field access. \
                             Type inference should resolve all type variables.",
                        base_ty_id
                    )
                });

                // Resolve field name to index using the normalized type
                let concrete_ty_id = normalized_ty.ty_id();
                let field_idx = self
                    .resolve_field_index(concrete_ty_id, *field)
                    .unwrap_or_else(|| {
                        let ty_kind = &self.ty_ctx.types.get(concrete_ty_id).kind;
                        panic!(
                            "ICE: Failed to resolve field '{}' on type {:?} (kind: {:?}). \
                             Type checker should have validated field access.",
                            self.interner.resolve(field),
                            concrete_ty_id,
                            ty_kind
                        )
                    });

                // If the base type is a reference (e.g., &self), insert a Deref
                // projection before the Field projection so backends correctly
                // dereference the pointer before accessing the struct field.
                let concrete_ty_kind = &self.ty_ctx.types.get(concrete_ty_id).kind;
                let needs_deref = matches!(concrete_ty_kind, TyKind::Ref { .. });

                let projection = if needs_deref {
                    vec![PlaceElem::Deref, PlaceElem::Field { field_idx }]
                } else {
                    vec![PlaceElem::Field { field_idx }]
                };

                let field_place = Place {
                    local: base_local,
                    projection,
                };

                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Copy(field_place)),
                    span: *span,
                });
            }

            Expr::EnumVariant {
                enum_name,
                variant,
                def,
                fields,
                span,
            } => {
                // Lower variant fields (use Copy or Move based on type)
                let field_operands: Vec<Operand> = fields
                    .iter()
                    .map(|field_expr| {
                        let field_local = self.lower_expr(body, *field_expr);
                        self.operand_for_local(field_local)
                    })
                    .collect();

                // Resolve variant name to index
                let type_def_id = def.unwrap_or_else(|| {
                    panic!(
                        "ICE: Enum variant construct '{}' has no type definition. \
                         Name resolution should have linked all enum variants to their type definitions.",
                        self.interner.resolve(variant)
                    )
                });

                let variant_idx = self
                    .resolve_variant_index(type_def_id, *variant)
                    .unwrap_or_else(|| {
                        panic!(
                            "ICE: Failed to resolve variant '{}' in type def {:?}. \
                             Type checker should have validated variant access.",
                            self.interner.resolve(variant),
                            type_def_id
                        )
                    });

                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Aggregate {
                        kind: AggregateKind::Enum {
                            name: *enum_name,
                            variant_idx,
                        },
                        operands: field_operands,
                    },
                    span: *span,
                });
            }

            Expr::Call { callee, args, type_args: _, span } => {
                // Lower arguments (use Copy or Move based on type)
                let arg_operands: Vec<Operand> = args
                    .iter()
                    .map(|arg_expr| {
                        let arg_local = self.lower_expr(body, *arg_expr);
                        self.operand_for_local(arg_local)
                    })
                    .collect();

                // Extract the function ID from the callee expression
                let callee_expr = &body.exprs[*callee];
                if let Expr::Variable {
                    def: Some(DefId::Function(func_id)),
                    ..
                } = callee_expr
                {
                    // Emit a regular function call
                    // Note: Intrinsic detection disabled (rv-intrinsics crate inaccessible)
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Call {
                            func: *func_id,
                            args: arg_operands,
                        },
                        span: *span,
                    });
                } else if let Expr::Variable { name, .. } = callee_expr {
                    // Check if this variable refers to a closure
                    if let Some(closure) = self.closure_info.get(name).cloned() {
                        // Inline the closure: bind parameters to arguments, then
                        // lower the closure body expression.

                        // Save current var_locals so we can restore after inlining
                        let saved_locals = self.var_locals.clone();

                        // Bind closure parameters to the argument values
                        for (i, param) in closure.params.iter().enumerate() {
                            if let Some(operand) = arg_operands.get(i) {
                                // Create a local for this closure parameter
                                let param_local = self.builder.new_local(
                                    Some(param.name),
                                    MirType::Unit,
                                    false,
                                    compiler_generated_span(),
                                );
                                self.builder.add_statement(Statement::Assign {
                                    place: Place::from_local(param_local),
                                    rvalue: RValue::Use(operand.clone()),
                                    span: *span,
                                });
                                self.var_locals.insert(param.name, param_local);
                            }
                        }

                        // Lower the closure body expression
                        let body_local = self.lower_expr(body, closure.body_expr);

                        // Assign the closure body result to the call result
                        self.builder.add_statement(Statement::Assign {
                            place: Place::from_local(result_local),
                            rvalue: RValue::Use(Operand::Copy(Place::from_local(body_local))),
                            span: *span,
                        });

                        // Restore var_locals (closure params go out of scope)
                        self.var_locals = saved_locals;
                    } else {
                        panic!(
                            "ICE: Callee '{}' is not a direct function reference \
                             or a known closure at {:?}. Callee expression: {:?}",
                            self.interner.resolve(name),
                            span,
                            callee_expr
                        );
                    }
                } else {
                    panic!(
                        "ICE: Callee is not a variable expression at {:?}. \
                         Only direct function calls and closure calls are supported. \
                         Callee expression: {:?}",
                        span, callee_expr
                    );
                }
            }

            Expr::PathCall {
                path,
                function,
                args,
                span,
            } => {
                // Lower arguments (use Copy or Move based on type)
                let arg_operands: Vec<Operand> = args
                    .iter()
                    .map(|arg_expr| {
                        let arg_local = self.lower_expr(body, *arg_expr);
                        self.operand_for_local(arg_local)
                    })
                    .collect();

                // Resolve the cross-module function
                let module_path: Vec<String> = path
                    .iter()
                    .map(|seg| self.interner.resolve(seg).to_string())
                    .collect();
                let func_name = self.interner.resolve(function).to_string();

                let resolved_func_id = self
                    .cross_module_functions
                    .and_then(|map| map.get(&(module_path, func_name)).copied());

                if let Some(func_id) = resolved_func_id {
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Call {
                            func: func_id,
                            args: arg_operands,
                        },
                        span: *span,
                    });
                } else {
                    let path_str: Vec<String> =
                        path.iter().map(|seg| self.interner.resolve(seg)).collect();
                    panic!(
                        "ICE: Cannot resolve cross-module call {}::{}. \
                         Cross-module function resolution must succeed before MIR lowering. \
                         Ensure the module is compiled and its functions are registered.",
                        path_str.join("::"),
                        self.interner.resolve(function)
                    );
                }
            }

            Expr::MethodCall {
                receiver,
                method,
                args,
                span,
            } => {
                // Lower receiver
                let receiver_local = self.lower_expr(body, *receiver);

                // Lower arguments (use Copy or Move based on type)
                let mut arg_operands: Vec<Operand> = vec![
                    // First argument is the receiver (self)
                    self.operand_for_local(receiver_local),
                ];

                // Add the rest of the arguments
                for arg_expr in args {
                    let arg_local = self.lower_expr(body, *arg_expr);
                    arg_operands.push(self.operand_for_local(arg_local));
                }

                // Resolve method name to function ID with mutability checking
                let receiver_ty = self.ty_ctx.get_expr_type(*receiver);

                // Normalize receiver type to resolve type variables before method resolution
                let normalized_receiver_ty = receiver_ty.map(|ty_id| {
                    self.ty_ctx
                        .normalize(ty_id)
                        .unwrap_or_else(|e| {
                            panic!(
                                "ICE: Failed to normalize receiver type {:?} during method resolution: {:?}. \
                                 Type inference should have resolved all type variables before MIR lowering.",
                                ty_id, e
                            )
                        })
                        .ty_id()
                });

                // Check for builtin pointer methods before normal method resolution
                let is_pointer_method = normalized_receiver_ty
                    .map(|ty_id| {
                        matches!(self.ty_ctx.types.get(ty_id).kind, TyKind::Pointer { .. })
                    })
                    .unwrap_or(false);

                if is_pointer_method {
                    let method_name = self.interner.resolve(method);
                    self.lower_pointer_method(
                        result_local,
                        receiver_local,
                        &method_name,
                        &arg_operands,
                        *span,
                    );
                } else {
                    // Get receiver mutability from type context (set during type inference)
                    let receiver_is_mut = self
                        .ty_ctx
                        .receiver_mutability
                        .get(&expr_id)
                        .copied()
                        .unwrap_or(false);

                    // ARCHITECTURE: Method resolution MUST succeed - no fallbacks allowed (per user directive)
                    let func_id = self
                        .resolve_method(normalized_receiver_ty, *method, receiver_is_mut)
                        .unwrap_or_else(|err| {
                            panic!(
                                "ICE: Method resolution failed for method '{:?}': {:?}",
                                self.interner.resolve(method),
                                err
                            )
                        });

                    // Emit a function call with the resolved method
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Call {
                            func: func_id,
                            args: arg_operands,
                        },
                        span: *span,
                    });
                }
            }

            Expr::Assign {
                target,
                value,
                span,
            } => {
                // Lower the value expression
                let value_local = self.lower_expr(body, *value);

                // Resolve the assignment target to a Place pointing at the
                // original storage (not a copy). This is critical for mutation.
                let target_place = self.resolve_lvalue_place(body, *target)
                    .unwrap_or_else(|| {
                        panic!(
                            "ICE: Failed to resolve assignment target {:?} to an lvalue Place. \
                             The target expression must be a variable, field access, or index expression.",
                            &body.exprs[*target]
                        )
                    });
                self.builder.add_statement(Statement::Assign {
                    place: target_place,
                    rvalue: RValue::Use(self.operand_for_local(value_local)),
                    span: *span,
                });
                // Assignment returns unit
                let constant = Constant {
                    kind: LiteralKind::Unit,
                    ty: MirType::Unit,
                };
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Constant(constant)),
                    span: *span,
                });
            }

            Expr::CompoundAssign {
                target,
                op,
                value,
                span,
            } => {
                let value_local = self.lower_expr(body, *value);
                let bin_op = BinaryOp::from(*op);

                // Resolve target to a Place pointing at original storage
                if let Some(target_place) = self.resolve_lvalue_place(body, *target) {
                    let temp_local = self.builder.new_local(
                        None,
                        mir_ty.clone(),
                        false,
                        compiler_generated_span(),
                    );
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(temp_local),
                        rvalue: RValue::BinaryOp {
                            op: bin_op,
                            left: Operand::Copy(target_place.clone()),
                            right: self.operand_for_local(value_local),
                        },
                        span: *span,
                    });
                    self.builder.add_statement(Statement::Assign {
                        place: target_place,
                        rvalue: RValue::Use(self.operand_for_local(temp_local)),
                        span: *span,
                    });
                }
                // Compound assignment returns unit
                let constant = Constant {
                    kind: LiteralKind::Unit,
                    ty: MirType::Unit,
                };
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Constant(constant)),
                    span: *span,
                });
            }

            Expr::WhileLoop {
                condition,
                body: loop_body,
                label: _,
                span,
            } => {
                // Create blocks: condition_check, loop_body, after_loop
                let condition_block = self.builder.new_block();
                let body_block = self.builder.new_block();
                let after_block = self.builder.new_block();

                // Jump to condition check
                self.builder
                    .set_terminator(Terminator::Goto(condition_block));

                // Push loop targets for break/continue
                self.loop_break_targets.push((after_block, result_local));
                self.loop_continue_targets.push(condition_block);

                // Condition check block
                self.builder.set_current_block(condition_block);
                let cond_local = self.lower_expr(body, *condition);
                self.builder.set_terminator(Terminator::SwitchInt {
                    discriminant: Operand::Copy(Place::from_local(cond_local)),
                    targets: {
                        let mut map = indexmap::IndexMap::new();
                        map.insert(1, body_block);
                        map
                    },
                    otherwise: after_block,
                    span: *span,
                });

                // Loop body block
                self.builder.set_current_block(body_block);
                self.lower_expr(body, *loop_body);
                self.builder
                    .set_terminator(Terminator::Goto(condition_block));

                // Pop loop targets
                self.loop_break_targets.pop();
                self.loop_continue_targets.pop();

                // Continue in after block
                self.builder.set_current_block(after_block);

                // While loops evaluate to unit
                let constant = Constant {
                    kind: LiteralKind::Unit,
                    ty: MirType::Unit,
                };
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Constant(constant)),
                    span: *span,
                });
            }

            Expr::Loop {
                body: loop_body,
                label: _,
                span,
            } => {
                let body_block = self.builder.new_block();
                let after_block = self.builder.new_block();

                // Jump to body
                self.builder.set_terminator(Terminator::Goto(body_block));

                // Push loop targets for break/continue
                self.loop_break_targets.push((after_block, result_local));
                self.loop_continue_targets.push(body_block);

                // Loop body
                self.builder.set_current_block(body_block);
                self.lower_expr(body, *loop_body);
                self.builder.set_terminator(Terminator::Goto(body_block));

                // Pop loop targets
                self.loop_break_targets.pop();
                self.loop_continue_targets.pop();

                // Continue in after block
                self.builder.set_current_block(after_block);

                // Unit value (break with value would set result_local)
                let constant = Constant {
                    kind: LiteralKind::Unit,
                    ty: MirType::Unit,
                };
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Constant(constant)),
                    span: *span,
                });
            }

            Expr::Break { value, label: _, span } => {
                if let Some((break_block, break_result)) = self.loop_break_targets.last().copied() {
                    // If break has a value, assign it to the loop's result local
                    if let Some(val) = value {
                        let val_local = self.lower_expr(body, *val);
                        self.builder.add_statement(Statement::Assign {
                            place: Place::from_local(break_result),
                            rvalue: RValue::Use(Operand::Copy(Place::from_local(val_local))),
                            span: *span,
                        });
                    }
                    // Jump to after-loop block
                    self.builder.set_terminator(Terminator::Goto(break_block));
                    // Create a new block for any dead code after break
                    let dead_block = self.builder.new_block();
                    self.builder.set_current_block(dead_block);
                }
                // Break itself evaluates to unit
                let constant = Constant {
                    kind: LiteralKind::Unit,
                    ty: MirType::Unit,
                };
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Constant(constant)),
                    span: *span,
                });
            }

            Expr::Continue { label: _, span } => {
                if let Some(&continue_block) = self.loop_continue_targets.last() {
                    self.builder
                        .set_terminator(Terminator::Goto(continue_block));
                    // Create a new block for any dead code after continue
                    let dead_block = self.builder.new_block();
                    self.builder.set_current_block(dead_block);
                }
                // Continue itself evaluates to unit
                let constant = Constant {
                    kind: LiteralKind::Unit,
                    ty: MirType::Unit,
                };
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Constant(constant)),
                    span: *span,
                });
            }

            Expr::Array { elements, span } => {
                let elem_operands: Vec<Operand> = elements
                    .iter()
                    .map(|elem| {
                        let elem_local = self.lower_expr(body, *elem);
                        self.operand_for_local(elem_local)
                    })
                    .collect();

                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Aggregate {
                        kind: AggregateKind::Array(mir_ty.clone()),
                        operands: elem_operands,
                    },
                    span: *span,
                });
            }

            Expr::Tuple { elements, span } => {
                let elem_operands: Vec<Operand> = elements
                    .iter()
                    .map(|elem| {
                        let elem_local = self.lower_expr(body, *elem);
                        self.operand_for_local(elem_local)
                    })
                    .collect();

                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Aggregate {
                        kind: AggregateKind::Tuple,
                        operands: elem_operands,
                    },
                    span: *span,
                });
            }

            Expr::Index { base, index, span } => {
                // Check if the index is a range expression for sub-slicing
                let index_expr = &body.exprs[*index];
                if let Expr::Range {
                    start: range_start,
                    end: range_end,
                    inclusive,
                    span: range_span,
                } = index_expr
                {
                    // Range indexing: arr[start..end] or arr[start..=end]
                    self.lower_range_index(
                        body,
                        *base,
                        *range_start,
                        *range_end,
                        *inclusive,
                        *range_span,
                        result_local,
                    );
                    return result_local;
                }

                let base_local = self.lower_expr(body, *base);
                let index_local = self.lower_expr(body, *index);

                // Check if the base type is a built-in array type
                let base_mir_ty = self.get_local_type(base_local);

                if let MirType::Array { size, .. } = base_mir_ty {
                    // Built-in array indexing with bounds check
                    let after_check_block = self.builder.new_block();

                    let i64_ty = MirType::Int(IntWidth::I64, Signedness::Signed);

                    // Create a local for the length constant
                    let len_local = self.builder.new_local(
                        None,
                        i64_ty.clone(),
                        false,
                        compiler_generated_span(),
                    );
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(len_local),
                        rvalue: RValue::Use(Operand::Constant(Constant {
                            kind: LiteralKind::Integer(size as i64, Some((IntWidth::I64, Signedness::Signed))),
                            ty: i64_ty.clone(),
                        })),
                        span: *span,
                    });

                    // Create the bounds check: index < len
                    let check_local = self.builder.new_local(
                        None,
                        MirType::Bool,
                        false,
                        compiler_generated_span(),
                    );
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(check_local),
                        rvalue: RValue::BinaryOp {
                            op: BinaryOp::Lt,
                            left: Operand::Copy(Place::from_local(index_local)),
                            right: Operand::Copy(Place::from_local(len_local)),
                        },
                        span: *span,
                    });

                    // Assert: index < len (panic if false)
                    self.builder.set_terminator(Terminator::Assert {
                        cond: Operand::Copy(Place::from_local(check_local)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck {
                            index: Operand::Copy(Place::from_local(index_local)),
                            len: Operand::Copy(Place::from_local(len_local)),
                        },
                        target: after_check_block,
                        span: *span,
                    });

                    // Continue in the after-check block
                    self.builder.set_current_block(after_check_block);

                    // Perform the actual indexing
                    let index_place = Place {
                        local: base_local,
                        projection: vec![PlaceElem::Index(index_local)],
                    };
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Use(Operand::Copy(index_place)),
                        span: *span,
                    });
                } else if let MirType::Slice { element } = base_mir_ty {
                    // Slice indexing with bounds check
                    // Slices are fat pointers: (ptr, len)
                    let after_check_block = self.builder.new_block();
                    let i64_ty = MirType::Int(IntWidth::I64, Signedness::Signed);

                    // Extract the length from the fat pointer (field 1)
                    let len_local = self.builder.new_local(
                        None,
                        i64_ty.clone(),
                        false,
                        compiler_generated_span(),
                    );
                    let len_place = Place {
                        local: base_local,
                        projection: vec![PlaceElem::Field { field_idx: 1 }],
                    };
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(len_local),
                        rvalue: RValue::Use(Operand::Copy(len_place)),
                        span: *span,
                    });

                    // Create the bounds check: index < len
                    let check_local = self.builder.new_local(
                        None,
                        MirType::Bool,
                        false,
                        compiler_generated_span(),
                    );
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(check_local),
                        rvalue: RValue::BinaryOp {
                            op: BinaryOp::Lt,
                            left: Operand::Copy(Place::from_local(index_local)),
                            right: Operand::Copy(Place::from_local(len_local)),
                        },
                        span: *span,
                    });

                    // Assert: index < len (panic if false)
                    self.builder.set_terminator(Terminator::Assert {
                        cond: Operand::Copy(Place::from_local(check_local)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck {
                            index: Operand::Copy(Place::from_local(index_local)),
                            len: Operand::Copy(Place::from_local(len_local)),
                        },
                        target: after_check_block,
                        span: *span,
                    });

                    // Continue in the after-check block
                    self.builder.set_current_block(after_check_block);

                    // Extract the pointer from the fat pointer (field 0) and index into it
                    // The result is element at ptr[index]
                    let ptr_local = self.builder.new_local(
                        None,
                        MirType::Pointer { mutable: false, inner: element },
                        false,
                        compiler_generated_span(),
                    );
                    let ptr_place = Place {
                        local: base_local,
                        projection: vec![PlaceElem::Field { field_idx: 0 }],
                    };
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(ptr_local),
                        rvalue: RValue::Use(Operand::Copy(ptr_place)),
                        span: *span,
                    });

                    // Index into the pointer: ptr[index]
                    let index_place = Place {
                        local: ptr_local,
                        projection: vec![PlaceElem::Index(index_local)],
                    };
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Use(Operand::Copy(index_place)),
                        span: *span,
                    });
                } else if let Some(func_id) = self.resolve_operator_trait(*base, "Index", "index") {
                    // Trait dispatch: call Index::index(&self, index)
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Call {
                            func: func_id,
                            args: vec![
                                Operand::Copy(Place::from_local(base_local)),
                                self.operand_for_local(index_local),
                            ],
                        },
                        span: *span,
                    });
                } else {
                    // Fallback: use PlaceElem::Index (no bounds check)
                    let index_place = Place {
                        local: base_local,
                        projection: vec![PlaceElem::Index(index_local)],
                    };
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Use(Operand::Copy(index_place)),
                        span: *span,
                    });
                }
            }

            Expr::Cast {
                expr: cast_expr,
                ty: target_type_id,
                span,
            } => {
                let expr_local = self.lower_expr(body, *cast_expr);

                // Determine source and target MIR types
                let source_mir_type = self.get_local_type(expr_local);
                let target_mir_type = self.hir_type_to_mir_type(*target_type_id);

                if source_mir_type == target_mir_type {
                    // Same type, just copy
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Use(Operand::Copy(Place::from_local(expr_local))),
                        span: *span,
                    });
                } else {
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Cast {
                            operand: Operand::Copy(Place::from_local(expr_local)),
                            from: source_mir_type,
                            to: target_mir_type,
                        },
                        span: *span,
                    });
                }
            }

            Expr::Closure {
                params: _,
                return_type: _,
                body: _,
                captures: _,
                is_move: _,
                span,
            } => {
                // Closures are inlined at call sites via closure_info, which is
                // populated in lower_stmt when `let f = |x| ...` is processed.
                // The closure body is lowered when `f(args)` is encountered.
                // This Unit value is assigned because closures are not yet
                // first-class values — they cannot be passed as arguments or
                // stored in data structures. If first-class closures are needed,
                // this must be replaced with a proper closure object (function
                // pointer + captured environment).
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Constant(Constant {
                        kind: LiteralKind::Unit,
                        ty: MirType::Unit,
                    })),
                    span: *span,
                });
            }
            Expr::UnsafeBlock {
                body: inner, span, ..
            } => {
                // At MIR level, unsafe blocks are transparent — safety was
                // already checked during type inference.
                let inner_local = self.lower_expr(body, *inner);
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Copy(Place::from_local(inner_local))),
                    span: *span,
                });
            }
            Expr::Error { span } => {
                // Error expression from failed lowering — emit unit and let
                // the diagnostic already recorded propagate to the user.
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Constant(Constant {
                        kind: LiteralKind::Unit,
                        ty: MirType::Unit,
                    })),
                    span: *span,
                });
            }

            Expr::Range { start, end, inclusive, span } => {
                // Range expressions produce a Range<T> struct
                // For now, lower to unit as proper Range types require stdlib
                // TODO: Implement proper Range struct construction when stdlib is available
                let _ = (start, end, inclusive); // Silence unused warnings
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Constant(Constant {
                        kind: LiteralKind::Unit,
                        ty: MirType::Unit,
                    })),
                    span: *span,
                });
            }

            Expr::Try { expr: inner, span } => {
                // Try operator desugars to match on Result/Option
                // For now, just lower the inner expression and return it
                // TODO: Implement proper try desugaring when Result/Option types are available
                let inner_local = self.lower_expr(body, *inner);
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Copy(Place::from_local(inner_local))),
                    span: *span,
                });
            }

            Expr::ForLoop { pattern, iterator, body: loop_body, label: _, span } => {
                // For loops desugar to:
                // {
                //     let mut iter = IntoIterator::into_iter(iterator);
                //     loop {
                //         match Iterator::next(&mut iter) {
                //             Some(pattern) => loop_body,
                //             None => break,
                //         }
                //     }
                // }
                // For now, just lower iterator and body, return unit
                // TODO: Implement proper for loop desugaring with Iterator trait
                let _ = (pattern, iterator, loop_body); // Silence unused warnings
                let _iter_local = self.lower_expr(body, *iterator);
                let _body_local = self.lower_expr(body, *loop_body);
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Constant(Constant {
                        kind: LiteralKind::Unit,
                        ty: MirType::Unit,
                    })),
                    span: *span,
                });
            }

            Expr::Box { value, span } => {
                // Lower the inner value expression
                let value_local = self.lower_expr(body, *value);

                // Get the type of the inner value
                let inner_ty = self.builder.locals().iter()
                    .find(|l| l.id == value_local)
                    .map(|l| l.ty.clone())
                    .unwrap_or(MirType::Unit);

                // Emit BoxNew rvalue to allocate on heap and store value
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::BoxNew {
                        operand: Operand::Copy(Place::from_local(value_local)),
                        inner_ty,
                    },
                    span: *span,
                });
            }
        }

        // Cache the result
        self.expr_locals.insert(expr_id, result_local);
        result_local
    }

    /// Lower a range index expression (arr[start..end] or arr[start..=end])
    /// This creates a sub-slice from the base array/slice.
    fn lower_range_index(
        &mut self,
        body: &Body,
        base: ExprId,
        range_start: Option<ExprId>,
        range_end: Option<ExprId>,
        inclusive: bool,
        span: FileSpan,
        result_local: LocalId,
    ) {
        let base_local = self.lower_expr(body, base);
        let base_mir_ty = self.get_local_type(base_local);

        let i64_ty = MirType::Int(IntWidth::I64, Signedness::Signed);

        // Get the start index (0 if not specified)
        let start_local = if let Some(start_expr) = range_start {
            self.lower_expr(body, start_expr)
        } else {
            let zero_local = self.builder.new_local(None, i64_ty.clone(), false, span);
            self.builder.add_statement(Statement::Assign {
                place: Place::from_local(zero_local),
                rvalue: RValue::Use(Operand::Constant(Constant {
                    kind: LiteralKind::Integer(0, Some((IntWidth::I64, Signedness::Signed))),
                    ty: i64_ty.clone(),
                })),
                span,
            });
            zero_local
        };

        // Get the end index (len if not specified)
        // For arrays, use the array size; for slices, use the length field
        let (element_ty, len_local) = match &base_mir_ty {
            MirType::Array { element, size } => {
                let len_local = self.builder.new_local(None, i64_ty.clone(), false, span);
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(len_local),
                    rvalue: RValue::Use(Operand::Constant(Constant {
                        kind: LiteralKind::Integer(*size as i64, Some((IntWidth::I64, Signedness::Signed))),
                        ty: i64_ty.clone(),
                    })),
                    span,
                });
                ((**element).clone(), len_local)
            }
            MirType::Slice { element } => {
                let len_local = self.builder.new_local(None, i64_ty.clone(), false, span);
                let len_place = Place {
                    local: base_local,
                    projection: vec![PlaceElem::Field { field_idx: 1 }],
                };
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(len_local),
                    rvalue: RValue::Use(Operand::Copy(len_place)),
                    span,
                });
                ((**element).clone(), len_local)
            }
            _ => {
                // For other types, try generic slice indexing
                // For now, just panic on unsupported types
                panic!("Range indexing not supported for type: {:?}", base_mir_ty);
            }
        };

        let end_local = if let Some(end_expr) = range_end {
            let end_val = self.lower_expr(body, end_expr);
            if inclusive {
                // For inclusive range (..=), add 1 to the end
                let end_plus_one = self.builder.new_local(None, i64_ty.clone(), false, span);
                let one_local = self.builder.new_local(None, i64_ty.clone(), false, span);
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(one_local),
                    rvalue: RValue::Use(Operand::Constant(Constant {
                        kind: LiteralKind::Integer(1, Some((IntWidth::I64, Signedness::Signed))),
                        ty: i64_ty.clone(),
                    })),
                    span,
                });
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(end_plus_one),
                    rvalue: RValue::BinaryOp {
                        op: BinaryOp::Add,
                        left: Operand::Copy(Place::from_local(end_val)),
                        right: Operand::Copy(Place::from_local(one_local)),
                    },
                    span,
                });
                end_plus_one
            } else {
                end_val
            }
        } else {
            // Use len if end not specified
            len_local
        };

        // Bounds checking: start <= end && end <= len
        let after_check_block = self.builder.new_block();

        // Check: start <= end
        let start_le_end = self.builder.new_local(None, MirType::Bool, false, span);
        self.builder.add_statement(Statement::Assign {
            place: Place::from_local(start_le_end),
            rvalue: RValue::BinaryOp {
                op: BinaryOp::Le,
                left: Operand::Copy(Place::from_local(start_local)),
                right: Operand::Copy(Place::from_local(end_local)),
            },
            span,
        });

        let check1_block = self.builder.new_block();
        self.builder.set_terminator(Terminator::Assert {
            cond: Operand::Copy(Place::from_local(start_le_end)),
            expected: true,
            msg: AssertMessage::Panic("slice index starts at a later index than it ends".to_string()),
            target: check1_block,
            span,
        });

        self.builder.set_current_block(check1_block);

        // Check: end <= len
        let end_le_len = self.builder.new_local(None, MirType::Bool, false, span);
        self.builder.add_statement(Statement::Assign {
            place: Place::from_local(end_le_len),
            rvalue: RValue::BinaryOp {
                op: BinaryOp::Le,
                left: Operand::Copy(Place::from_local(end_local)),
                right: Operand::Copy(Place::from_local(len_local)),
            },
            span,
        });

        self.builder.set_terminator(Terminator::Assert {
            cond: Operand::Copy(Place::from_local(end_le_len)),
            expected: true,
            msg: AssertMessage::BoundsCheck {
                index: Operand::Copy(Place::from_local(end_local)),
                len: Operand::Copy(Place::from_local(len_local)),
            },
            target: after_check_block,
            span,
        });

        self.builder.set_current_block(after_check_block);

        // Calculate slice length: end - start
        let slice_len = self.builder.new_local(None, i64_ty.clone(), false, span);
        self.builder.add_statement(Statement::Assign {
            place: Place::from_local(slice_len),
            rvalue: RValue::BinaryOp {
                op: BinaryOp::Sub,
                left: Operand::Copy(Place::from_local(end_local)),
                right: Operand::Copy(Place::from_local(start_local)),
            },
            span,
        });

        // Get pointer to start of sub-slice
        // For arrays: pointer to base + start * element_size
        // For slices: base.ptr + start * element_size
        let ptr_local = match &base_mir_ty {
            MirType::Array { .. } => {
                // Create pointer to array start + offset
                let ptr = self.builder.new_local(
                    None,
                    MirType::Pointer { mutable: false, inner: Box::new(element_ty.clone()) },
                    false,
                    span,
                );
                // Get pointer to base[start]
                let offset_place = Place {
                    local: base_local,
                    projection: vec![PlaceElem::Index(start_local)],
                };
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(ptr),
                    rvalue: RValue::Ref {
                        place: offset_place,
                        mutable: false,
                    },
                    span,
                });
                ptr
            }
            MirType::Slice { .. } => {
                // For slices, extract ptr and add offset
                let base_ptr = self.builder.new_local(
                    None,
                    MirType::Pointer { mutable: false, inner: Box::new(element_ty.clone()) },
                    false,
                    span,
                );
                let ptr_place = Place {
                    local: base_local,
                    projection: vec![PlaceElem::Field { field_idx: 0 }],
                };
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(base_ptr),
                    rvalue: RValue::Use(Operand::Copy(ptr_place)),
                    span,
                });

                // Offset the pointer by start
                let offset_ptr = self.builder.new_local(
                    None,
                    MirType::Pointer { mutable: false, inner: Box::new(element_ty.clone()) },
                    false,
                    span,
                );
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(offset_ptr),
                    rvalue: RValue::BinaryOp {
                        op: BinaryOp::Add,
                        left: Operand::Copy(Place::from_local(base_ptr)),
                        right: Operand::Copy(Place::from_local(start_local)),
                    },
                    span,
                });
                offset_ptr
            }
            _ => unreachable!(),
        };

        // Create the slice as a fat pointer (ptr, len) aggregate
        // The result type is a slice
        self.builder.add_statement(Statement::Assign {
            place: Place::from_local(result_local),
            rvalue: RValue::Aggregate {
                kind: AggregateKind::Tuple,
                operands: vec![
                    Operand::Copy(Place::from_local(ptr_local)),
                    Operand::Copy(Place::from_local(slice_len)),
                ],
            },
            span,
        });
    }

    /// Lower a statement
    fn lower_stmt(&mut self, body: &Body, stmt_id: StmtId) {
        let stmt = &body.stmts[stmt_id];

        match stmt {
            Stmt::Box { .. } => {
                panic!("ICE: Box statements should be lowered before MIR lowering")
            }

            Stmt::Let {
                pattern,
                initializer,
                span,
                ..
            } => {
                // Lower initializer if present
                if let Some(init_expr) = initializer {
                    let init_local = self.lower_expr(body, *init_expr);

                    // Bind to pattern using the same pattern bindings infrastructure
                    // as match arms. This supports simple bindings, tuple destructuring,
                    // struct destructuring, and enum destructuring uniformly.
                    let pat = &body.patterns[*pattern];
                    match pat {
                        rv_hir::Pattern::Binding { name, .. } => {
                            // Check if the initializer is a closure expression.
                            // If so, register the closure info for inlining at call sites.
                            let init_expr_ref = &body.exprs[*init_expr];
                            if let Expr::Closure {
                                params: closure_params,
                                body: closure_body,
                                ..
                            } = init_expr_ref
                            {
                                self.closure_info.insert(
                                    *name,
                                    ClosureInfo {
                                        params: closure_params.clone(),
                                        body_expr: *closure_body,
                                    },
                                );
                            }

                            // Create a new local for this binding with the initializer's type
                            let init_ty = self.builder.locals().iter()
                                .find(|l| l.id == init_local)
                                .map(|l| l.ty.clone())
                                .expect("Failed to find type for initializer local. This indicates a bug in MIR lowering.");
                            let binding_local = self.builder.new_local(
                                Some(*name),
                                init_ty,
                                false,
                                compiler_generated_span(),
                            );

                            // Assign the initializer value to the binding
                            self.builder.add_statement(Statement::Assign {
                                place: Place::from_local(binding_local),
                                rvalue: RValue::Use(self.operand_for_local(init_local)),
                                span: *span,
                            });

                            // Emit StorageLive for the new binding
                            self.builder
                                .add_statement(Statement::StorageLive(binding_local));

                            // Track this local in the current scope for StorageDead emission
                            if let Some(scope) = self.scope_locals.last_mut() {
                                scope.push(binding_local);
                            }

                            // Store mapping from variable name to local
                            self.var_locals.insert(*name, binding_local);
                        }
                        _ => {
                            // For tuple, struct, enum, and other patterns:
                            // Reuse the same pattern binding extraction as match arms.
                            // This handles field extraction via PlaceElem::Field projections.
                            self.lower_pattern_bindings(pat, init_local, body);
                        }
                    }
                }
            }

            Stmt::Expr { expr, .. } => {
                self.lower_expr(body, *expr);
            }

            Stmt::Return { value, span } => {
                if let Some(val_expr) = value {
                    let val_local = self.lower_expr(body, *val_expr);
                    if let Some(return_local) = self.return_local {
                        self.builder.add_statement(Statement::Assign {
                            place: Place::from_local(return_local),
                            rvalue: RValue::Use(Operand::Copy(Place::from_local(val_local))),
                            span: *span,
                        });
                    }
                }
                // Note: actual return is handled by function epilogue
            }
        }
    }

    /// Lower a type from type system to MIR type
    ///
    /// Takes a NormalizedTy which guarantees all type variables are resolved.
    /// This prevents the silent `TyKind::Var → MirType::Int` bug.
    fn lower_type(&self, ty: rv_ty::NormalizedTy) -> MirType {
        use rv_mir::MirVariant;
        use rv_ty::{NormalizedTy, VariantTy};

        // No need for apply_subst - NormalizedTy guarantees no unresolved variables!
        let ty_kind = &self.ty_ctx.types.get(ty.ty_id()).kind;

        match ty_kind {
            TyKind::Int(w, s) => MirType::Int(*w, *s),
            TyKind::Float(w) => MirType::Float(*w),
            TyKind::Char => MirType::Char,
            TyKind::Bool => MirType::Bool,
            TyKind::String => MirType::String,
            TyKind::Unit => MirType::Unit,
            TyKind::Function { params, ret } => MirType::Function {
                // Nested TyIds are also normalized, so we can wrap them
                params: params
                    .iter()
                    .map(|p| self.lower_type(NormalizedTy::wrap_child(*p)))
                    .collect(),
                ret: Box::new(self.lower_type(NormalizedTy::wrap_child(**ret))),
            },
            TyKind::Tuple { elements } => MirType::Tuple(
                elements
                    .iter()
                    .map(|e| self.lower_type(NormalizedTy::wrap_child(*e)))
                    .collect(),
            ),
            TyKind::Ref {
                mutable,
                inner,
                lifetime,
            } => MirType::Ref {
                mutable: *mutable,
                inner: Box::new(self.lower_type(NormalizedTy::wrap_child(**inner))),
                lifetime: *lifetime,
            },
            TyKind::Struct { def_id, fields } => {
                // Look up the struct name from the definition
                let struct_def = self.structs
                    .get(def_id)
                    .unwrap_or_else(|| {
                        panic!(
                            "ICE: Struct type references unknown TypeDefId {:?}. \
                             Name resolution should have linked all struct types to their definitions.",
                            def_id
                        )
                    });

                MirType::Struct {
                    name: struct_def.name,
                    fields: fields
                        .iter()
                        .map(|(_, ty_id)| self.lower_type(NormalizedTy::wrap_child(*ty_id)))
                        .collect(),
                }
            }
            TyKind::Enum { def_id, variants } => {
                let mir_variants = variants
                    .iter()
                    .map(|(name, variant_ty)| {
                        let fields = match variant_ty {
                            VariantTy::Unit => vec![],
                            VariantTy::Tuple(types) => types
                                .iter()
                                .map(|t| self.lower_type(NormalizedTy::wrap_child(*t)))
                                .collect(),
                            VariantTy::Struct(fields) => fields
                                .iter()
                                .map(|(_, ty)| self.lower_type(NormalizedTy::wrap_child(*ty)))
                                .collect(),
                        };
                        MirVariant {
                            name: *name,
                            fields,
                        }
                    })
                    .collect();

                // Look up the enum name from the definition
                let enum_def = self.enums
                    .get(def_id)
                    .unwrap_or_else(|| {
                        panic!(
                            "ICE: Enum type references unknown TypeDefId {:?}. \
                             Name resolution should have linked all enum types to their definitions.",
                            def_id
                        )
                    });

                MirType::Enum {
                    name: enum_def.name,
                    variants: mir_variants,
                }
            }
            TyKind::Array { element, size } => MirType::Array {
                element: Box::new(self.lower_type(NormalizedTy::wrap_child(**element))),
                size: *size,
            },
            TyKind::Slice { element } => MirType::Slice {
                element: Box::new(self.lower_type(NormalizedTy::wrap_child(**element))),
            },
            TyKind::Named { name, def, args } => {
                // Try to resolve the named type to its actual definition
                // Check if it's a struct
                if let Some(struct_def) = self.structs.get(def) {
                    // Build substitution map from generic params to concrete args (TyId -> MirType)
                    let type_subst = self.build_ty_generic_subst_map(
                        &struct_def.generic_params,
                        args,
                    );

                    // Create full struct type with fields by converting HIR types to MIR types
                    let field_types: Vec<MirType> = struct_def
                        .fields
                        .iter()
                        .map(|field| {
                            let hir_ty = &self.hir_types[field.ty];
                            self.lower_hir_type_with_subst(hir_ty, &type_subst)
                        })
                        .collect();

                    MirType::Struct {
                        name: *name,
                        fields: field_types,
                    }
                } else if let Some(enum_def) = self.enums.get(def) {
                    // Build substitution map from generic params to concrete args (TyId -> MirType)
                    let type_subst = self.build_ty_generic_subst_map(
                        &enum_def.generic_params,
                        args,
                    );

                    // Create full enum type with variants, including their field types
                    let mir_variants: Vec<MirVariant> = enum_def
                        .variants
                        .iter()
                        .map(|variant| {
                            let fields = match &variant.fields {
                                rv_hir::VariantFields::Unit => vec![],
                                rv_hir::VariantFields::Tuple(type_ids) => type_ids
                                    .iter()
                                    .map(|type_id| {
                                        let hir_ty = &self.hir_types[*type_id];
                                        self.lower_hir_type_with_subst(hir_ty, &type_subst)
                                    })
                                    .collect(),
                                rv_hir::VariantFields::Struct(field_defs) => field_defs
                                    .iter()
                                    .map(|field_def| {
                                        let hir_ty = &self.hir_types[field_def.ty];
                                        self.lower_hir_type_with_subst(hir_ty, &type_subst)
                                    })
                                    .collect(),
                            };
                            MirVariant {
                                name: variant.name,
                                fields,
                            }
                        })
                        .collect();

                    MirType::Enum {
                        name: *name,
                        variants: mir_variants,
                    }
                } else {
                    // Unknown named type, keep as Named
                    MirType::Named(*name)
                }
            }
            TyKind::Never => MirType::Never,
            TyKind::Pointer { mutable, inner } => MirType::Pointer {
                mutable: *mutable,
                inner: Box::new(self.lower_type(NormalizedTy::wrap_child(**inner))),
            },
            TyKind::DynTrait {
                principal,
                principal_name,
            } => MirType::DynTrait {
                principal: *principal_name,
                trait_id: Some(*principal),
            },
            TyKind::ImplTrait { principal } => MirType::ImplTrait {
                principal: *principal,
            },
            TyKind::Param { name, .. } => {
                // Generic type parameter - keep as named type
                // During monomorphization, this will be substituted with concrete types
                MirType::Named(*name)
            }
            TyKind::IntVar { .. } => {
                // Unconstrained integer inference variable — default to i32
                MirType::Int(rv_hir::IntWidth::I32, rv_hir::Signedness::Signed)
            }
            TyKind::FloatVar { .. } => {
                // Unconstrained float inference variable — default to f64
                MirType::Float(rv_hir::FloatWidth::F64)
            }
            TyKind::Var { id } => {
                // ⚠️ COMPILE ERROR: If you hit this, it means a non-normalized type was passed!
                // NormalizedTy should make this unreachable.
                panic!(
                    "ICE: Unresolved type variable ?{} in supposedly normalized type {:?}. \
                     This indicates normalize() didn't work correctly or a non-normalized TyId \
                     was unsafely wrapped in NormalizedTy.",
                    id.0,
                    ty.ty_id()
                )
            }
            TyKind::FunctionPointer { params, ret, abi } => MirType::FunctionPointer {
                params: params
                    .iter()
                    .map(|p| self.lower_type(NormalizedTy::wrap_child(*p)))
                    .collect(),
                ret: Box::new(self.lower_type(NormalizedTy::wrap_child(**ret))),
                abi: abi.clone(),
            },
            TyKind::Box { inner } => MirType::Box {
                inner: Box::new(self.lower_type(NormalizedTy::wrap_child(**inner))),
            },
            TyKind::Projection {
                base,
                assoc_type,
                trait_ref,
            } => {
                // Associated type projection that wasn't resolved during type inference.
                // This should have been resolved by looking up impl blocks during inference,
                // but if we reach here, we need to try resolving it now or panic.
                panic!(
                    "ICE: Unresolved associated type projection '{:?}::{:?}' (trait: {:?}) \
                     reached MIR lowering. All projections must be resolved to concrete types \
                     before this stage. Check that type inference properly resolves associated types.",
                    base,
                    assoc_type,
                    trait_ref
                )
            }
        }
    }

    /// Helper function to recursively convert HIR Type to MirType
    /// This is used when we need to convert struct field types from HIR to MIR
    fn lower_hir_type_recursive(&self, hir_ty: &Type) -> MirType {
        // Call the substitution-aware version with an empty substitution map
        self.lower_hir_type_with_subst(hir_ty, &HashMap::new())
    }

    /// Build a generic substitution map from generic params and concrete type args
    ///
    /// For a type like `Option<i64>`, this maps `T` -> `MirType::Int(I64, Signed)`
    fn build_generic_subst_map(
        &self,
        generic_params: &[rv_hir::GenericParam],
        args: &[rv_hir::TypeId],
        parent_subst: &HashMap<Symbol, MirType>,
    ) -> HashMap<Symbol, MirType> {
        let mut subst = parent_subst.clone();
        for (param, arg_type_id) in generic_params.iter().zip(args.iter()) {
            let arg_hir_ty = &self.hir_types[*arg_type_id];
            // Recursively lower the argument type, using parent substitutions
            let arg_mir_ty = self.lower_hir_type_with_subst(arg_hir_ty, &subst);
            subst.insert(param.name, arg_mir_ty);
        }
        subst
    }

    /// Build a generic substitution map from generic params and TyId args (from type inference)
    ///
    /// This is used when lowering TyKind::Named types that have been through type inference.
    /// The args are TyIds from the type inference context, which we convert to MirTypes.
    ///
    /// Since this is called from lower_type() on a NormalizedTy, the args TyIds are guaranteed
    /// to be children of a normalized type, so we can wrap them as NormalizedTy directly.
    fn build_ty_generic_subst_map(
        &self,
        generic_params: &[rv_hir::GenericParam],
        args: &[TyId],
    ) -> HashMap<Symbol, MirType> {
        let mut subst = HashMap::new();
        for (param, &arg_ty_id) in generic_params.iter().zip(args.iter()) {
            // The arg TyId is a child of a NormalizedTy, so it's already normalized
            let arg_mir_ty = self.lower_type(rv_ty::NormalizedTy::wrap_child(arg_ty_id));
            subst.insert(param.name, arg_mir_ty);
        }
        subst
    }

    /// Helper function to recursively convert HIR Type to MirType with generic substitutions
    ///
    /// When lowering a generic type like `Option<i64>`, we build a substitution map from the
    /// type's generic parameters (T) to the concrete arguments (i64). This map is then used
    /// when recursively lowering field types - when we encounter `Type::Generic { name: "T" }`,
    /// we look up "T" in the substitution map and return the concrete MirType.
    fn lower_hir_type_with_subst(
        &self,
        hir_ty: &Type,
        type_subst: &HashMap<Symbol, MirType>,
    ) -> MirType {
        match hir_ty {
            Type::Named {
                name,
                def: Some(def_id),
                args,
                ..
            } => {
                // User-defined type - look up the struct/enum definition
                if let Some(struct_def) = self.structs.get(def_id) {
                    // Build substitution map from generic params to concrete args
                    let local_subst = self.build_generic_subst_map(&struct_def.generic_params, args, type_subst);

                    let field_types: Vec<MirType> = struct_def
                        .fields
                        .iter()
                        .map(|field| {
                            let field_hir_ty = &self.hir_types[field.ty];
                            self.lower_hir_type_with_subst(field_hir_ty, &local_subst)
                        })
                        .collect();

                    MirType::Struct {
                        name: *name,
                        fields: field_types,
                    }
                } else if let Some(enum_def) = self.enums.get(def_id) {
                    // Build substitution map from generic params to concrete args
                    let local_subst = self.build_generic_subst_map(&enum_def.generic_params, args, type_subst);

                    let mir_variants: Vec<MirVariant> = enum_def
                        .variants
                        .iter()
                        .map(|variant| {
                            let fields = match &variant.fields {
                                rv_hir::VariantFields::Unit => vec![],
                                rv_hir::VariantFields::Tuple(type_ids) => type_ids
                                    .iter()
                                    .map(|type_id| {
                                        let hir_ty = &self.hir_types[*type_id];
                                        self.lower_hir_type_with_subst(hir_ty, &local_subst)
                                    })
                                    .collect(),
                                rv_hir::VariantFields::Struct(field_defs) => field_defs
                                    .iter()
                                    .map(|field_def| {
                                        let hir_ty = &self.hir_types[field_def.ty];
                                        self.lower_hir_type_with_subst(hir_ty, &local_subst)
                                    })
                                    .collect(),
                            };
                            MirVariant {
                                name: variant.name,
                                fields,
                            }
                        })
                        .collect();

                    MirType::Enum {
                        name: *name,
                        variants: mir_variants,
                    }
                } else {
                    // Not a struct or enum, probably a built-in type
                    MirType::Named(*name)
                }
            }
            Type::Named { name, args, .. } => {
                // def is None - could be a generic type parameter or named type
                // First check if it's a generic type parameter in the substitution map
                if let Some(concrete_ty) = type_subst.get(name) {
                    return concrete_ty.clone();
                }

                // Try to look up by name as a struct or enum
                let name_lookup = self
                    .structs
                    .iter()
                    .find(|(_, s)| s.name == *name)
                    .map(|(id, _)| *id)
                    .or_else(|| {
                        self.enums
                            .iter()
                            .find(|(_, e)| e.name == *name)
                            .map(|(id, _)| *id)
                    });

                if let Some(def_id) = name_lookup {
                    // Found a struct or enum - recursively convert it with generic substitutions
                    if let Some(struct_def) = self.structs.get(&def_id) {
                        let local_subst = self.build_generic_subst_map(&struct_def.generic_params, args, type_subst);
                        let field_types: Vec<MirType> = struct_def
                            .fields
                            .iter()
                            .map(|field| {
                                let field_hir_ty = &self.hir_types[field.ty];
                                self.lower_hir_type_with_subst(field_hir_ty, &local_subst)
                            })
                            .collect();

                        return MirType::Struct {
                            name: *name,
                            fields: field_types,
                        };
                    } else if let Some(enum_def) = self.enums.get(&def_id) {
                        let local_subst = self.build_generic_subst_map(&enum_def.generic_params, args, type_subst);
                        let mir_variants: Vec<MirVariant> = enum_def
                            .variants
                            .iter()
                            .map(|variant| {
                                let fields = match &variant.fields {
                                    rv_hir::VariantFields::Unit => vec![],
                                    rv_hir::VariantFields::Tuple(type_ids) => type_ids
                                        .iter()
                                        .map(|type_id| {
                                            let hir_ty = &self.hir_types[*type_id];
                                            self.lower_hir_type_with_subst(hir_ty, &local_subst)
                                        })
                                        .collect(),
                                    rv_hir::VariantFields::Struct(field_defs) => field_defs
                                        .iter()
                                        .map(|field_def| {
                                            let hir_ty = &self.hir_types[field_def.ty];
                                            self.lower_hir_type_with_subst(hir_ty, &local_subst)
                                        })
                                        .collect(),
                                };
                                MirVariant {
                                    name: variant.name,
                                    fields,
                                }
                            })
                            .collect();

                        return MirType::Enum {
                            name: *name,
                            variants: mir_variants,
                        };
                    }
                }

                // Not found as struct/enum - check if it's a primitive type
                let name_str = self.interner.resolve(name);
                match name_str.as_str() {
                    "i8" => MirType::Int(rv_hir::IntWidth::I8, rv_hir::Signedness::Signed),
                    "i16" => MirType::Int(rv_hir::IntWidth::I16, rv_hir::Signedness::Signed),
                    "i32" | "int" => {
                        MirType::Int(rv_hir::IntWidth::I32, rv_hir::Signedness::Signed)
                    }
                    "i64" => MirType::Int(rv_hir::IntWidth::I64, rv_hir::Signedness::Signed),
                    "i128" => MirType::Int(rv_hir::IntWidth::I128, rv_hir::Signedness::Signed),
                    "isize" => MirType::Int(rv_hir::IntWidth::Isize, rv_hir::Signedness::Signed),
                    "u8" => MirType::Int(rv_hir::IntWidth::I8, rv_hir::Signedness::Unsigned),
                    "u16" => MirType::Int(rv_hir::IntWidth::I16, rv_hir::Signedness::Unsigned),
                    "u32" => MirType::Int(rv_hir::IntWidth::I32, rv_hir::Signedness::Unsigned),
                    "u64" => MirType::Int(rv_hir::IntWidth::I64, rv_hir::Signedness::Unsigned),
                    "u128" => MirType::Int(rv_hir::IntWidth::I128, rv_hir::Signedness::Unsigned),
                    "usize" => MirType::Int(rv_hir::IntWidth::Isize, rv_hir::Signedness::Unsigned),
                    "f32" => MirType::Float(rv_hir::FloatWidth::F32),
                    "f64" | "float" => MirType::Float(rv_hir::FloatWidth::F64),
                    "char" => MirType::Char,
                    "bool" => MirType::Bool,
                    "String" | "str" => MirType::String,
                    _ => MirType::Named(*name),
                }
            }
            Type::Generic { name, .. } => {
                // Look up in type substitution map first
                if let Some(concrete_ty) = type_subst.get(name) {
                    concrete_ty.clone()
                } else {
                    // No substitution found - keep as named type
                    // This happens for unsubstituted generic parameters
                    MirType::Named(*name)
                }
            }
            Type::Function { params, ret, .. } => {
                let param_types: Vec<MirType> = params
                    .iter()
                    .map(|p| {
                        let param_ty = &self.hir_types[*p];
                        self.lower_hir_type_with_subst(param_ty, type_subst)
                    })
                    .collect();
                let ret_ty = &self.hir_types[**ret];
                MirType::Function {
                    params: param_types,
                    ret: Box::new(self.lower_hir_type_with_subst(ret_ty, type_subst)),
                }
            }
            Type::Tuple { elements, .. } => {
                let element_types: Vec<MirType> = elements
                    .iter()
                    .map(|e| {
                        let elem_ty = &self.hir_types[*e];
                        self.lower_hir_type_with_subst(elem_ty, type_subst)
                    })
                    .collect();
                MirType::Tuple(element_types)
            }
            Type::Reference { inner, mutable, .. } => {
                let inner_ty = &self.hir_types[**inner];
                MirType::Ref {
                    mutable: *mutable,
                    inner: Box::new(self.lower_hir_type_with_subst(inner_ty, type_subst)),
                    lifetime: None,
                }
            }
            Type::QualifiedPath {
                base, assoc_type, ..
            } => {
                // ARCHITECTURE: Resolve associated types by looking up trait impl blocks
                // Example: Self::Item where Self is a type implementing Container trait

                // Step 1: Get the base type
                let base_hir_ty = &self.hir_types[**base];

                // Step 2: Extract TypeDefId from base type
                let base_type_def_id = match base_hir_ty {
                    Type::Named {
                        def: Some(def_id), ..
                    } => Some(*def_id),
                    _ => None,
                };

                // Step 3: Look up associated type in impl blocks
                if let Some(def_id) = base_type_def_id {
                    // Search all impl blocks for one that:
                    // 1. Implements a trait (has trait_ref)
                    // 2. For this type (self_ty matches)
                    // 3. Provides this associated type
                    for impl_block in self.impl_blocks.values() {
                        // Check if this impl is for our type
                        let impl_self_ty = &self.hir_types[impl_block.self_ty];
                        let matches_type = match impl_self_ty {
                            Type::Named {
                                def: Some(impl_def_id),
                                ..
                            } => *impl_def_id == def_id,
                            _ => false,
                        };

                        if matches_type && impl_block.trait_ref.is_some() {
                            // This is a trait impl for our type
                            // Look for the associated type implementation
                            for assoc_impl in &impl_block.associated_type_impls {
                                if assoc_impl.name == *assoc_type {
                                    // Found it! Convert the concrete type to MirType
                                    let concrete_ty = &self.hir_types[assoc_impl.ty];
                                    return self.lower_hir_type_with_subst(concrete_ty, type_subst);
                                }
                            }
                        }
                    }
                }

                // Associated type could not be resolved — no matching impl found
                let assoc_name = self.interner.resolve(assoc_type);
                panic!(
                    "ICE: Could not resolve associated type '{}'. \
                     The trait implementation should have provided this type.",
                    assoc_name
                );
            }
            Type::Pointer { inner, mutable, .. } => {
                let inner_ty = &self.hir_types[**inner];
                MirType::Pointer {
                    mutable: *mutable,
                    inner: Box::new(self.lower_hir_type_with_subst(inner_ty, type_subst)),
                }
            }
            Type::Array { element, .. } => {
                let elem_ty = &self.hir_types[**element];
                MirType::Array {
                    element: Box::new(self.lower_hir_type_with_subst(elem_ty, type_subst)),
                    size: 0,
                }
            }
            Type::Never { .. } => MirType::Never,
            Type::DynTrait { bounds, .. } => {
                let principal = bounds
                    .first()
                    .map(|b| b.name)
                    .unwrap_or_else(|| self.interner.intern("dyn"));
                // Resolve trait by name
                let trait_id = self
                    .traits
                    .iter()
                    .find(|(_, td)| td.name == principal)
                    .map(|(id, _)| *id);
                MirType::DynTrait {
                    principal,
                    trait_id,
                }
            }
            Type::ImplTrait { bounds, .. } => {
                let principal = bounds
                    .first()
                    .map(|b| b.name)
                    .unwrap_or_else(|| self.interner.intern("impl"));
                MirType::ImplTrait { principal }
            }
            Type::Unknown { .. } => {
                panic!(
                    "HIR contains Unknown type. \
                    This indicates the HIR was not properly constructed - all types should be \
                    concrete type references (Named, Generic, Function, etc.), not Unknown."
                )
            }
        }
    }

    /// Get the MIR type of a local variable from the builder.
    fn get_local_type(&self, local: LocalId) -> MirType {
        self.builder.get_local_type(local).unwrap_or_else(|| {
            panic!(
                "ICE: Local {:?} has no type in MIR builder. \
                     All locals should have types assigned at creation time.",
                local
            )
        })
    }

    /// Convert an HIR TypeId to a MirType by looking up the type in the HIR arena
    /// and recursively converting it.
    fn hir_type_to_mir_type(&self, type_id: rv_hir::TypeId) -> MirType {
        let hir_ty = &self.hir_types[type_id];
        self.lower_hir_type_recursive(hir_ty)
    }

    /// Resolve an lvalue expression to a Place pointing at the original storage.
    ///
    /// Unlike `lower_expr` which creates temporaries (copies), this method resolves
    /// directly to the variable's local with appropriate projections. This is critical
    /// for mutation: `p.x = 10` must write to `p`'s storage, not a copy.
    fn resolve_lvalue_place(&mut self, body: &Body, expr_id: ExprId) -> Option<Place> {
        let expr = &body.exprs[expr_id];
        match expr {
            Expr::Variable { name, .. } => self
                .var_locals
                .get(name)
                .map(|&local| Place::from_local(local)),
            Expr::Field { base, field, .. } => {
                let mut base_place = self.resolve_lvalue_place(body, *base)?;

                // Resolve field index using the base expression's type
                let base_ty = self.ty_ctx.get_expr_type(*base)?;
                let normalized_ty = self
                    .ty_ctx
                    .normalize(base_ty)
                    .unwrap_or_else(|e| {
                        panic!(
                            "ICE: Failed to normalize type {:?} during lvalue field resolution: {:?}. \
                             Type inference should have resolved all type variables before MIR lowering.",
                            base_ty, e
                        )
                    });
                let field_idx = self.resolve_field_index(normalized_ty.ty_id(), *field)?;

                base_place.projection.push(PlaceElem::Field { field_idx });
                Some(base_place)
            }
            Expr::Index { base, index, .. } => {
                let mut base_place = self.resolve_lvalue_place(body, *base)?;
                // The index expression is evaluated normally (it's a value, not an lvalue)
                let index_local = self.lower_expr(body, *index);
                base_place.projection.push(PlaceElem::Index(index_local));
                Some(base_place)
            }
            _ => None,
        }
    }

    /// Resolve a field name to its index in a struct
    fn resolve_field_index(&self, ty_id: TyId, field_name: Symbol) -> Option<usize> {
        let ty = self.ty_ctx.types.get(ty_id);

        // Follow type variable substitutions (Var, IntVar, FloatVar)
        let concrete_ty = match &ty.kind {
            TyKind::Var { id: var_id }
            | TyKind::IntVar { id: var_id }
            | TyKind::FloatVar { id: var_id } => {
                if let Some(&subst_ty_id) = self.ty_ctx.subst.get(var_id) {
                    self.ty_ctx.types.get(subst_ty_id)
                } else {
                    ty
                }
            }
            _ => ty,
        };

        // Handle references - auto-deref to find the underlying type
        let inner_ty = match &concrete_ty.kind {
            TyKind::Ref { inner, .. } => {
                let inner_ty_id = **inner;
                let inner_ty = self.ty_ctx.types.get(inner_ty_id);
                // Follow substitutions on the inner type too
                match &inner_ty.kind {
                    TyKind::Var { id: var_id }
                    | TyKind::IntVar { id: var_id }
                    | TyKind::FloatVar { id: var_id } => {
                        if let Some(&subst_ty_id) = self.ty_ctx.subst.get(var_id) {
                            self.ty_ctx.types.get(subst_ty_id)
                        } else {
                            inner_ty
                        }
                    }
                    _ => inner_ty,
                }
            }
            _ => concrete_ty,
        };

        match &inner_ty.kind {
            TyKind::Struct { def_id, .. } => {
                // Look up the struct definition
                if let Some(struct_def) = self.structs.get(def_id) {
                    // Find the field by name
                    struct_def
                        .fields
                        .iter()
                        .position(|field| field.name == field_name)
                } else {
                    None
                }
            }
            TyKind::Named { def, .. } => {
                // Try to resolve the named type to a struct
                if let Some(struct_def) = self.structs.get(def) {
                    struct_def
                        .fields
                        .iter()
                        .position(|field| field.name == field_name)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Resolve a variant name to its index in an enum
    fn resolve_variant_index(&self, type_def_id: TypeDefId, variant_name: Symbol) -> Option<usize> {
        // Look up the enum definition
        if let Some(enum_def) = self.enums.get(&type_def_id) {
            // Find the variant by name
            enum_def
                .variants
                .iter()
                .position(|variant| variant.name == variant_name)
        } else {
            None
        }
    }

    /// Compute the byte size of a MIR type (for pointer arithmetic)
    fn mir_type_size(ty: &MirType) -> usize {
        match ty {
            MirType::Int(width, _) => width.byte_size(),
            MirType::Float(width) => width.byte_size(),
            MirType::Bool => 1,
            MirType::Char => 4,
            MirType::Unit => 0,
            MirType::Ref { inner, .. } | MirType::Pointer { inner, .. } => {
                if inner.ref_is_fat_ptr() { 16 } else { 8 }
            }
            MirType::String => 8,
            MirType::Struct { fields, .. } => fields.iter().map(Self::mir_type_size).sum(),
            MirType::Tuple(elements) => elements.iter().map(Self::mir_type_size).sum(),
            MirType::Array { element, size } => Self::mir_type_size(element) * size,
            _ => 8,
        }
    }

    /// Lower a builtin pointer method call (offset, add, sub, is_null)
    fn lower_pointer_method(
        &mut self,
        result_local: LocalId,
        receiver_local: LocalId,
        method_name: &str,
        arg_operands: &[Operand],
        span: FileSpan,
    ) {
        match method_name {
            "offset" | "add" | "wrapping_add" => {
                // ptr.offset(n) / ptr.add(n) = ptr + n * pointee_size
                let pointee_size = self.pointer_pointee_size_from_local(receiver_local);
                self.emit_pointer_offset(
                    result_local,
                    receiver_local,
                    arg_operands,
                    pointee_size,
                    BinaryOp::Add,
                    span,
                );
            }
            "sub" | "wrapping_sub" => {
                // ptr.sub(n) = ptr - n * pointee_size
                let pointee_size = self.pointer_pointee_size_from_local(receiver_local);
                self.emit_pointer_offset(
                    result_local,
                    receiver_local,
                    arg_operands,
                    pointee_size,
                    BinaryOp::Sub,
                    span,
                );
            }
            "is_null" => {
                // ptr.is_null() = ptr == 0
                let i64_ty = MirType::Int(rv_hir::IntWidth::I64, rv_hir::Signedness::Signed);
                let zero_local =
                    self.builder
                        .new_local(None, i64_ty.clone(), false, compiler_generated_span());
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(zero_local),
                    rvalue: RValue::Use(Operand::Constant(Constant {
                        kind: LiteralKind::Integer(0, None),
                        ty: i64_ty,
                    })),
                    span,
                });
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::BinaryOp {
                        op: BinaryOp::Eq,
                        left: Operand::Copy(Place::from_local(receiver_local)),
                        right: Operand::Copy(Place::from_local(zero_local)),
                    },
                    span,
                });
            }
            _ => {
                panic!(
                    "ICE: Unknown pointer method '{}'. Raw pointers only support \
                     offset, add, sub, wrapping_add, wrapping_sub, is_null",
                    method_name
                );
            }
        }
    }

    /// Get the pointee size for a pointer type using the receiver's MIR type
    fn pointer_pointee_size_from_local(&self, receiver_local: LocalId) -> usize {
        let mir_ty = self.get_local_type(receiver_local);
        if let MirType::Pointer { inner, .. } = &mir_ty {
            Self::mir_type_size(inner)
        } else {
            8 // default to 8 bytes (i64-sized)
        }
    }

    /// Emit MIR for pointer + n * size or pointer - n * size
    fn emit_pointer_offset(
        &mut self,
        result_local: LocalId,
        receiver_local: LocalId,
        arg_operands: &[Operand],
        pointee_size: usize,
        op: BinaryOp,
        span: FileSpan,
    ) {
        let i64_ty = MirType::Int(rv_hir::IntWidth::I64, rv_hir::Signedness::Signed);

        // arg_operands[0] is self (receiver), arg_operands[1] is the offset count
        let offset_operand = if arg_operands.len() > 1 {
            arg_operands[1].clone()
        } else {
            // No offset argument — this shouldn't happen but handle gracefully
            Operand::Constant(Constant {
                kind: LiteralKind::Integer(0, None),
                ty: i64_ty.clone(),
            })
        };

        // size_local = pointee_size constant
        let size_local =
            self.builder
                .new_local(None, i64_ty.clone(), false, compiler_generated_span());
        self.builder.add_statement(Statement::Assign {
            place: Place::from_local(size_local),
            rvalue: RValue::Use(Operand::Constant(Constant {
                kind: LiteralKind::Integer(pointee_size as i64, None),
                ty: i64_ty.clone(),
            })),
            span,
        });

        // byte_offset = n * pointee_size
        let byte_offset_local =
            self.builder
                .new_local(None, i64_ty, false, compiler_generated_span());
        self.builder.add_statement(Statement::Assign {
            place: Place::from_local(byte_offset_local),
            rvalue: RValue::BinaryOp {
                op: BinaryOp::Mul,
                left: offset_operand,
                right: Operand::Copy(Place::from_local(size_local)),
            },
            span,
        });

        // result = ptr +/- byte_offset
        self.builder.add_statement(Statement::Assign {
            place: Place::from_local(result_local),
            rvalue: RValue::BinaryOp {
                op,
                left: Operand::Copy(Place::from_local(receiver_local)),
                right: Operand::Copy(Place::from_local(byte_offset_local)),
            },
            span,
        });
    }

    /// Resolve a method call to a function ID with mutability checking
    fn resolve_method(
        &self,
        receiver_ty: Option<TyId>,
        method_name: Symbol,
        receiver_is_mut: bool,
    ) -> Result<FunctionId, MethodResolutionError> {
        // Receiver type should already be normalized by caller
        // Just extract the type definition ID and handle auto-deref
        let ty = receiver_ty.map(|ty_id| self.ty_ctx.types.get(ty_id));

        // Handle references - auto-deref to find the underlying type
        let resolved_ty = ty.and_then(|t| match &t.kind {
            TyKind::Ref { inner, .. } => Some(self.ty_ctx.types.get(**inner)),
            _ => Some(t),
        });

        // Get the type definition ID from the resolved type
        let type_def_id = resolved_ty.and_then(|inner_ty| {
            match &inner_ty.kind {
                TyKind::Struct { def_id, .. } => Some(*def_id),
                TyKind::Enum { def_id, .. } => Some(*def_id),
                // TyKind::Named has def field containing the TypeDefId directly
                TyKind::Named { def, .. } => Some(*def),
                _ => None,
            }
        });

        // Search all impl blocks for one that matches this type
        for (_impl_id, impl_block) in self.impl_blocks.iter() {
            let hir_ty = &self.hir_types[impl_block.self_ty];

            let impl_type_matches = if let Some(type_def_id) = type_def_id {
                match hir_ty {
                    Type::Named {
                        def: Some(def_id), ..
                    } => def_id == &type_def_id,
                    _ => false,
                }
            } else if let Some(resolved) = resolved_ty {
                // Handle primitive types - match by comparing HIR type names
                let matches = match &resolved.kind {
                    TyKind::Int(w, s) => {
                        // Match any integer type name to its width/signedness
                        if let Type::Named { name, .. } = hir_ty {
                            let n = self.interner.resolve(name);
                            match (w, s) {
                                (rv_hir::IntWidth::I8, rv_hir::Signedness::Signed) => n == "i8",
                                (rv_hir::IntWidth::I16, rv_hir::Signedness::Signed) => n == "i16",
                                (rv_hir::IntWidth::I32, rv_hir::Signedness::Signed) => {
                                    n == "i32" || n == "int"
                                }
                                (rv_hir::IntWidth::I64, rv_hir::Signedness::Signed) => n == "i64",
                                (rv_hir::IntWidth::I128, rv_hir::Signedness::Signed) => n == "i128",
                                (rv_hir::IntWidth::Isize, rv_hir::Signedness::Signed) => {
                                    n == "isize"
                                }
                                (rv_hir::IntWidth::I8, rv_hir::Signedness::Unsigned) => n == "u8",
                                (rv_hir::IntWidth::I16, rv_hir::Signedness::Unsigned) => n == "u16",
                                (rv_hir::IntWidth::I32, rv_hir::Signedness::Unsigned) => n == "u32",
                                (rv_hir::IntWidth::I64, rv_hir::Signedness::Unsigned) => n == "u64",
                                (rv_hir::IntWidth::I128, rv_hir::Signedness::Unsigned) => {
                                    n == "u128"
                                }
                                (rv_hir::IntWidth::Isize, rv_hir::Signedness::Unsigned) => {
                                    n == "usize"
                                }
                            }
                        } else {
                            false
                        }
                    }
                    TyKind::Float(w) => {
                        if let Type::Named { name, .. } = hir_ty {
                            let n = self.interner.resolve(name);
                            match w {
                                rv_hir::FloatWidth::F32 => n == "f32",
                                rv_hir::FloatWidth::F64 => n == "f64" || n == "float",
                            }
                        } else {
                            false
                        }
                    }
                    TyKind::Bool => {
                        matches!(hir_ty, Type::Named { name, .. } if self.interner.resolve(name) == "bool")
                    }
                    TyKind::String => {
                        matches!(hir_ty, Type::Named { name, .. } if self.interner.resolve(name) == "String")
                    }
                    _ => false,
                };
                matches
            } else {
                false
            };

            if impl_type_matches {
                // If this impl block implements a trait, check trait methods
                if let Some(trait_id) = impl_block.trait_ref {
                    if let Some(trait_def) = self.traits.get(&trait_id) {
                        // Check if the method is a trait method
                        if let Some(trait_method) =
                            trait_def.methods.iter().find(|m| m.name == method_name)
                        {
                            // Found a trait method, check mutability requirements
                            if let Some(self_param) = trait_method.self_param {
                                if !self.check_mutability_compatible(self_param, receiver_is_mut) {
                                    return Err(MethodResolutionError::MutabilityMismatch {
                                        required: self_param,
                                        provided_mutable: receiver_is_mut,
                                    });
                                }
                            }

                            // Look it up in the impl block
                            for &func_id in &impl_block.methods {
                                if let Some(func) = self.functions.get(&func_id) {
                                    if func.name == method_name {
                                        return Ok(func_id);
                                    }
                                }
                            }

                            // Method not overridden in impl — use default body if available
                            if let Some(default_fn) = trait_method.default_body {
                                return Ok(default_fn);
                            }
                        } else {
                        }
                    }
                }

                // Also check inherent methods (impl Type { ... })
                for &func_id in &impl_block.methods {
                    if let Some(func) = self.functions.get(&func_id) {
                        if func.name == method_name {
                            // Check mutability requirements for inherent methods
                            if let Some(self_param) = func.self_param {
                                if !self.check_mutability_compatible(self_param, receiver_is_mut) {
                                    return Err(MethodResolutionError::MutabilityMismatch {
                                        required: self_param,
                                        provided_mutable: receiver_is_mut,
                                    });
                                }
                            }
                            return Ok(func_id);
                        }
                    }
                }
            }
        }

        // Second pass: blanket impls (impl<T: Bound> Trait for T)
        for (_impl_id, impl_block) in self.impl_blocks.iter() {
            if !impl_block.is_blanket {
                continue;
            }
            // Only consider blanket impls that implement a trait
            if impl_block.trait_ref.is_none() {
                continue;
            }
            // Check if the receiver type satisfies the blanket impl's bounds
            if !self.type_satisfies_blanket_bounds(type_def_id, impl_block) {
                continue;
            }
            // Search methods in this blanket impl
            for &func_id in &impl_block.methods {
                if let Some(func) = self.functions.get(&func_id) {
                    if func.name == method_name {
                        // Check mutability requirements
                        if let Some(self_param) = func.self_param {
                            if !self.check_mutability_compatible(self_param, receiver_is_mut) {
                                return Err(MethodResolutionError::MutabilityMismatch {
                                    required: self_param,
                                    provided_mutable: receiver_is_mut,
                                });
                            }
                        }
                        return Ok(func_id);
                    }
                }
            }
            // Also check default methods from the trait
            if let Some(trait_id) = impl_block.trait_ref {
                if let Some(trait_def) = self.traits.get(&trait_id) {
                    for method in &trait_def.methods {
                        if method.name == method_name {
                            if let Some(default_fn) = method.default_body {
                                return Ok(default_fn);
                            }
                        }
                    }
                }
            }
        }

        Err(MethodResolutionError::MethodNotFound)
    }

    /// Check if a concrete type satisfies the bounds of a blanket impl's generic parameter.
    fn type_satisfies_blanket_bounds(
        &self,
        type_def_id: Option<rv_hir::TypeDefId>,
        impl_block: &rv_hir::ImplBlock,
    ) -> bool {
        let Some(def_id) = type_def_id else {
            return false;
        };
        // Get the bounds from the first generic parameter (the blanket type param)
        let Some(first_param) = impl_block.generic_params.first() else {
            // No generic params — not a real blanket impl
            return false;
        };
        // Check each required trait bound
        for bound in &first_param.bounds {
            if !self.type_implements_trait(def_id, bound.trait_ref) {
                return false;
            }
        }
        true
    }

    /// Check if a type definition has an impl block implementing the given trait.
    fn type_implements_trait(&self, def_id: rv_hir::TypeDefId, trait_id: rv_hir::TraitId) -> bool {
        self.impl_blocks.values().any(|ib| {
            ib.trait_ref == Some(trait_id) && !ib.is_blanket && {
                let hir_ty = &self.hir_types[ib.self_ty];
                matches!(hir_ty, rv_hir::Type::Named { def: Some(d), .. } if *d == def_id)
            }
        })
    }

    /// Map a binary operator to its corresponding trait name and method name.
    /// Returns None for logical operators (&&, ||) which cannot be overloaded.
    fn binary_op_trait_method(op: &rv_hir::BinaryOp) -> Option<(&'static str, &'static str)> {
        use rv_hir::BinaryOp as HirBinOp;
        match op {
            HirBinOp::Add => Some(("Add", "add")),
            HirBinOp::Sub => Some(("Sub", "sub")),
            HirBinOp::Mul => Some(("Mul", "mul")),
            HirBinOp::Div => Some(("Div", "div")),
            HirBinOp::Mod => Some(("Rem", "rem")),
            HirBinOp::Eq => Some(("PartialEq", "eq")),
            HirBinOp::Ne => Some(("PartialEq", "ne")),
            HirBinOp::Lt => Some(("PartialOrd", "lt")),
            HirBinOp::Le => Some(("PartialOrd", "le")),
            HirBinOp::Gt => Some(("PartialOrd", "gt")),
            HirBinOp::Ge => Some(("PartialOrd", "ge")),
            HirBinOp::BitAnd => Some(("BitAnd", "bitand")),
            HirBinOp::BitOr => Some(("BitOr", "bitor")),
            HirBinOp::BitXor => Some(("BitXor", "bitxor")),
            HirBinOp::Shl => Some(("Shl", "shl")),
            HirBinOp::Shr => Some(("Shr", "shr")),
            HirBinOp::And | HirBinOp::Or => None,
        }
    }

    /// Map a unary operator to its corresponding trait name and method name.
    /// Returns None for operators that cannot be overloaded (Ref, RefMut, Deref).
    fn unary_op_trait_method(op: &rv_hir::UnaryOp) -> Option<(&'static str, &'static str)> {
        use rv_hir::UnaryOp as HirUnOp;
        match op {
            HirUnOp::Neg => Some(("Neg", "neg")),
            HirUnOp::Not => Some(("Not", "not")),
            HirUnOp::BitNot => Some(("Not", "not")),
            _ => None,
        }
    }

    /// Try to resolve a binary operator to a trait method call for non-primitive types.
    /// Returns Some(FunctionId) if a matching trait impl is found, None for primitives.
    fn resolve_operator_trait(
        &mut self,
        left_expr_id: ExprId,
        trait_name: &str,
        method_name: &str,
    ) -> Option<FunctionId> {
        // Get the type of the left operand
        let left_ty = self.ty_ctx.get_expr_type(left_expr_id)?;
        let normalized = self.ty_ctx.normalize(left_ty).ok()?.ty_id();
        let ty = self.ty_ctx.types.get(normalized);

        // Check if this is a primitive type — if so, use built-in ops
        match &ty.kind {
            TyKind::Int(..) | TyKind::Float(..) | TyKind::Bool | TyKind::Char => return None,
            _ => {}
        }

        // For non-primitive types, look up the operator trait
        let trait_name_sym = self.interner.intern(trait_name);
        let method_name_sym = self.interner.intern(method_name);

        // Fast path: if a lang item is registered for this trait, use it directly
        let lang = match trait_name {
            "Add" => Some(rv_hir::LangItem::Add),
            "Sub" => Some(rv_hir::LangItem::Sub),
            "Mul" => Some(rv_hir::LangItem::Mul),
            "Div" => Some(rv_hir::LangItem::Div),
            "Rem" => Some(rv_hir::LangItem::Rem),
            "Neg" => Some(rv_hir::LangItem::Neg),
            "Not" => Some(rv_hir::LangItem::Not),
            "BitAnd" => Some(rv_hir::LangItem::BitAnd),
            "BitOr" => Some(rv_hir::LangItem::BitOr),
            "BitXor" => Some(rv_hir::LangItem::BitXor),
            "Shl" => Some(rv_hir::LangItem::Shl),
            "Shr" => Some(rv_hir::LangItem::Shr),
            "PartialEq" => Some(rv_hir::LangItem::PartialEq),
            "PartialOrd" => Some(rv_hir::LangItem::PartialOrd),
            "Deref" => Some(rv_hir::LangItem::Deref),
            "DerefMut" => Some(rv_hir::LangItem::DerefMut),
            "Index" => Some(rv_hir::LangItem::Index),
            "IndexMut" => Some(rv_hir::LangItem::IndexMut),
            _ => None,
        };
        let trait_id = if let Some(lang_trait_id) = lang.and_then(|l| self.lang_items.get_trait(l))
        {
            lang_trait_id
        } else {
            // Fallback: find the trait by name
            self.traits.iter().find_map(|(id, t)| {
                if t.name == trait_name_sym {
                    Some(*id)
                } else {
                    None
                }
            })?
        };

        // Get the TypeDefId from the operand type
        let type_def_id = match &ty.kind {
            TyKind::Struct { def_id, .. } | TyKind::Enum { def_id, .. } => Some(*def_id),
            TyKind::Ref { inner, .. } => {
                let inner_ty = self.ty_ctx.types.get(**inner);
                match &inner_ty.kind {
                    TyKind::Struct { def_id, .. } | TyKind::Enum { def_id, .. } => Some(*def_id),
                    _ => None,
                }
            }
            _ => None,
        }?;

        // Find the impl block that implements this trait for this type
        for (_impl_id, impl_block) in self.impl_blocks.iter() {
            if impl_block.trait_ref != Some(trait_id) {
                continue;
            }
            // Check if this impl block is for our type
            let hir_ty = &self.hir_types[impl_block.self_ty];
            let matches = match hir_ty {
                Type::Named { def: Some(def), .. } => *def == type_def_id,
                _ => false,
            };
            if matches {
                // Find the method in this impl block
                for &func_id in &impl_block.methods {
                    if let Some(func) = self.functions.get(&func_id) {
                        if func.name == method_name_sym {
                            return Some(func_id);
                        }
                    }
                }
            }
        }

        // Second pass: blanket impls for operator traits
        for (_impl_id, impl_block) in self.impl_blocks.iter() {
            if !impl_block.is_blanket || impl_block.trait_ref != Some(trait_id) {
                continue;
            }
            if self.type_satisfies_blanket_bounds(Some(type_def_id), impl_block) {
                for &func_id in &impl_block.methods {
                    if let Some(func) = self.functions.get(&func_id) {
                        if func.name == method_name_sym {
                            return Some(func_id);
                        }
                    }
                }
            }
        }

        None
    }

    /// Check if a type is Copy (can be duplicated without moving).
    ///
    /// Primitives are implicitly Copy. User-defined types are Copy if they implement
    /// the Copy trait (found via lang item registry or by trait name).
    fn is_copy_type(&self, mir_ty: &MirType) -> bool {
        match mir_ty {
            // Primitives are always Copy
            MirType::Int(..)
            | MirType::Float(..)
            | MirType::Bool
            | MirType::Char
            | MirType::Unit
            | MirType::String => true,
            // Shared references are Copy
            MirType::Ref { mutable: false, .. } => true,
            // Raw pointers are Copy
            MirType::Pointer { .. } => true,
            // Tuples are Copy if all elements are Copy
            MirType::Tuple(elements) => elements.iter().all(|e| self.is_copy_type(e)),
            // Arrays are Copy if the element type is Copy
            MirType::Array { element, .. } => self.is_copy_type(element),
            // Struct/Enum types: check for Copy trait impl
            MirType::Struct { name, .. } => self.has_copy_impl_by_name(*name),
            MirType::Named(name) => self.has_copy_impl_by_name(*name),
            // Mutable references and other types are not Copy
            _ => false,
        }
    }

    /// Check if a named type has a Copy trait implementation.
    fn has_copy_impl_by_name(&self, type_name: rv_intern::Symbol) -> bool {
        // Find the TypeDefId for this type name
        let type_def_id = self
            .structs
            .iter()
            .find(|(_, s)| s.name == type_name)
            .map(|(id, _)| *id)
            .or_else(|| {
                self.enums
                    .iter()
                    .find(|(_, e)| e.name == type_name)
                    .map(|(id, _)| *id)
            });

        let Some(def_id) = type_def_id else {
            return false;
        };

        self.has_copy_impl(def_id)
    }

    /// Check if a type definition has an implementation of the Copy trait.
    fn has_copy_impl(&self, def_id: TypeDefId) -> bool {
        // Try lang item registry first
        let copy_trait_id = self.lang_items.get_trait(rv_hir::LangItem::Copy);

        // Fallback: search by trait name "Copy"
        let copy_trait_id = copy_trait_id.or_else(|| {
            let copy_name = self.interner.intern("Copy");
            self.traits.iter().find_map(
                |(id, t)| {
                    if t.name == copy_name { Some(*id) } else { None }
                },
            )
        });

        let Some(trait_id) = copy_trait_id else {
            return false;
        };

        // Search impl blocks for one implementing Copy for this type
        self.impl_blocks.values().any(|impl_block| {
            if impl_block.trait_ref != Some(trait_id) {
                return false;
            }
            let hir_ty = &self.hir_types[impl_block.self_ty];
            matches!(hir_ty, Type::Named { def: Some(def), .. } if *def == def_id)
        })
    }

    /// Create an operand for reading a local variable, choosing Copy or Move
    /// based on whether the local's type is Copy.
    fn operand_for_local(&self, local: LocalId) -> Operand {
        let mir_ty = self.get_local_type(local);
        if self.is_copy_type(&mir_ty) {
            Operand::Copy(Place::from_local(local))
        } else {
            Operand::Move(Place::from_local(local))
        }
    }

    /// Check if receiver mutability is compatible with method requirements
    fn check_mutability_compatible(&self, required: SelfParam, receiver_is_mut: bool) -> bool {
        match required {
            SelfParam::Value => {
                // Method takes self by value - works with both mut and immut
                true
            }
            SelfParam::Ref => {
                // Method takes &self - works with both mut and immut
                true
            }
            SelfParam::MutRef => {
                // Method takes &mut self - requires mutable receiver
                receiver_is_mut
            }
        }
    }
}

/// Convert a literal to u128 for switch target
fn literal_to_u128(kind: &LiteralKind) -> Option<u128> {
    match kind {
        LiteralKind::Integer(val, _) => Some(*val as u128),
        LiteralKind::Bool(b) => Some(if *b { 1 } else { 0 }),
        _ => None,
    }
}

/// Get the span of an expression
fn get_expr_span(expr: &Expr) -> rv_span::FileSpan {
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
        | Expr::PathCall { span, .. }
        | Expr::EnumVariant { span, .. }
        | Expr::Closure { span, .. }
        | Expr::Assign { span, .. }
        | Expr::CompoundAssign { span, .. }
        | Expr::WhileLoop { span, .. }
        | Expr::WhileLet { span, .. }
        | Expr::IfLet { span, .. }
        | Expr::Loop { span, .. }
        | Expr::Break { span, .. }
        | Expr::Continue { span, .. }
        | Expr::Array { span, .. }
        | Expr::Tuple { span, .. }
        | Expr::Index { span, .. }
        | Expr::Cast { span, .. }
        | Expr::UnsafeBlock { span, .. }
        | Expr::Error { span, .. }
        | Expr::Range { span, .. }
        | Expr::Try { span, .. }
        | Expr::ForLoop { span, .. }
        | Expr::Box { span, .. } => *span,
    }
}

/// Get the span of a pattern
fn get_pattern_span(pattern: &Pattern) -> rv_span::FileSpan {
    match pattern {
        Pattern::Wildcard { span }
        | Pattern::Binding { span, .. }
        | Pattern::Literal { span, .. }
        | Pattern::Tuple { span, .. }
        | Pattern::Struct { span, .. }
        | Pattern::Enum { span, .. }
        | Pattern::Or { span, .. }
        | Pattern::Range { span, .. }
        | Pattern::Slice { span, .. } => *span,
    }
}

impl<'ctx> LoweringContext<'ctx> {
    /// Lower pattern bindings by copying the scrutinee value to bound variables
    fn lower_pattern_bindings(&mut self, pattern: &Pattern, scrutinee_local: LocalId, body: &Body) {
        match pattern {
            Pattern::Binding {
                name, sub_pattern, ..
            } => {
                // Create a new MIR local for this binding
                let mir_local = self.builder.new_local(
                    Some(*name),
                    MirType::Unit,
                    false,
                    compiler_generated_span(),
                );

                // Get span from the pattern itself
                let pattern_span = get_pattern_span(pattern);

                // Copy scrutinee to the bound variable
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(mir_local),
                    rvalue: RValue::Use(Operand::Copy(Place::from_local(scrutinee_local))),
                    span: pattern_span,
                });

                // Store mapping for variable resolution
                self.var_locals.insert(*name, mir_local);

                // If there's a sub-pattern (@ pattern), recursively match it against the same scrutinee
                if let Some(sub_pat_id) = sub_pattern {
                    let sub_pat = &body.patterns[**sub_pat_id];
                    self.lower_pattern_bindings(sub_pat, scrutinee_local, body);
                }
            }
            Pattern::Tuple { patterns, .. } => {
                // For tuple patterns, we need to extract each field and bind recursively
                // Get the span from the overall tuple pattern for field extraction operations
                let tuple_span = get_pattern_span(pattern);

                for (idx, pat_id) in patterns.iter().enumerate() {
                    // Create a local to hold the extracted field
                    let field_local = self.builder.new_local(
                        None,
                        MirType::Unit,
                        false,
                        compiler_generated_span(),
                    );

                    // Extract the field using Place projection
                    let field_place = Place {
                        local: scrutinee_local,
                        projection: vec![PlaceElem::Field { field_idx: idx }],
                    };

                    // Copy the field to the local (use tuple pattern's span for field access)
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(field_local),
                        rvalue: RValue::Use(Operand::Copy(field_place)),
                        span: tuple_span,
                    });

                    // Recursively bind sub-pattern with the extracted field
                    let sub_pattern = &body.patterns[*pat_id];
                    self.lower_pattern_bindings(sub_pattern, field_local, body);
                }
            }
            Pattern::Struct { fields, ty, .. } => {
                // For struct patterns, we need to extract each field and bind recursively
                // Get the span from the overall struct pattern for field extraction operations
                let struct_span = get_pattern_span(pattern);

                // First, resolve the struct definition to get field indices
                if let Type::Named {
                    def: Some(def_id), ..
                } = &self.hir_types[*ty]
                {
                    if let Some(struct_def) = self.structs.get(def_id) {
                        for (field_name, pat_id) in fields {
                            // Find the field index in the struct definition
                            if let Some((field_idx, _)) = struct_def
                                .fields
                                .iter()
                                .enumerate()
                                .find(|(_, f)| f.name == *field_name)
                            {
                                // Create a local to hold the extracted field
                                let field_local = self.builder.new_local(
                                    None,
                                    MirType::Unit,
                                    false,
                                    compiler_generated_span(),
                                );

                                // Extract the field using Place projection
                                let field_place = Place {
                                    local: scrutinee_local,
                                    projection: vec![PlaceElem::Field { field_idx }],
                                };

                                // Copy the field to the local (use struct pattern's span for field access)
                                self.builder.add_statement(Statement::Assign {
                                    place: Place::from_local(field_local),
                                    rvalue: RValue::Use(Operand::Copy(field_place)),
                                    span: struct_span,
                                });

                                // Recursively bind sub-pattern with the extracted field
                                let sub_pattern = &body.patterns[*pat_id];
                                self.lower_pattern_bindings(sub_pattern, field_local, body);
                            }
                        }
                    }
                }
            }
            Pattern::Or { patterns, .. } => {
                // For or-patterns, we only bind if one alternative matches
                // In practice, or-patterns typically don't have bindings
                // But if they do, we bind the first pattern's bindings
                if let Some(first_pat_id) = patterns.first() {
                    let first_pattern = &body.patterns[*first_pat_id];
                    self.lower_pattern_bindings(first_pattern, scrutinee_local, body);
                }
            }
            Pattern::Enum { sub_patterns, .. } => {
                // For enum patterns with sub-patterns like Some(x), extract data fields.
                // Interpreter stores enum as: { variant_idx, fields: [...] }
                // The discriminant is NOT stored in the fields array, so we use direct indexing.
                // sub_pattern[i] corresponds to PlaceElem::Field { field_idx: i }.
                if !sub_patterns.is_empty() {
                    let enum_span = get_pattern_span(pattern);

                    for (idx, sub_pat_id) in sub_patterns.iter().enumerate() {
                        // Create a local to hold the extracted enum data field
                        let field_local = self.builder.new_local(
                            None,
                            MirType::Unit,
                            false,
                            compiler_generated_span(),
                        );

                        // Extract the data field directly (no discriminant offset)
                        let field_place = Place {
                            local: scrutinee_local,
                            projection: vec![PlaceElem::Field { field_idx: idx }],
                        };

                        self.builder.add_statement(Statement::Assign {
                            place: Place::from_local(field_local),
                            rvalue: RValue::Use(Operand::Copy(field_place)),
                            span: enum_span,
                        });

                        // Recursively bind the sub-pattern with the extracted field
                        let sub_pattern = &body.patterns[*sub_pat_id];
                        self.lower_pattern_bindings(sub_pattern, field_local, body);
                    }
                }
            }
            Pattern::Range { .. } | Pattern::Literal { .. } | Pattern::Wildcard { .. } => {
                // No bindings to handle
            }
            Pattern::Slice {
                prefix,
                rest,
                suffix,
                span,
            } => {
                // For slice patterns, extract elements by index
                // prefix patterns are at indices 0, 1, 2, ...
                // suffix patterns are at indices len - suffix.len(), len - suffix.len() + 1, ...
                // rest pattern (if any) captures the middle elements

                let i64_ty = MirType::Int(IntWidth::I64, Signedness::Signed);

                // Get the length of the scrutinee (for suffix pattern indexing)
                // For arrays, we need to get the size from the type
                // For slices, extract from the fat pointer
                let scrutinee_ty = self.get_local_type(scrutinee_local);
                let len_local = self.builder.new_local(None, i64_ty.clone(), false, *span);

                match &scrutinee_ty {
                    MirType::Array { size, .. } => {
                        // Array length is known at compile time
                        self.builder.add_statement(Statement::Assign {
                            place: Place::from_local(len_local),
                            rvalue: RValue::Use(Operand::Constant(Constant {
                                kind: LiteralKind::Integer(*size as i64, Some((IntWidth::I64, Signedness::Signed))),
                                ty: i64_ty.clone(),
                            })),
                            span: *span,
                        });
                    }
                    MirType::Slice { .. } => {
                        // Extract length from fat pointer (field 1)
                        let len_place = Place {
                            local: scrutinee_local,
                            projection: vec![PlaceElem::Field { field_idx: 1 }],
                        };
                        self.builder.add_statement(Statement::Assign {
                            place: Place::from_local(len_local),
                            rvalue: RValue::Use(Operand::Copy(len_place)),
                            span: *span,
                        });
                    }
                    _ => {
                        // For other types, assume length 0 (shouldn't happen with well-typed code)
                        self.builder.add_statement(Statement::Assign {
                            place: Place::from_local(len_local),
                            rvalue: RValue::Use(Operand::Constant(Constant {
                                kind: LiteralKind::Integer(0, Some((IntWidth::I64, Signedness::Signed))),
                                ty: i64_ty.clone(),
                            })),
                            span: *span,
                        });
                    }
                }

                // Extract prefix elements (indices 0, 1, 2, ...)
                for (idx, pat_id) in prefix.iter().enumerate() {
                    let elem_local = self.builder.new_local(
                        None,
                        MirType::Unit,
                        false,
                        compiler_generated_span(),
                    );

                    // Create index local for the element
                    let idx_local = self.builder.new_local(None, i64_ty.clone(), false, *span);
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(idx_local),
                        rvalue: RValue::Use(Operand::Constant(Constant {
                            kind: LiteralKind::Integer(idx as i64, Some((IntWidth::I64, Signedness::Signed))),
                            ty: i64_ty.clone(),
                        })),
                        span: *span,
                    });

                    // Extract element at index
                    let elem_place = Place {
                        local: scrutinee_local,
                        projection: vec![PlaceElem::Index(idx_local)],
                    };
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(elem_local),
                        rvalue: RValue::Use(Operand::Copy(elem_place)),
                        span: *span,
                    });

                    let sub_pattern = &body.patterns[*pat_id];
                    self.lower_pattern_bindings(sub_pattern, elem_local, body);
                }

                // If there's a rest pattern binding, create a sub-slice
                // rest captures slice[prefix.len()..len-suffix.len()]
                if let Some(rest_pat_id) = rest {
                    let rest_pattern = &body.patterns[*rest_pat_id];

                    // Calculate rest slice bounds
                    let rest_start = self.builder.new_local(None, i64_ty.clone(), false, *span);
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(rest_start),
                        rvalue: RValue::Use(Operand::Constant(Constant {
                            kind: LiteralKind::Integer(prefix.len() as i64, Some((IntWidth::I64, Signedness::Signed))),
                            ty: i64_ty.clone(),
                        })),
                        span: *span,
                    });

                    let suffix_len_const = self.builder.new_local(None, i64_ty.clone(), false, *span);
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(suffix_len_const),
                        rvalue: RValue::Use(Operand::Constant(Constant {
                            kind: LiteralKind::Integer(suffix.len() as i64, Some((IntWidth::I64, Signedness::Signed))),
                            ty: i64_ty.clone(),
                        })),
                        span: *span,
                    });

                    let rest_end = self.builder.new_local(None, i64_ty.clone(), false, *span);
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(rest_end),
                        rvalue: RValue::BinaryOp {
                            op: BinaryOp::Sub,
                            left: Operand::Copy(Place::from_local(len_local)),
                            right: Operand::Copy(Place::from_local(suffix_len_const)),
                        },
                        span: *span,
                    });

                    // Create a sub-slice for rest binding
                    // For now, bind the scrutinee itself (full sub-slice extraction is complex)
                    self.lower_pattern_bindings(rest_pattern, scrutinee_local, body);
                }

                // Extract suffix elements (indices len - suffix.len() + offset)
                for (offset, pat_id) in suffix.iter().enumerate() {
                    let elem_local = self.builder.new_local(
                        None,
                        MirType::Unit,
                        false,
                        compiler_generated_span(),
                    );

                    // Calculate index: len - suffix.len() + offset
                    let suffix_len_const = self.builder.new_local(None, i64_ty.clone(), false, *span);
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(suffix_len_const),
                        rvalue: RValue::Use(Operand::Constant(Constant {
                            kind: LiteralKind::Integer(suffix.len() as i64, Some((IntWidth::I64, Signedness::Signed))),
                            ty: i64_ty.clone(),
                        })),
                        span: *span,
                    });

                    let base_idx = self.builder.new_local(None, i64_ty.clone(), false, *span);
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(base_idx),
                        rvalue: RValue::BinaryOp {
                            op: BinaryOp::Sub,
                            left: Operand::Copy(Place::from_local(len_local)),
                            right: Operand::Copy(Place::from_local(suffix_len_const)),
                        },
                        span: *span,
                    });

                    let offset_const = self.builder.new_local(None, i64_ty.clone(), false, *span);
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(offset_const),
                        rvalue: RValue::Use(Operand::Constant(Constant {
                            kind: LiteralKind::Integer(offset as i64, Some((IntWidth::I64, Signedness::Signed))),
                            ty: i64_ty.clone(),
                        })),
                        span: *span,
                    });

                    let idx_local = self.builder.new_local(None, i64_ty.clone(), false, *span);
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(idx_local),
                        rvalue: RValue::BinaryOp {
                            op: BinaryOp::Add,
                            left: Operand::Copy(Place::from_local(base_idx)),
                            right: Operand::Copy(Place::from_local(offset_const)),
                        },
                        span: *span,
                    });

                    // Extract element at calculated index
                    let elem_place = Place {
                        local: scrutinee_local,
                        projection: vec![PlaceElem::Index(idx_local)],
                    };
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(elem_local),
                        rvalue: RValue::Use(Operand::Copy(elem_place)),
                        span: *span,
                    });

                    let sub_pattern = &body.patterns[*pat_id];
                    self.lower_pattern_bindings(sub_pattern, elem_local, body);
                }
            }
        }
    }
}
