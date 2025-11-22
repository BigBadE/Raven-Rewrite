//! HIR → MIR lowering

use rv_mir::{
    AggregateKind, BinaryOp, Constant, LocalId, MirBuilder, MirFunction, MirType, MirVariant,
    Operand, Place, PlaceElem, RValue, Statement, Terminator, UnaryOp,
};
use rustc_hash::FxHashMap;
use la_arena::Arena;
use rv_hir::{Body, DefId, EnumDef, Expr, ExprId, Function, FunctionId, ImplBlock, ImplId, LiteralKind, Pattern, SelfParam, Stmt, StmtId, StructDef, TraitDef, TraitId, Type, TypeDefId};
use rv_intern::{Interner, Symbol};
use rv_ty::{TyContext, TyId, TyKind};
use std::collections::HashMap;

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
        }
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
    ) -> MirFunction {
        let mut builder = MirBuilder::new(function.id);
        builder.set_param_count(function.parameters.len());
        let mut ctx = Self::new(builder, ty_ctx, structs, enums, impl_blocks, functions, hir_types, traits, interner);

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
            let ty_id = ctx.ty_ctx.get_def_type(def_id)
                .unwrap_or_else(|| {
                    panic!(
                        "COMPILER BUG: Parameter '{}' (function '{}', DefId={:?}) has no inferred type. \
                         Type inference MUST populate def_types before MIR lowering.",
                        ctx.interner.resolve(&param.name),
                        ctx.interner.resolve(&function.name),
                        def_id
                    )
                });

            // Normalize to resolve type variables
            // If normalization fails (unresolved type variable), use Int as default
            let normalized_ty = ctx.ty_ctx.normalize(ty_id)
                .unwrap_or_else(|_| {
                    // Use Int type as default for unresolved type variables
                    use rv_ty::NormalizedTy;
                    NormalizedTy::wrap_child(ctx.ty_ctx.types.int())
                });

            let mir_ty = ctx.lower_type(normalized_ty);
            let param_local = ctx.builder.new_local(Some(param.name), mir_ty, false);
            ctx.var_locals.insert(param.name, param_local);
        }

        // Create return local AFTER parameters
        let return_ty = if let Some(ty_id) = ctx.ty_ctx.get_expr_type(function.body.root_expr) {
            match ctx.ty_ctx.normalize(ty_id) {
                Ok(normalized_ty) => ctx.lower_type(normalized_ty),
                Err(_) => MirType::Unit, // Normalization failed - default to Unit
            }
        } else {
            MirType::Unit
        };
        let return_local = ctx.builder.new_local(None, return_ty, false);
        ctx.return_local = Some(return_local);

        // Lower function body
        ctx.lower_body(&function.body);

        // Set return terminator
        ctx.builder.set_terminator(Terminator::Return {
            value: Some(Operand::Copy(Place::from_local(return_local))),
        });

        ctx.builder.finish()
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
    ) -> MirFunction {
        let mut builder = MirBuilder::new(instance_id);
        builder.set_param_count(function.parameters.len());
        let mut ctx = Self::new(builder, ty_ctx, structs, enums, impl_blocks, functions, hir_types, traits, interner);

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
                        panic!("Generic parameter '{}' missing from type_subst map",
                            ctx.interner.resolve(name));
                    }
                }
                // Non-generic type - use DefId lookup
                _ => {
                    let local_id = rv_hir::LocalId(param_idx as u32);
                    let def_id = rv_hir::DefId::Local {
                        func: function.id,
                        local: local_id,
                    };

                    let ty_id = ctx.ty_ctx.get_def_type(def_id)
                        .unwrap_or_else(|| {
                            panic!(
                                "COMPILER BUG: Parameter '{:?}' (index {}, DefId={:?}) has no inferred type. \
                                 Type inference should have assigned a type to all parameters.",
                                param.name, param_idx, def_id
                            )
                        });

                    // Try to normalize, but if it fails (unresolved type variable), use Int as default
                    // This can happen for generic parameters without concrete substitutions
                    let normalized_ty = ctx.ty_ctx.normalize(ty_id)
                        .unwrap_or_else(|_| {
                            // Use Int type as default for unresolved type variables
                            use rv_ty::NormalizedTy;
                            NormalizedTy::wrap_child(ctx.ty_ctx.types.int())
                        });

                    ctx.lower_type(normalized_ty)
                }
            };

            let param_local = ctx.builder.new_local(Some(param.name), param_ty, false);
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
                        panic!("Generic return type '{}' missing from type_subst map",
                            ctx.interner.resolve(name));
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
                                Err(_) => MirType::Unit,
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
                                panic!("Generic return type '{}' missing from type_subst map",
                                    ctx.interner.resolve(name));
                            }
                        }
                        _ => {
                            // Non-generic inner type, use type inference
                            if let Some(ty_id) = ctx.ty_ctx.get_expr_type(function.body.root_expr) {
                                match ctx.ty_ctx.normalize(ty_id) {
                                    Ok(normalized_ty) => ctx.lower_type(normalized_ty),
                                    Err(_) => MirType::Unit,
                                }
                            } else {
                                MirType::Unit
                            }
                        }
                    };
                    MirType::Ref {
                        mutable: *mutable,
                        inner: Box::new(inner_mir_ty),
                    }
                }
                // Other types, use type inference
                _ => {
                    if let Some(ty_id) = ctx.ty_ctx.get_expr_type(function.body.root_expr) {
                        match ctx.ty_ctx.normalize(ty_id) {
                            Ok(normalized_ty) => ctx.lower_type(normalized_ty),
                            Err(_) => MirType::Unit,
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
                    Err(_) => MirType::Unit,
                }
            } else {
                MirType::Unit
            }
        };
        let return_local = ctx.builder.new_local(None, return_ty, false);
        ctx.return_local = Some(return_local);

        // Lower function body
        ctx.lower_body(&function.body);

        // Set return terminator
        ctx.builder.set_terminator(Terminator::Return {
            value: Some(Operand::Copy(Place::from_local(return_local))),
        });

        ctx.builder.finish()
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
            Ok(normalized_ty) => {
                self.lower_type(normalized_ty)
            }
            Err(e) => {
                panic!(
                    "COMPILER BUG: Type normalization failed for expression {:?} with type {:?}. \
                    Error: {:?}. This indicates unresolved type variables that should have been \
                    resolved by type inference.",
                    expr, ty_id, e
                )
            }
        };

        // Create a temporary for the result
        let result_local = self.builder.new_local(None, mir_ty.clone(), false);

        match expr {
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

            Expr::Variable { name, def: _, span } => {
                // Look up variable in var_locals (set by let bindings and parameters)
                let var_local = self.var_locals.get(name).copied();

                if let Some(var_local) = var_local {
                    // Copy the value from the variable's local to the result local
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Use(Operand::Copy(Place::from_local(var_local))),
                        span: *span,
                    });
                } else {
                    // Variable not found - return Unit for now
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
            }

            Expr::BinaryOp {
                op,
                left,
                right,
                span,
            } => {
                let left_local = self.lower_expr(body, *left);
                let right_local = self.lower_expr(body, *right);

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

            Expr::UnaryOp { op, operand, span } => {
                let operand_local = self.lower_expr(body, *operand);

                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::UnaryOp {
                        op: UnaryOp::from(*op),
                        operand: Operand::Copy(Place::from_local(operand_local)),
                    },
                    span: *span,
                });
            }

            Expr::Block {
                statements,
                expr,
                span,
            } => {
                // Lower statements
                for stmt_id in statements {
                    self.lower_stmt(body, *stmt_id);
                }

                // Lower trailing expression if present
                if let Some(trailing_expr) = expr {
                    let trailing_local = self.lower_expr(body, *trailing_expr);
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Use(Operand::Copy(Place::from_local(trailing_local))),
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
                use rv_hir::exhaustiveness::{is_exhaustive, ExhaustivenessResult};
                let exhaustiveness = is_exhaustive(arms, body, self.structs, self.enums);
                if let ExhaustivenessResult::NonExhaustive { missing_patterns } = exhaustiveness {
                    eprintln!("Warning: match is not exhaustive");
                    eprintln!("Missing patterns: {}", missing_patterns.join(", "));
                }

                // Lower scrutinee
                let scrutinee_local = self.lower_expr(body, *scrutinee);

                // Create blocks for each arm + after block
                let after_block = self.builder.new_block();
                let arm_blocks: Vec<_> = arms.iter().map(|_| self.builder.new_block()).collect();

                // Create otherwise block (unreachable for exhaustive matches)
                let otherwise_block = self.builder.new_block();

                // Build switch on scrutinee
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
                        Pattern::Or { patterns: or_patterns, .. } => {
                            // Or-pattern: map each alternative to the same block
                            for pat_id in or_patterns {
                                if let Pattern::Literal { kind, .. } = &body.patterns[*pat_id] {
                                    if let Some(value) = literal_to_u128(kind) {
                                        targets.insert(value, arm_blocks[arm_idx]);
                                    }
                                }
                            }
                        }
                        Pattern::Range { start, end, inclusive, .. } => {
                            // Range pattern: map all values in range to arm block
                            if let (Some(start_val), Some(end_val)) = (literal_to_u128(start), literal_to_u128(end)) {
                                let end_inclusive = if *inclusive { end_val } else { end_val.saturating_sub(1) };
                                for value in start_val..=end_inclusive {
                                    targets.insert(value, arm_blocks[arm_idx]);
                                }
                            }
                        }
                        _ => {
                            // Other patterns (tuple, struct, enum) - treat as wildcard for now
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
                    discriminant: Operand::Copy(Place::from_local(scrutinee_local)),
                    targets,
                    otherwise: otherwise_target,
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
                struct_name: _,
                def: _,
                fields,
                span,
            } => {
                // Lower field initializers
                let field_operands: Vec<Operand> = fields
                    .iter()
                    .map(|(_, field_expr)| {
                        let field_local = self.lower_expr(body, *field_expr);
                        Operand::Copy(Place::from_local(field_local))
                    })
                    .collect();

                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Aggregate {
                        kind: AggregateKind::Struct,
                        operands: field_operands,
                    },
                    span: *span,
                });
            }

            Expr::Field { base, field, span } => {
                // Lower base expression
                let base_local = self.lower_expr(body, *base);

                // Get the type of the base expression from type inference
                let base_ty_id = self.ty_ctx.get_expr_type(*base)
                    .unwrap_or_else(|| {
                        panic!(
                            "COMPILER BUG: Field access base expression has no inferred type. \
                             Type inference should have assigned a type to all expressions."
                        )
                    });

                // Resolve field name to index
                let field_idx = self.resolve_field_index(base_ty_id, *field)
                    .unwrap_or_else(|| {
                        panic!(
                            "COMPILER BUG: Failed to resolve field '{}' on type {:?}. \
                             Type checker should have validated field access.",
                            self.interner.resolve(field), base_ty_id
                        )
                    });

                let field_place = Place {
                    local: base_local,
                    projection: vec![PlaceElem::Field { field_idx }],
                };

                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Copy(field_place)),
                    span: *span,
                });
            }

            Expr::EnumVariant {
                enum_name: _,
                variant,
                def,
                fields,
                span,
            } => {
                // Lower variant fields
                let field_operands: Vec<Operand> = fields
                    .iter()
                    .map(|field_expr| {
                        let field_local = self.lower_expr(body, *field_expr);
                        Operand::Copy(Place::from_local(field_local))
                    })
                    .collect();

                // Resolve variant name to index
                let type_def_id = def.unwrap_or_else(|| {
                    panic!(
                        "COMPILER BUG: Enum variant construct '{}' has no type definition. \
                         Name resolution should have linked all enum variants to their type definitions.",
                        self.interner.resolve(variant)
                    )
                });

                let variant_idx = self.resolve_variant_index(type_def_id, *variant)
                    .unwrap_or_else(|| {
                        panic!(
                            "COMPILER BUG: Failed to resolve variant '{}' in type def {:?}. \
                             Type checker should have validated variant access.",
                            self.interner.resolve(variant), type_def_id
                        )
                    });

                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Aggregate {
                        kind: AggregateKind::Enum { variant_idx },
                        operands: field_operands,
                    },
                    span: *span,
                });
            }

            Expr::Call {
                callee,
                args,
                span,
            } => {
                // Lower arguments
                let arg_operands: Vec<Operand> = args
                    .iter()
                    .map(|arg_expr| {
                        let arg_local = self.lower_expr(body, *arg_expr);
                        Operand::Copy(Place::from_local(arg_local))
                    })
                    .collect();

                // Extract the function ID from the callee expression
                let callee_expr = &body.exprs[*callee];
                if let Expr::Variable { def: Some(DefId::Function(func_id)), .. } = callee_expr {
                    // Emit a function call
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Call {
                            func: *func_id,
                            args: arg_operands,
                        },
                        span: *span,
                    });
                } else {
                    // Callee is not a direct function reference, return unit for now
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
            }

            Expr::MethodCall {
                receiver,
                method,
                args,
                span,
            } => {

                // Lower receiver
                let receiver_local = self.lower_expr(body, *receiver);

                // Lower arguments
                let mut arg_operands: Vec<Operand> = vec![
                    // First argument is the receiver (self)
                    Operand::Copy(Place::from_local(receiver_local))
                ];

                // Add the rest of the arguments
                for arg_expr in args {
                    let arg_local = self.lower_expr(body, *arg_expr);
                    arg_operands.push(Operand::Copy(Place::from_local(arg_local)));
                }

                // Resolve method name to function ID with mutability checking
                let receiver_ty = self.ty_ctx.get_expr_type(*receiver);

                // Get receiver mutability from type context (set during type inference)
                let receiver_is_mut = self.ty_ctx.receiver_mutability
                    .get(&expr_id)
                    .copied()
                    .unwrap_or(false);

                // ARCHITECTURE: Method resolution MUST succeed - no fallbacks allowed (per user directive)
                let func_id = self.resolve_method(receiver_ty, *method, receiver_is_mut)
                    .unwrap_or_else(|err| {
                        panic!(
                            "COMPILER BUG: Method resolution failed for method '{:?}': {:?}",
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

            Expr::Closure {
                params: _,
                return_type: _,
                body: _,
                captures,
                span,
            } => {
                // Lower closure to a struct containing captured variables
                // The closure is represented as an aggregate with:
                // - Field 0..N: captured variables
                // - No function pointer in MIR (handled by backends)

                let capture_operands: Vec<Operand> = captures
                    .iter()
                    .filter_map(|capture| {
                        // Look up the captured variable
                        self.var_locals.get(capture).map(|&local| {
                            Operand::Copy(Place::from_local(local))
                        })
                    })
                    .collect();

                // Create a struct aggregate for the closure environment
                // Backends will need to handle calling closures specially
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Aggregate {
                        kind: AggregateKind::Struct,
                        operands: capture_operands,
                    },
                    span: *span,
                });
            }
        }

        // Cache the result
        self.expr_locals.insert(expr_id, result_local);
        result_local
    }

    /// Lower a statement
    fn lower_stmt(&mut self, body: &Body, stmt_id: StmtId) {
        let stmt = &body.stmts[stmt_id];

        match stmt {
            Stmt::Let {
                pattern,
                initializer,
                span,
                ..
            } => {
                // Lower initializer if present
                if let Some(init_expr) = initializer {
                    let init_local = self.lower_expr(body, *init_expr);

                    // Bind to pattern - for now just handle simple binding patterns
                    let pat = &body.patterns[*pattern];
                    match pat {
                        rv_hir::Pattern::Binding { name, .. } => {
                            // Create a new local for this binding with the initializer's type
                            let init_ty = self.builder.locals().iter()
                                .find(|l| l.id == init_local)
                                .map(|l| l.ty.clone())
                                .expect("Failed to find type for initializer local. This indicates a bug in MIR lowering.");
                            let binding_local = self.builder.new_local(Some(*name), init_ty, false);

                            // Assign the initializer value to the binding
                            self.builder.add_statement(Statement::Assign {
                                place: Place::from_local(binding_local),
                                rvalue: RValue::Use(Operand::Copy(Place::from_local(init_local))),
                                span: *span,
                            });

                            // Store mapping from variable name to local
                            self.var_locals.insert(*name, binding_local);
                        }
                        _ => {
                            // For other patterns, just lower the initializer
                            // More complex pattern matching not yet implemented
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
            TyKind::Int => MirType::Int,
            TyKind::Float => MirType::Float,
            TyKind::Bool => MirType::Bool,
            TyKind::String => MirType::String,
            TyKind::Unit => MirType::Unit,
            TyKind::Function { params, ret } => MirType::Function {
                // Nested TyIds are also normalized, so we can wrap them
                params: params.iter().map(|p| self.lower_type(NormalizedTy::wrap_child(*p))).collect(),
                ret: Box::new(self.lower_type(NormalizedTy::wrap_child(**ret))),
            },
            TyKind::Tuple { elements } => {
                MirType::Tuple(elements.iter().map(|e| self.lower_type(NormalizedTy::wrap_child(*e))).collect())
            }
            TyKind::Ref { mutable, inner } => MirType::Ref {
                mutable: *mutable,
                inner: Box::new(self.lower_type(NormalizedTy::wrap_child(**inner))),
            },
            TyKind::Struct { def_id, fields } => {
                // Look up the struct name from the definition
                let struct_def = self.structs
                    .get(def_id)
                    .unwrap_or_else(|| {
                        panic!(
                            "COMPILER BUG: Struct type references unknown TypeDefId {:?}. \
                             Name resolution should have linked all struct types to their definitions.",
                            def_id
                        )
                    });

                MirType::Struct {
                    name: struct_def.name,
                    fields: fields.iter().map(|(_, ty_id)| self.lower_type(NormalizedTy::wrap_child(*ty_id))).collect(),
                }
            },
            TyKind::Enum { def_id, variants } => {
                let mir_variants = variants
                    .iter()
                    .map(|(name, variant_ty)| {
                        let fields = match variant_ty {
                            VariantTy::Unit => vec![],
                            VariantTy::Tuple(types) => {
                                types.iter().map(|t| self.lower_type(NormalizedTy::wrap_child(*t))).collect()
                            }
                            VariantTy::Struct(fields) => {
                                fields.iter().map(|(_, ty)| self.lower_type(NormalizedTy::wrap_child(*ty))).collect()
                            }
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
                            "COMPILER BUG: Enum type references unknown TypeDefId {:?}. \
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
            TyKind::Named { name, def, .. } => {
                // Try to resolve the named type to its actual definition
                // Check if it's a struct
                if let Some(struct_def) = self.structs.get(def) {
                    // Create full struct type with fields by converting HIR types to MIR types
                    let field_types: Vec<MirType> = struct_def.fields
                        .iter()
                        .map(|field| {
                            let hir_ty = &self.hir_types[field.ty];
                            self.lower_hir_type_recursive(hir_ty)
                        })
                        .collect();

                    MirType::Struct {
                        name: *name,
                        fields: field_types,
                    }
                } else if let Some(enum_def) = self.enums.get(def) {
                    // Create full enum type with variants
                    let mir_variants: Vec<MirVariant> = enum_def.variants
                        .iter()
                        .map(|variant| {
                            MirVariant {
                                name: variant.name,
                                fields: vec![], // Simplified for now
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
            TyKind::Never => {
                // Never type - map to unit for now
                MirType::Unit
            }
            TyKind::Param { name, .. } => {
                // Generic type parameter - keep as named type
                // During monomorphization, this will be substituted with concrete types
                MirType::Named(*name)
            }
            TyKind::Var { id } => {
                // ⚠️ COMPILE ERROR: If you hit this, it means a non-normalized type was passed!
                // NormalizedTy should make this unreachable.
                panic!(
                    "BUG: Unresolved type variable ?{} in supposedly normalized type {:?}. \
                     This indicates normalize() didn't work correctly or a non-normalized TyId \
                     was unsafely wrapped in NormalizedTy.",
                    id.0, ty.ty_id()
                )
            }
        }
    }

    /// Helper function to recursively convert HIR Type to MirType
    /// This is used when we need to convert struct field types from HIR to MIR
    fn lower_hir_type_recursive(&self, hir_ty: &Type) -> MirType {
        match hir_ty {
            Type::Named { name, def: Some(def_id), .. } => {
                // User-defined type - look up the struct/enum definition
                if let Some(struct_def) = self.structs.get(def_id) {
                    let field_types: Vec<MirType> = struct_def.fields
                        .iter()
                        .map(|field| {
                            let field_hir_ty = &self.hir_types[field.ty];
                            self.lower_hir_type_recursive(field_hir_ty)
                        })
                        .collect();

                    MirType::Struct {
                        name: *name,
                        fields: field_types,
                    }
                } else if let Some(enum_def) = self.enums.get(def_id) {
                    let mir_variants: Vec<MirVariant> = enum_def.variants
                        .iter()
                        .map(|variant| {
                            MirVariant {
                                name: variant.name,
                                fields: vec![],
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
            Type::Named { name, .. } => {
                // def is None - try to look up by name
                // First check if it's a struct or enum by name
                let name_lookup = self.structs.iter()
                    .find(|(_, s)| s.name == *name)
                    .map(|(id, _)| *id)
                    .or_else(|| {
                        self.enums.iter()
                            .find(|(_, e)| e.name == *name)
                            .map(|(id, _)| *id)
                    });

                if let Some(def_id) = name_lookup {
                    // Found a struct or enum - recursively convert it
                    if let Some(struct_def) = self.structs.get(&def_id) {
                        let field_types: Vec<MirType> = struct_def.fields
                            .iter()
                            .map(|field| {
                                let field_hir_ty = &self.hir_types[field.ty];
                                self.lower_hir_type_recursive(field_hir_ty)
                            })
                            .collect();

                        return MirType::Struct {
                            name: *name,
                            fields: field_types,
                        };
                    } else if let Some(enum_def) = self.enums.get(&def_id) {
                        let mir_variants: Vec<MirVariant> = enum_def.variants
                            .iter()
                            .map(|variant| {
                                MirVariant {
                                    name: variant.name,
                                    fields: vec![],
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
                    "i64" | "i32" | "isize" => MirType::Int,
                    "f64" | "f32" => MirType::Float,
                    "bool" => MirType::Bool,
                    "String" | "str" => MirType::String,
                    _ => MirType::Named(*name),
                }
            }
            Type::Generic { name, .. } => MirType::Named(*name),
            Type::Function { params, ret, .. } => {
                let param_types: Vec<MirType> = params
                    .iter()
                    .map(|p| {
                        let param_ty = &self.hir_types[*p];
                        self.lower_hir_type_recursive(param_ty)
                    })
                    .collect();
                let ret_ty = &self.hir_types[**ret];
                MirType::Function {
                    params: param_types,
                    ret: Box::new(self.lower_hir_type_recursive(ret_ty)),
                }
            }
            Type::Tuple { elements, .. } => {
                let element_types: Vec<MirType> = elements
                    .iter()
                    .map(|e| {
                        let elem_ty = &self.hir_types[*e];
                        self.lower_hir_type_recursive(elem_ty)
                    })
                    .collect();
                MirType::Tuple(element_types)
            }
            Type::Reference { inner, mutable, .. } => {
                let inner_ty = &self.hir_types[**inner];
                MirType::Ref {
                    mutable: *mutable,
                    inner: Box::new(self.lower_hir_type_recursive(inner_ty)),
                }
            }
            Type::QualifiedPath { base, assoc_type, .. } => {
                // ARCHITECTURE: Resolve associated types by looking up trait impl blocks
                // Example: Self::Item where Self is a type implementing Container trait

                // Step 1: Get the base type
                let base_hir_ty = &self.hir_types[**base];

                // Step 2: Extract TypeDefId from base type
                let base_type_def_id = match base_hir_ty {
                    Type::Named { def: Some(def_id), .. } => Some(*def_id),
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
                            Type::Named { def: Some(impl_def_id), .. } => {
                                *impl_def_id == def_id
                            }
                            _ => false,
                        };

                        if matches_type && impl_block.trait_ref.is_some() {
                            // This is a trait impl for our type
                            // Look for the associated type implementation
                            for assoc_impl in &impl_block.associated_type_impls {
                                if assoc_impl.name == *assoc_type {
                                    // Found it! Convert the concrete type to MirType
                                    let concrete_ty = &self.hir_types[assoc_impl.ty];
                                    return self.lower_hir_type_recursive(concrete_ty);
                                }
                            }
                        }
                    }
                }

                // Fallback: If we can't resolve the associated type, panic
                // (per user directive: we should panic on type inference errors)
                let assoc_name = self.interner.resolve(assoc_type);
                panic!(
                    "COMPILER BUG: Could not resolve associated type '{}'. \
                     The trait implementation should have provided this type.",
                    assoc_name
                );
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

    /// Resolve a field name to its index in a struct
    fn resolve_field_index(&self, ty_id: TyId, field_name: Symbol) -> Option<usize> {
        let ty = self.ty_ctx.types.get(ty_id);

        // Follow type variable substitutions
        let concrete_ty = match &ty.kind {
            TyKind::Var { id: var_id } => {
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
                    TyKind::Var { id: var_id } => {
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

    /// Resolve a method call to a function ID with mutability checking
    fn resolve_method(
        &self,
        receiver_ty: Option<TyId>,
        method_name: Symbol,
        receiver_is_mut: bool,
    ) -> Result<FunctionId, MethodResolutionError> {
        // First, resolve the receiver type (follow type variables and auto-deref)
        let resolved_ty = receiver_ty.map(|ty_id| {
            let ty = self.ty_ctx.types.get(ty_id);

            // Follow type variable substitutions
            let concrete_ty = match &ty.kind {
                TyKind::Var { id: var_id} => {
                    if let Some(&subst_ty_id) = self.ty_ctx.subst.get(var_id) {
                        self.ty_ctx.types.get(subst_ty_id)
                    } else {
                        ty
                    }
                }
                _ => ty,
            };

            // Handle references - auto-deref to find the underlying type
            match &concrete_ty.kind {
                TyKind::Ref { inner, .. } => {
                    let inner_ty_id = **inner;
                    let inner_ty = self.ty_ctx.types.get(inner_ty_id);
                    // Follow substitutions on the inner type too
                    match &inner_ty.kind {
                        TyKind::Var { id: var_id } => {
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
            }
        });

        // Get the type definition ID from the resolved type
        let type_def_id = resolved_ty.and_then(|inner_ty| {
            match &inner_ty.kind {
                TyKind::Struct { def_id, .. } => Some(*def_id),
                TyKind::Enum { def_id, .. } => Some(*def_id),
                TyKind::Named { name, .. } => {
                    // Try to find in structs first
                    self.structs
                        .iter()
                        .find(|(_, s)| s.name == *name)
                        .map(|(def_id, _)| *def_id)
                        .or_else(|| {
                            // Also try enums
                            self.enums
                                .iter()
                                .find(|(_, e)| e.name == *name)
                                .map(|(def_id, _)| *def_id)
                        })
                }
                _ => None,
            }
        });

        // Search all impl blocks for one that matches this type
        for (_impl_id, impl_block) in self.impl_blocks.iter() {
            let hir_ty = &self.hir_types[impl_block.self_ty];

            let impl_type_matches = if let Some(type_def_id) = type_def_id {
                match hir_ty {
                    Type::Named { def: Some(def_id), .. } => def_id == &type_def_id,
                    _ => false,
                }
            } else if let Some(resolved) = resolved_ty {
                // Handle primitive types - match by comparing HIR type names
                let matches = match &resolved.kind {
                    TyKind::Int => matches!(hir_ty, Type::Named { name, .. } if self.interner.resolve(name) == "i64"),
                    TyKind::Bool => matches!(hir_ty, Type::Named { name, .. } if self.interner.resolve(name) == "bool"),
                    TyKind::String => matches!(hir_ty, Type::Named { name, .. } if self.interner.resolve(name) == "String"),
                    TyKind::Float => matches!(hir_ty, Type::Named { name, .. } if self.interner.resolve(name) == "f64"),
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
                        if let Some(trait_method) = trait_def.methods.iter().find(|m| m.name == method_name) {
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
                        } else {
                        }
                    }
                }

                // Also check inherent methods (impl Type { ... })
                for &func_id in &impl_block.methods {
                    if let Some(func) = self.functions.get(&func_id) {
                        if func.name == method_name {
                            // Check self parameter mutability for inherent methods
                            if !func.parameters.is_empty() {
                                // The first parameter should be self
                                // We need to infer self type from the method's implementation
                                // For now, we assume methods with &mut self require mutable receivers
                                // This is a simplified check; a full implementation would need to parse
                                // the self parameter type from HIR
                                //
                                // Since we don't store SelfParam in Function, we'll be conservative:
                                // If receiver is immutable but function name suggests mutation, warn.
                                // For production, we should add SelfParam to Function HIR.
                                return Ok(func_id);
                            }
                            return Ok(func_id);
                        }
                    }
                }
            }
        }

        Err(MethodResolutionError::MethodNotFound)
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
        LiteralKind::Integer(val) => Some(*val as u128),
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
        | Expr::EnumVariant { span, .. }
        | Expr::Closure { span, .. } => *span,
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
        | Pattern::Range { span, .. } => *span,
    }
}

impl<'ctx> LoweringContext<'ctx> {
    /// Lower pattern bindings by copying the scrutinee value to bound variables
    fn lower_pattern_bindings(
        &mut self,
        pattern: &Pattern,
        scrutinee_local: LocalId,
        body: &Body,
    ) {
        match pattern {
            Pattern::Binding { name, sub_pattern, .. } => {
                // Create a new MIR local for this binding
                let mir_local = self.builder.new_local(Some(*name), MirType::Unit, false);

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
                    let field_local = self.builder.new_local(None, MirType::Unit, false);

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
                if let Type::Named { def: Some(def_id), .. } = &self.hir_types[*ty] {
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
                                let field_local = self.builder.new_local(None, MirType::Unit, false);

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
            Pattern::Range { .. } | Pattern::Literal { .. } | Pattern::Wildcard { .. } | Pattern::Enum { .. } => {
                // No bindings to handle
            }
        }
    }
}
