//! HIR → MIR lowering

use crate::{
    AggregateKind, BinaryOp, Constant, LocalId, MirBuilder, MirFunction, MirType, Operand, Place,
    PlaceElem, RValue, Statement, Terminator, UnaryOp,
};
use lasso::Key;
use rustc_hash::FxHashMap;
use rv_arena::Arena;
use rv_hir::{Body, DefId, Expr, ExprId, Function, FunctionId, ImplBlock, ImplId, LiteralKind, Pattern, Stmt, StmtId, StructDef, TraitDef, TraitId, Type, TypeDefId};
use rv_intern::Symbol;
use rv_span::{FileId, FileSpan, Span};
use rv_ty::{TyContext, TyId, TyKind};
use std::collections::HashMap;

/// Context for lowering HIR to MIR
pub struct LoweringContext<'ctx> {
    /// MIR builder
    builder: MirBuilder,
    /// Type context
    ty_ctx: &'ctx TyContext,
    /// Map from HIR ExprId to MIR LocalId
    expr_locals: FxHashMap<ExprId, LocalId>,
    /// Return local (for storing return value)
    return_local: Option<LocalId>,
    /// Struct definitions from HIR (for field name resolution)
    structs: &'ctx HashMap<TypeDefId, StructDef>,
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
}

impl<'ctx> LoweringContext<'ctx> {
    /// Create a new lowering context
    pub fn new(
        builder: MirBuilder,
        ty_ctx: &'ctx TyContext,
        structs: &'ctx HashMap<TypeDefId, StructDef>,
        impl_blocks: &'ctx HashMap<ImplId, ImplBlock>,
        functions: &'ctx HashMap<FunctionId, Function>,
        hir_types: &'ctx Arena<Type>,
        traits: &'ctx HashMap<TraitId, TraitDef>,
    ) -> Self {
        Self {
            builder,
            ty_ctx,
            expr_locals: FxHashMap::default(),
            return_local: None,
            structs,
            impl_blocks,
            functions,
            hir_types,
            traits,
            var_locals: FxHashMap::default(),
        }
    }

    /// Lower a HIR function to MIR
    pub fn lower_function(
        function: &Function,
        ty_ctx: &'ctx TyContext,
        structs: &'ctx HashMap<TypeDefId, StructDef>,
        impl_blocks: &'ctx HashMap<ImplId, ImplBlock>,
        functions: &'ctx HashMap<FunctionId, Function>,
        hir_types: &'ctx Arena<Type>,
        traits: &'ctx HashMap<TraitId, TraitDef>,
    ) -> MirFunction {
        let builder = MirBuilder::new(function.id);
        let mut ctx = Self::new(builder, ty_ctx, structs, impl_blocks, functions, hir_types, traits);

        // Register function parameters FIRST so they get LocalId(0), LocalId(1), etc.
        // This matches the interpreter's expectation for parameter locals
        for param in &function.parameters {
            // Look up the parameter type from type inference var_types
            // Apply substitutions to resolve type variables
            let param_ty = if let Some(&ty_id) = ty_ctx.var_types.get(&param.name) {
                let resolved_ty_id = ty_ctx.apply_subst(ty_id);
                ctx.lower_type(resolved_ty_id)
            } else {
                // Fallback to Unit if type inference didn't track this parameter
                MirType::Unit
            };

            let param_local = ctx.builder.new_local(Some(param.name), param_ty, false);
            ctx.var_locals.insert(param.name, param_local);
        }

        // Create return local AFTER parameters
        let return_ty = if let Some(ty_id) = ty_ctx.get_expr_type(function.body.root_expr) {
            ctx.lower_type(ty_id)
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
        let mir_ty = if let Some(ty_id) = self.ty_ctx.get_expr_type(expr_id) {
            self.lower_type(ty_id)
        } else {
            MirType::Unknown
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
                        Pattern::Binding { .. } | Pattern::Wildcard { .. } => {
                            // Binding/wildcard patterns match everything
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

                // Get the type of the base expression
                let base_ty = self.ty_ctx.get_expr_type(*base);

                // Resolve field name to index
                let field_idx = if let Some(ty_id) = base_ty {
                    self.resolve_field_index(ty_id, *field).unwrap_or(0)
                } else {
                    0 // Fallback
                };

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
                variant: _,
                def: _,
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

                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Aggregate {
                        kind: AggregateKind::Enum {
                            variant_idx: 0, // TODO: Resolve variant name to index
                        },
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

                // Resolve method name to function ID
                let receiver_ty = self.ty_ctx.get_expr_type(*receiver);

                if let Some(func_id) = self.resolve_method(receiver_ty, *method) {
                    // Emit a function call with the resolved method
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(result_local),
                        rvalue: RValue::Call {
                            func: func_id,
                            args: arg_operands,
                        },
                        span: *span,
                    });
                } else {
                    // Method not found, return Unit
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

            _ => {
                // For unsupported expressions, create unit
                let constant = Constant {
                    kind: LiteralKind::Unit,
                    ty: MirType::Unit,
                };
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(result_local),
                    rvalue: RValue::Use(Operand::Constant(constant)),
                    span: get_expr_span(expr),
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
                            // Create a new local for this binding
                            // TODO: Determine proper type from type inference
                            let binding_local = self.builder.new_local(Some(*name), MirType::Unit, false);

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
    fn lower_type(&self, ty_id: TyId) -> MirType {
        use crate::MirVariant;
        use rv_ty::VariantTy;

        // Apply substitutions first to resolve type variables
        let resolved_ty_id = self.ty_ctx.apply_subst(ty_id);
        let ty = self.ty_ctx.types.get(resolved_ty_id);

        match &ty.kind {
            TyKind::Int => MirType::Int,
            TyKind::Float => MirType::Float,
            TyKind::Bool => MirType::Bool,
            TyKind::String => MirType::String,
            TyKind::Unit => MirType::Unit,
            TyKind::Function { params, ret } => MirType::Function {
                params: params.iter().map(|p| self.lower_type(*p)).collect(),
                ret: Box::new(self.lower_type(**ret)),
            },
            TyKind::Tuple { elements } => {
                MirType::Tuple(elements.iter().map(|e| self.lower_type(*e)).collect())
            }
            TyKind::Ref { mutable, inner } => MirType::Ref {
                mutable: *mutable,
                inner: Box::new(self.lower_type(**inner)),
            },
            TyKind::Struct { fields, .. } => MirType::Struct {
                name: Key::try_from_usize(0).unwrap(), // TODO: Get actual name
                fields: fields.iter().map(|(_, ty)| self.lower_type(*ty)).collect(),
            },
            TyKind::Enum { variants, .. } => {
                let mir_variants = variants
                    .iter()
                    .map(|(name, variant_ty)| {
                        let fields = match variant_ty {
                            VariantTy::Unit => vec![],
                            VariantTy::Tuple(types) => {
                                types.iter().map(|t| self.lower_type(*t)).collect()
                            }
                            VariantTy::Struct(fields) => {
                                fields.iter().map(|(_, ty)| self.lower_type(*ty)).collect()
                            }
                        };
                        MirVariant {
                            name: *name,
                            fields,
                        }
                    })
                    .collect();
                MirType::Enum {
                    name: Key::try_from_usize(0).unwrap(), // TODO: Get actual name
                    variants: mir_variants,
                }
            }
            TyKind::Array { element, size } => MirType::Array {
                element: Box::new(self.lower_type(**element)),
                size: *size,
            },
            TyKind::Slice { element } => MirType::Slice {
                element: Box::new(self.lower_type(**element)),
            },
            TyKind::Named { name, .. } => MirType::Named(*name),
            _ => MirType::Unknown,
        }
    }

    /// Resolve a field name to its index in a struct
    fn resolve_field_index(&self, ty_id: TyId, field_name: Symbol) -> Option<usize> {
        let ty = self.ty_ctx.types.get(ty_id);
        match &ty.kind {
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

    /// Resolve a method call to a function ID
    fn resolve_method(&self, receiver_ty: Option<TyId>, method_name: Symbol) -> Option<FunctionId> {
        // Get the type definition ID from the receiver type
        let type_def_id = receiver_ty.and_then(|ty_id| {
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

            match &concrete_ty.kind {
                TyKind::Struct { def_id, .. } => Some(*def_id),
                TyKind::Named { name, .. } => {
                    self.structs
                        .iter()
                        .find(|(_, s)| s.name == *name)
                        .map(|(def_id, _)| *def_id)
                }
                _ => None,
            }
        })?;

        // Search all impl blocks for one that matches this type
        for impl_block in self.impl_blocks.values() {
            let hir_ty = &self.hir_types[impl_block.self_ty];

            let impl_type_matches = match hir_ty {
                Type::Named { def: Some(def_id), .. } => def_id == &type_def_id,
                _ => false,
            };

            if impl_type_matches {
                // If this impl block implements a trait, check trait methods
                if let Some(trait_id) = impl_block.trait_ref {
                    if let Some(trait_def) = self.traits.get(&trait_id) {
                        // Check if the method is a trait method
                        if trait_def.methods.iter().any(|m| m.name == method_name) {
                            // Found a trait method, look it up in the impl block
                            for &func_id in &impl_block.methods {
                                if let Some(func) = self.functions.get(&func_id) {
                                    if func.name == method_name {
                                        return Some(func_id);
                                    }
                                }
                            }
                        }
                    }
                }

                // Also check inherent methods (impl Type { ... })
                for &func_id in &impl_block.methods {
                    if let Some(func) = self.functions.get(&func_id) {
                        if func.name == method_name {
                            return Some(func_id);
                        }
                    }
                }
            }
        }

        None
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
        | Expr::EnumVariant { span, .. } => *span,
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
            Pattern::Binding { name, .. } => {
                // Create a new MIR local for this binding
                let mir_local = self.builder.new_local(Some(*name), MirType::Unit, false);

                // Copy scrutinee to the bound variable
                self.builder.add_statement(Statement::Assign {
                    place: Place::from_local(mir_local),
                    rvalue: RValue::Use(Operand::Copy(Place::from_local(scrutinee_local))),
                    span: FileSpan::new(FileId(0), Span::new(0, 0)), // TODO: use actual span
                });

                // Store mapping for variable resolution
                self.var_locals.insert(*name, mir_local);
            }
            Pattern::Tuple { patterns, .. } => {
                // For tuple patterns, we need to extract each field and bind recursively
                for (idx, pat_id) in patterns.iter().enumerate() {
                    // Create a local to hold the extracted field
                    let field_local = self.builder.new_local(None, MirType::Unit, false);

                    // Extract the field using Place projection
                    let field_place = Place {
                        local: scrutinee_local,
                        projection: vec![PlaceElem::Field { field_idx: idx }],
                    };

                    // Copy the field to the local
                    self.builder.add_statement(Statement::Assign {
                        place: Place::from_local(field_local),
                        rvalue: RValue::Use(Operand::Copy(field_place)),
                        span: FileSpan::new(FileId(0), Span::new(0, 0)),
                    });

                    // Recursively bind sub-pattern with the extracted field
                    let sub_pattern = &body.patterns[*pat_id];
                    self.lower_pattern_bindings(sub_pattern, field_local, body);
                }
            }
            Pattern::Struct { fields, ty, .. } => {
                // For struct patterns, we need to extract each field and bind recursively
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

                                // Copy the field to the local
                                self.builder.add_statement(Statement::Assign {
                                    place: Place::from_local(field_local),
                                    rvalue: RValue::Use(Operand::Copy(field_place)),
                                    span: FileSpan::new(FileId(0), Span::new(0, 0)),
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
