//! MIR interpreter

#![allow(
    clippy::min_ident_chars,
    reason = "Short identifiers like op, i, l, r, f, b are conventional in operator implementations"
)]

use crate::value::Value;
use rv_mir::{
    AggregateKind, BinaryOp, Constant, LocalId, MirFunction, MirType, Operand, Place, PlaceElem, RValue,
    Statement, Terminator, UnaryOp,
};
use rv_hir::{FunctionId, LiteralKind};
use rv_hir_lower::LoweringContext as HirContext;
use rv_ty::TyContext;
use rustc_hash::FxHashMap;
use std::collections::HashMap;
use thiserror::Error;

/// Interpreter error
#[derive(Debug, Error)]
pub enum InterpreterError {
    /// Undefined local variable
    #[error("undefined local variable: {0:?}")]
    UndefinedLocal(LocalId),
    /// Type mismatch
    #[error("type mismatch: expected {expected}, got {got}")]
    TypeMismatch {
        /// Expected type
        expected: String,
        /// Got type
        got: String,
    },
    /// Division by zero
    #[error("division by zero")]
    DivisionByZero,
    /// Invalid operation
    #[error("invalid operation: {0}")]
    InvalidOperation(String),
    /// Unreachable code
    #[error("reached unreachable code")]
    Unreachable,
}

/// Interpreter state
pub struct Interpreter<'ctx> {
    /// Local variable values
    locals: FxHashMap<LocalId, Value>,
    /// HIR context for function lookup
    hir_ctx: Option<&'ctx HirContext>,
    /// Type context for type inference
    ty_ctx: Option<&'ctx TyContext>,
    /// Cache of monomorphized MIR functions
    mono_cache: HashMap<(FunctionId, Vec<MirType>), MirFunction>,
}

impl<'ctx> Interpreter<'ctx> {
    /// Create a new interpreter
    #[must_use]
    pub fn new() -> Self {
        Self {
            locals: FxHashMap::default(),
            hir_ctx: None,
            ty_ctx: None,
            mono_cache: HashMap::new(),
        }
    }

    /// Create a new interpreter with HIR and type context
    #[must_use]
    pub fn new_with_context(hir_ctx: &'ctx HirContext, ty_ctx: &'ctx TyContext) -> Self {
        Self {
            locals: FxHashMap::default(),
            hir_ctx: Some(hir_ctx),
            ty_ctx: Some(ty_ctx),
            mono_cache: HashMap::new(),
        }
    }

    /// Execute a MIR function and return the result
    ///
    /// # Errors
    /// Returns `InterpreterError` if execution fails
    pub fn execute(&mut self, function: &MirFunction) -> Result<Value, InterpreterError> {
        // Initialize all locals to Unit (but don't overwrite existing parameter values)
        for local in &function.locals {
            self.locals.entry(local.id).or_insert(Value::Unit);
        }

        // Start at entry block
        let mut current_block = function.entry_block;

        // Execute blocks until we hit a return
        loop {
            let block = &function.basic_blocks[current_block];

            // Execute all statements in the block
            for stmt in &block.statements {
                self.execute_statement(stmt)?;
            }

            // Execute terminator
            match &block.terminator {
                Terminator::Goto(target) => {
                    current_block = *target;
                }
                Terminator::SwitchInt {
                    discriminant,
                    targets,
                    otherwise,
                } => {
                    let value = self.eval_operand(discriminant)?;

                    // Convert value to discriminant (integers or booleans)
                    let discriminant_value: u128 = match value {
                        Value::Int(i) => i as u128,
                        Value::Bool(true) => 1,
                        Value::Bool(false) => 0,
                        _ => {
                            return Err(InterpreterError::TypeMismatch {
                                expected: "int or bool".to_string(),
                                got: format!("{value:?}"),
                            })
                        }
                    };

                    // Find matching target
                    let target = targets
                        .iter()
                        .find(|(val, _)| **val == discriminant_value)
                        .map_or(*otherwise, |(_, target_block)| *target_block);

                    current_block = target;
                }
                Terminator::Return { value } => {
                    return value
                        .as_ref()
                        .map_or(Ok(Value::Unit), |operand| self.eval_operand(operand));
                }
                Terminator::Call { .. } => {
                    return Err(InterpreterError::InvalidOperation(
                        "function calls not yet implemented".to_string(),
                    ));
                }
                Terminator::Unreachable => {
                    return Err(InterpreterError::Unreachable);
                }
            }
        }
    }

    /// Execute a statement
    ///
    /// # Errors
    /// Returns `InterpreterError` if execution fails
    fn execute_statement(&mut self, stmt: &Statement) -> Result<(), InterpreterError> {
        match stmt {
            Statement::Assign {
                place, rvalue, ..
            } => {
                let value = self.eval_rvalue(rvalue)?;
                self.write_place(place, value)?;
            }
            Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop => {
                // No-op for interpreter
            }
        }
        Ok(())
    }

    /// Evaluate an rvalue
    ///
    /// # Errors
    /// Returns `InterpreterError` if evaluation fails
    fn eval_rvalue(&mut self, rvalue: &RValue) -> Result<Value, InterpreterError> {
        match rvalue {
            RValue::Use(operand) => self.eval_operand(operand),
            RValue::BinaryOp { op, left, right } => {
                let left_val = self.eval_operand(left)?;
                let right_val = self.eval_operand(right)?;
                Self::eval_binary_op(*op, left_val, right_val)
            }
            RValue::UnaryOp { op, operand } => {
                let val = self.eval_operand(operand)?;
                Self::eval_unary_op(*op, val)
            }
            RValue::Call { func, args, .. } => {
                // Evaluate arguments
                let arg_values: Result<Vec<Value>, InterpreterError> =
                    args.iter().map(|arg| self.eval_operand(arg)).collect();
                let arg_values = arg_values?;

                // Call the function
                self.call_function(*func, arg_values)
            }
            RValue::Ref { place, .. } => {
                // For the interpreter, references are just values
                // We don't track memory addresses, so &x just evaluates to x's value
                self.read_place(place)
            }
            RValue::Aggregate { kind, operands } => {
                let field_values: Result<Vec<Value>, InterpreterError> =
                    operands.iter().map(|op| self.eval_operand(op)).collect();
                let field_values = field_values?;

                match kind {
                    AggregateKind::Tuple => Ok(Value::Tuple(field_values)),
                    AggregateKind::Struct => {
                        // TODO: Get actual struct name from type information
                        use lasso::Key;
                        Ok(Value::Struct {
                            name: Key::try_from_usize(0).unwrap(),
                            fields: field_values,
                        })
                    }
                    AggregateKind::Enum { variant_idx } => {
                        // TODO: Get actual enum name from type information
                        use lasso::Key;
                        Ok(Value::Enum {
                            name: Key::try_from_usize(0).unwrap(),
                            variant_idx: *variant_idx,
                            fields: field_values,
                        })
                    }
                    AggregateKind::Array(_) => Ok(Value::Array(field_values)),
                }
            }
        }
    }

    /// Evaluate an operand
    ///
    /// # Errors
    /// Returns `InterpreterError` if evaluation fails
    fn eval_operand(&self, operand: &Operand) -> Result<Value, InterpreterError> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.read_place(place),
            Operand::Constant(constant) => Ok(Self::eval_constant(constant)),
        }
    }

    /// Evaluate a constant
    #[must_use]
    fn eval_constant(constant: &Constant) -> Value {
        match &constant.kind {
            LiteralKind::Integer(i) => Value::Int(*i),
            LiteralKind::Float(f) => Value::Float(*f),
            LiteralKind::Bool(b) => Value::Bool(*b),
            LiteralKind::String(s) => Value::String(s.clone()),
            LiteralKind::Unit => Value::Unit,
        }
    }

    /// Read from a place
    ///
    /// # Errors
    /// Returns `InterpreterError` if place is undefined
    fn read_place(&self, place: &Place) -> Result<Value, InterpreterError> {
        let mut value = self
            .locals
            .get(&place.local)
            .cloned()
            .ok_or(InterpreterError::UndefinedLocal(place.local))?;

        // Apply projections
        for projection in &place.projection {
            value = match projection {
                PlaceElem::Deref => {
                    return Err(InterpreterError::InvalidOperation(
                        "deref not yet implemented".to_string(),
                    ))
                }
                PlaceElem::Field { field_idx } => match value {
                    Value::Struct { fields, .. } => fields
                        .get(*field_idx)
                        .cloned()
                        .ok_or_else(|| {
                            InterpreterError::InvalidOperation(format!(
                                "field index {} out of bounds",
                                field_idx
                            ))
                        })?,
                    Value::Tuple(fields) => fields.get(*field_idx).cloned().ok_or_else(|| {
                        InterpreterError::InvalidOperation(format!(
                            "field index {} out of bounds",
                            field_idx
                        ))
                    })?,
                    Value::Enum { fields, .. } => fields
                        .get(*field_idx)
                        .cloned()
                        .ok_or_else(|| {
                            InterpreterError::InvalidOperation(format!(
                                "field index {} out of bounds",
                                field_idx
                            ))
                        })?,
                    _ => {
                        panic!("FIELD PROJECTION TYPE MISMATCH: got {:?}", value);
                    }
                },
                PlaceElem::Index(_) => {
                    return Err(InterpreterError::InvalidOperation(
                        "index not yet implemented".to_string(),
                    ))
                }
            };
        }

        Ok(value)
    }

    /// Write to a place
    ///
    /// # Errors
    /// Returns `InterpreterError` if place is invalid
    fn write_place(&mut self, place: &Place, value: Value) -> Result<(), InterpreterError> {
        if !place.projection.is_empty() {
            return Err(InterpreterError::InvalidOperation(
                "projections not yet implemented".to_string(),
            ));
        }

        self.locals.insert(place.local, value);
        Ok(())
    }

    /// Evaluate a binary operation
    ///
    /// # Errors
    /// Returns `InterpreterError` if operation fails
    #[allow(
        clippy::too_many_lines,
        reason = "Comprehensive binary operation handling requires many match arms"
    )]
    fn eval_binary_op(
        op: BinaryOp,
        left: Value,
        right: Value,
    ) -> Result<Value, InterpreterError> {
        match (op, left, right) {
            // Integer operations
            (BinaryOp::Add, Value::Int(l), Value::Int(r)) => Ok(Value::Int(l + r)),
            (BinaryOp::Sub, Value::Int(l), Value::Int(r)) => Ok(Value::Int(l - r)),
            (BinaryOp::Mul, Value::Int(l), Value::Int(r)) => Ok(Value::Int(l * r)),
            (BinaryOp::Div | BinaryOp::Mod, Value::Int(_), Value::Int(0)) => {
                Err(InterpreterError::DivisionByZero)
            }
            (BinaryOp::Div, Value::Int(l), Value::Int(r)) => Ok(Value::Int(l / r)),
            (BinaryOp::Mod, Value::Int(l), Value::Int(r)) => Ok(Value::Int(l % r)),

            // Float operations
            (BinaryOp::Add, Value::Float(l), Value::Float(r)) => Ok(Value::Float(l + r)),
            (BinaryOp::Sub, Value::Float(l), Value::Float(r)) => Ok(Value::Float(l - r)),
            (BinaryOp::Mul, Value::Float(l), Value::Float(r)) => Ok(Value::Float(l * r)),
            (BinaryOp::Div, Value::Float(l), Value::Float(r)) => Ok(Value::Float(l / r)),
            (BinaryOp::Mod, Value::Float(l), Value::Float(r)) => Ok(Value::Float(l % r)),

            // Integer comparisons
            (BinaryOp::Eq, Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l == r)),
            (BinaryOp::Ne, Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l != r)),
            (BinaryOp::Lt, Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l < r)),
            (BinaryOp::Le, Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l <= r)),
            (BinaryOp::Gt, Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l > r)),
            (BinaryOp::Ge, Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l >= r)),

            // Float comparisons
            #[allow(clippy::float_cmp, reason = "Direct float comparison is intentional for interpreter semantics")]
            (BinaryOp::Eq, Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l == r)),
            #[allow(clippy::float_cmp, reason = "Direct float comparison is intentional for interpreter semantics")]
            (BinaryOp::Ne, Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l != r)),
            (BinaryOp::Lt, Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l < r)),
            (BinaryOp::Le, Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l <= r)),
            (BinaryOp::Gt, Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l > r)),
            (BinaryOp::Ge, Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l >= r)),

            // Boolean operations
            (BinaryOp::Eq, Value::Bool(l), Value::Bool(r)) => Ok(Value::Bool(l == r)),
            (BinaryOp::Ne, Value::Bool(l), Value::Bool(r)) => Ok(Value::Bool(l != r)),
            (BinaryOp::BitAnd, Value::Bool(l), Value::Bool(r)) => Ok(Value::Bool(l & r)),
            (BinaryOp::BitOr, Value::Bool(l), Value::Bool(r)) => Ok(Value::Bool(l | r)),
            (BinaryOp::BitXor, Value::Bool(l), Value::Bool(r)) => Ok(Value::Bool(l ^ r)),

            // Integer bitwise operations
            (BinaryOp::BitAnd, Value::Int(l), Value::Int(r)) => Ok(Value::Int(l & r)),
            (BinaryOp::BitOr, Value::Int(l), Value::Int(r)) => Ok(Value::Int(l | r)),
            (BinaryOp::BitXor, Value::Int(l), Value::Int(r)) => Ok(Value::Int(l ^ r)),
            (BinaryOp::Shl, Value::Int(l), Value::Int(r)) => Ok(Value::Int(l << r)),
            (BinaryOp::Shr, Value::Int(l), Value::Int(r)) => Ok(Value::Int(l >> r)),

            // Type mismatch
            (_op, left, right) => Err(InterpreterError::TypeMismatch {
                expected: format!("{left:?}"),
                got: format!("{right:?}"),
            }),
        }
    }

    /// Evaluate a unary operation
    ///
    /// # Errors
    /// Returns `InterpreterError` if operation fails
    fn eval_unary_op(op: UnaryOp, value: Value) -> Result<Value, InterpreterError> {
        match (op, value) {
            (UnaryOp::Neg, Value::Int(i)) => Ok(Value::Int(-i)),
            (UnaryOp::Neg, Value::Float(f)) => Ok(Value::Float(-f)),
            (UnaryOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
            (UnaryOp::Not, Value::Int(i)) => Ok(Value::Int(!i)),
            (_, val) => {
                panic!("UNARY OP TYPE MISMATCH: got {:?}", val);
            }
        }
    }

    /// Call a function with given arguments
    ///
    /// # Errors
    /// Returns `InterpreterError` if function call fails
    fn call_function(
        &mut self,
        func_id: FunctionId,
        args: Vec<Value>,
    ) -> Result<Value, InterpreterError> {
        // Get HIR context
        let hir_ctx = self.hir_ctx.ok_or_else(|| {
            InterpreterError::InvalidOperation("No HIR context available for function calls".to_string())
        })?;

        // Look up the function in HIR
        let hir_func = hir_ctx.functions.get(&func_id).ok_or_else(|| {
            InterpreterError::InvalidOperation(format!("Function {:?} not found", func_id))
        })?;

        // For now, infer types from argument values (simple monomorphization)
        // In a full implementation, we'd use type inference results
        let type_args: Vec<MirType> = args.iter().map(|val| match val {
            Value::Int(_) => MirType::Int,
            Value::Float(_) => MirType::Float,
            Value::Bool(_) => MirType::Bool,
            _ => MirType::Unit,
        }).collect();

        // Check if we have a cached monomorphized version
        let cache_key = (func_id, type_args.clone());
        if !self.mono_cache.contains_key(&cache_key) {
            // Lower HIR function to MIR with type substitution
            let ty_ctx = self.ty_ctx.ok_or_else(|| {
                InterpreterError::InvalidOperation("No type context available".to_string())
            })?;

            // Clone context for MIR lowering
            let mut ty_ctx_clone = ty_ctx.clone();

            // ARCHITECTURE: Populate def_types with concrete type substitutions
            // for generic function parameters BEFORE running type inference
            if !hir_func.generics.is_empty() {
                // For each parameter, create TyId and store by DefId::Local
                for (param_idx, _param) in hir_func.parameters.iter().enumerate() {
                    // Get the corresponding type argument
                    let mir_ty = type_args.get(param_idx).unwrap_or_else(|| {
                        panic!(
                            "COMPILER BUG: Generic function called with insufficient type arguments. \
                             Expected at least {} type arguments for parameter {}, got {}.",
                            param_idx + 1, param_idx, type_args.len()
                        )
                    });

                    // Create TyId for this concrete type
                    let concrete_ty_id = match mir_ty {
                        MirType::Int => ty_ctx_clone.types.alloc(rv_ty::TyKind::Int),
                        MirType::Float => ty_ctx_clone.types.alloc(rv_ty::TyKind::Float),
                        MirType::Bool => ty_ctx_clone.types.alloc(rv_ty::TyKind::Bool),
                        MirType::Unit => ty_ctx_clone.types.alloc(rv_ty::TyKind::Unit),
                        other => {
                            panic!(
                                "COMPILER BUG: Unsupported MIR type {:?} in generic instantiation. \
                                 All MIR types should have corresponding TyKind mappings.",
                                other
                            )
                        }
                    };

                    // ARCHITECTURE: Store by DefId (not Symbol name)
                    let local_id = rv_hir::LocalId(param_idx as u32);
                    let def_id = rv_hir::DefId::Local {
                        func: func_id,
                        local: local_id,
                    };
                    ty_ctx_clone.set_def_type(def_id, concrete_ty_id);
                }
            }

            // ARCHITECTURE FIX: Must run type inference before MIR lowering
            // This matches the pattern used in rv-mono/src/lib.rs
            use rv_ty::TypeInference;
            let mut type_inference = TypeInference::with_hir_context_and_tyctx(
                &hir_ctx.impl_blocks,
                &hir_ctx.functions,
                &hir_ctx.types,
                &hir_ctx.structs,
                &hir_ctx.enums,
                &hir_ctx.traits,
                &hir_ctx.interner,
                ty_ctx_clone,
            );
            type_inference.infer_function(hir_func);
            let inference_result = type_inference.finish();
            let mut ty_ctx_with_inference = inference_result.ctx;

            // Now lower with inferred types
            let mir_func = rv_mir_lower::LoweringContext::lower_function(
                hir_func,
                &mut ty_ctx_with_inference,
                &hir_ctx.structs,
                &hir_ctx.enums,
                &hir_ctx.impl_blocks,
                &hir_ctx.functions,
                &hir_ctx.types,
                &hir_ctx.traits,
                &hir_ctx.interner,
            );

            self.mono_cache.insert(cache_key.clone(), mir_func);
        }

        // Get the monomorphized function (clone to avoid borrow issues)
        let mir_func = self.mono_cache[&cache_key].clone();

        // Save current locals state
        let saved_locals = self.locals.clone();

        // Initialize function parameters with argument values
        for (param_idx, arg_value) in args.iter().enumerate() {
            // Parameter locals start at index 0
            let param_local = LocalId(param_idx as u32);
            self.locals.insert(param_local, arg_value.clone());
        }

        // Execute the function
        let result = self.execute(&mir_func);

        // Restore previous locals
        self.locals = saved_locals;

        result
    }
}

impl<'ctx> Default for Interpreter<'ctx> {
    fn default() -> Self {
        Self::new()
    }
}
