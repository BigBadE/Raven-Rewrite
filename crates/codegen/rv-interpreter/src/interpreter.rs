//! MIR interpreter

#![allow(
    clippy::min_ident_chars,
    reason = "Short identifiers like op, i, l, r, f, b are conventional in operator implementations"
)]

use crate::value::Value;
use rustc_hash::FxHashMap;
use rv_hir::{FunctionId, LiteralKind};
use rv_hir_lower::LoweringContext as HirContext;
use rv_mir::{
    AggregateKind, AssertMessage, BinaryOp, Constant, LocalId, MirFunction, MirType, Operand,
    Place, PlaceElem, RValue, Statement, Terminator, UnaryOp,
};
use rv_ty::TyContext;
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
    /// Assertion failed
    #[error("assertion failed: {0}")]
    AssertionFailed(String),
}

/// Convert a MIR type to a TyId for the type inference engine.
///
/// Handles primitive types directly and creates fresh type variables for
/// compound types whose full structure will be resolved by type inference.
fn convert_mir_type_to_ty_id(mir_ty: &MirType, ty_ctx: &mut TyContext) -> rv_ty::TyId {
    match mir_ty {
        MirType::Int(w, s) => ty_ctx.types.int_typed(*w, *s),
        MirType::Float(w) => ty_ctx.types.float_typed(*w),
        MirType::Char => ty_ctx.types.char(),
        MirType::Bool => ty_ctx.types.bool(),
        MirType::Unit => ty_ctx.types.unit(),
        MirType::String => ty_ctx.types.string(),
        MirType::Ref {
            inner,
            mutable,
            lifetime,
        } => {
            let inner_ty = convert_mir_type_to_ty_id(inner, ty_ctx);
            ty_ctx.types.alloc(rv_ty::TyKind::Ref {
                inner: Box::new(inner_ty),
                mutable: *mutable,
                lifetime: *lifetime,
            })
        }
        MirType::Tuple(elements) => {
            let elem_tys: Vec<rv_ty::TyId> = elements
                .iter()
                .map(|e| convert_mir_type_to_ty_id(e, ty_ctx))
                .collect();
            ty_ctx
                .types
                .alloc(rv_ty::TyKind::Tuple { elements: elem_tys })
        }
        MirType::Array { element, size } => {
            let elem_ty = convert_mir_type_to_ty_id(element, ty_ctx);
            ty_ctx.types.alloc(rv_ty::TyKind::Array {
                element: Box::new(elem_ty),
                size: *size,
            })
        }
        // For Struct/Enum/other compound types, create a fresh type variable.
        // The caller is responsible for constructing full TyKind::Struct with
        // TypeDefId and field names when HIR context is available.
        _ => ty_ctx.fresh_ty_var(),
    }
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
    /// Pre-registered MIR functions (e.g., from cross-module compilation)
    registered_functions: HashMap<FunctionId, MirFunction>,
    /// Simulated heap memory for raw pointer support
    memory: HashMap<usize, Value>,
    /// Next available address for memory allocation
    next_addr: usize,
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
            registered_functions: HashMap::new(),
            memory: HashMap::new(),
            next_addr: 0x1000,
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
            registered_functions: HashMap::new(),
            memory: HashMap::new(),
            next_addr: 0x1000,
        }
    }

    /// Allocate a value in simulated memory, returning its address
    fn alloc_memory(&mut self, value: Value) -> usize {
        let addr = self.next_addr;
        self.next_addr += 8; // Align to 8 bytes
        self.memory.insert(addr, value);
        addr
    }

    /// Register a pre-lowered MIR function for execution.
    ///
    /// This is used for cross-module compilation where functions from other modules
    /// have already been lowered to MIR and don't need on-demand lowering from HIR.
    pub fn register_mir_function(&mut self, func_id: FunctionId, mir_func: MirFunction) {
        self.registered_functions.insert(func_id, mir_func);
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
                    ..
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
                            });
                        }
                    };

                    // Find matching target
                    let target = targets
                        .iter()
                        .find(|(val, _)| **val == discriminant_value)
                        .map_or(*otherwise, |(_, target_block)| *target_block);

                    current_block = target;
                }
                Terminator::Return { value, .. } => {
                    return value
                        .as_ref()
                        .map_or(Ok(Value::Unit), |operand| self.eval_operand(operand));
                }
                Terminator::Call {
                    func,
                    args,
                    destination,
                    target,
                    ..
                } => {
                    let arg_values: Result<Vec<Value>, InterpreterError> =
                        args.iter().map(|arg| self.eval_operand(arg)).collect();
                    let arg_values = arg_values?;

                    let result = self.call_function(*func, arg_values)?;
                    self.write_place(destination, result)?;
                    current_block = *target;
                }
                Terminator::Drop { place, target, .. } => {
                    // Check if the type being dropped is a Box
                    // If so, deallocate the memory (remove from heap)
                    if let Some(local_ty) = function.get_local_type(place.local) {
                        if matches!(local_ty, MirType::Box { .. }) {
                            // Read the box pointer value
                            if let Ok(Value::Pointer(addr)) = self.read_place(place) {
                                // Deallocate the memory
                                self.memory.remove(&addr);
                            }
                        }
                    }
                    // TODO(tier4): Call Drop::drop if the type implements Drop trait.
                    // For now, just continue to the target block — the value is
                    // considered consumed and its storage will be reclaimed.
                    current_block = *target;
                }
                Terminator::Unreachable => {
                    return Err(InterpreterError::Unreachable);
                }
                Terminator::Assert {
                    cond,
                    expected,
                    msg,
                    target,
                    ..
                } => {
                    let cond_val = self.eval_operand(cond)?;
                    let cond_bool = match cond_val {
                        Value::Bool(b) => b,
                        Value::Int(i) => i != 0,
                        _ => {
                            return Err(InterpreterError::TypeMismatch {
                                expected: "bool".to_string(),
                                got: format!("{cond_val:?}"),
                            });
                        }
                    };

                    // If condition matches expected, continue; otherwise panic
                    if cond_bool == *expected {
                        current_block = *target;
                    } else {
                        // Assertion failed
                        let error_msg = match msg {
                            AssertMessage::BoundsCheck { index, len } => {
                                let idx = self.eval_operand(index)?;
                                let length = self.eval_operand(len)?;
                                format!(
                                    "index out of bounds: the len is {:?} but the index is {:?}",
                                    length, idx
                                )
                            }
                            AssertMessage::Overflow(op) => {
                                format!("attempt to {:?} with overflow", op)
                            }
                            AssertMessage::DivisionByZero => {
                                "attempt to divide by zero".to_string()
                            }
                            AssertMessage::RemainderByZero => {
                                "attempt to calculate the remainder with a divisor of zero"
                                    .to_string()
                            }
                            AssertMessage::Panic(s) => s.clone(),
                        };
                        return Err(InterpreterError::AssertionFailed(error_msg));
                    }
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
            Statement::Assign { place, rvalue, .. } => {
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
            RValue::Call { func, args } => {
                // Evaluate arguments
                let arg_values: Result<Vec<Value>, InterpreterError> =
                    args.iter().map(|arg| self.eval_operand(arg)).collect();
                let arg_values = arg_values?;

                // Call the function
                self.call_function(*func, arg_values)
            }
            RValue::Intrinsic { intrinsic, args, type_args } => {
                // Evaluate arguments
                let arg_values: Result<Vec<Value>, InterpreterError> =
                    args.iter().map(|arg| self.eval_operand(arg)).collect();
                let arg_values = arg_values?;

                // Execute the intrinsic with type arguments
                self.eval_intrinsic(intrinsic, arg_values, type_args)
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
                    AggregateKind::Struct { name } => Ok(Value::Struct {
                        name: *name,
                        fields: field_values,
                    }),
                    AggregateKind::Enum { name, variant_idx } => Ok(Value::Enum {
                        name: *name,
                        variant_idx: *variant_idx,
                        fields: field_values,
                    }),
                    AggregateKind::Array(_) => Ok(Value::Array(field_values)),
                }
            }
            RValue::Discriminant(place) => {
                let value = self.read_place(place)?;
                match value {
                    Value::Enum { variant_idx, .. } => Ok(Value::Int(variant_idx as i64)),
                    _ => Err(InterpreterError::InvalidOperation(format!(
                        "cannot extract discriminant from non-enum value: {value:?}"
                    ))),
                }
            }
            RValue::VtableCall {
                method_name,
                trait_id,
                receiver,
                args,
                ..
            } => {
                // Dynamic dispatch: look up the concrete method for the receiver's type
                // For the interpreter, we resolve by finding the trait impl and calling by name
                let receiver_val = self.eval_operand(receiver)?;
                let mut call_args = vec![receiver_val];
                for arg in args {
                    call_args.push(self.eval_operand(arg)?);
                }

                // Find the concrete function by looking through registered MIR functions
                // that have the matching method name
                if let Some(hir_ctx) = self.hir_ctx {
                    // Search all impl blocks for one that implements this trait
                    for impl_block in hir_ctx.impl_blocks.values() {
                        if impl_block.trait_ref != Some(*trait_id) || impl_block.is_blanket {
                            continue;
                        }
                        for &func_id in &impl_block.methods {
                            if let Some(func) = hir_ctx.functions.get(&func_id) {
                                if func.name == *method_name {
                                    return self.call_function(func_id, call_args);
                                }
                            }
                        }
                    }
                }

                Err(InterpreterError::InvalidOperation(format!(
                    "vtable call: could not resolve method '{:?}' for trait {:?}",
                    method_name, trait_id
                )))
            }
            RValue::Cast { operand, to, .. } => {
                let value = self.eval_operand(operand)?;
                match (&value, to) {
                    // Int → Float
                    (Value::Int(n), MirType::Float(..)) => Ok(Value::Float(*n as f64)),
                    // Float → Int (truncate)
                    (Value::Float(f), MirType::Int(..)) => Ok(Value::Int(*f as i64)),
                    // Bool → Int
                    (Value::Bool(b), MirType::Int(..)) => Ok(Value::Int(if *b { 1 } else { 0 })),
                    // Int → Bool (0 = false, nonzero = true)
                    (Value::Int(n), MirType::Bool) => Ok(Value::Bool(*n != 0)),
                    // Int → Pointer (integer-to-pointer cast)
                    (Value::Int(n), MirType::Pointer { .. }) => Ok(Value::Pointer(*n as usize)),
                    // Pointer → Int (pointer-to-integer cast)
                    (Value::Pointer(addr), MirType::Int(..)) => Ok(Value::Int(*addr as i64)),
                    // Pointer → Pointer (pointer-to-pointer cast, identity)
                    (Value::Pointer(_), MirType::Pointer { .. }) => Ok(value),
                    // Ref/Value → Pointer (e.g., &x as *const T)
                    // Allocate the value in simulated memory and return a pointer
                    (_, MirType::Pointer { .. }) => {
                        let addr = self.alloc_memory(value);
                        Ok(Value::Pointer(addr))
                    }
                    // Same type or unsupported: pass through
                    _ => Ok(value),
                }
            }
            RValue::BoxNew { operand, .. } => {
                // Box allocation: allocate the value in memory and return pointer
                let value = self.eval_operand(operand)?;
                let addr = self.alloc_memory(value);
                Ok(Value::Pointer(addr))
            }
            RValue::BoxFree { .. } => {
                // Box deallocation: no-op in interpreter (no actual memory management)
                Ok(Value::Unit)
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
            LiteralKind::Integer(i, _) => Value::Int(*i),
            LiteralKind::Float(f, _) => Value::Float(*f),
            LiteralKind::Char(c) => Value::Int(*c as i64),
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
                PlaceElem::Deref => match value {
                    Value::Pointer(addr) => self.memory.get(&addr).cloned().ok_or_else(|| {
                        InterpreterError::InvalidOperation(format!(
                            "dangling pointer dereference at address 0x{addr:x}"
                        ))
                    })?,
                    // For references, Deref is a no-op (references are values)
                    _ => value,
                },
                PlaceElem::Field { field_idx } => match value {
                    Value::Struct { fields, .. } => {
                        fields.get(*field_idx).cloned().ok_or_else(|| {
                            InterpreterError::InvalidOperation(format!(
                                "field index {} out of bounds",
                                field_idx
                            ))
                        })?
                    }
                    Value::Tuple(fields) => fields.get(*field_idx).cloned().ok_or_else(|| {
                        InterpreterError::InvalidOperation(format!(
                            "field index {} out of bounds",
                            field_idx
                        ))
                    })?,
                    Value::Enum { fields, .. } => {
                        fields.get(*field_idx).cloned().ok_or_else(|| {
                            InterpreterError::InvalidOperation(format!(
                                "field index {} out of bounds",
                                field_idx
                            ))
                        })?
                    }
                    _ => {
                        return Err(InterpreterError::TypeMismatch {
                            expected: "struct or enum for field projection".to_string(),
                            got: format!("{:?}", value),
                        });
                    }
                },
                PlaceElem::Index(index_local) => {
                    let index_value = self
                        .locals
                        .get(index_local)
                        .ok_or(InterpreterError::UndefinedLocal(*index_local))?;
                    let index = match index_value {
                        Value::Int(i) => *i as usize,
                        _ => {
                            return Err(InterpreterError::TypeMismatch {
                                expected: "integer index".to_string(),
                                got: format!("{index_value:?}"),
                            });
                        }
                    };
                    match value {
                        Value::Array(elements) => {
                            elements.get(index).cloned().ok_or_else(|| {
                                InterpreterError::InvalidOperation(format!(
                                    "array index {} out of bounds (len {})",
                                    index,
                                    elements.len()
                                ))
                            })?
                        }
                        _ => {
                            return Err(InterpreterError::InvalidOperation(format!(
                                "cannot index into {:?}",
                                value
                            )));
                        }
                    }
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
        if place.projection.is_empty() {
            self.locals.insert(place.local, value);
            return Ok(());
        }

        // Check for pointer write: [Deref, ...] on a Pointer value
        // writes into simulated memory instead of modifying the local
        if let Some(PlaceElem::Deref) = place.projection.first() {
            let base = self
                .locals
                .get(&place.local)
                .cloned()
                .ok_or(InterpreterError::UndefinedLocal(place.local))?;
            if let Value::Pointer(addr) = base {
                if place.projection.len() == 1 {
                    // Simple *ptr = value
                    self.memory.insert(addr, value);
                    return Ok(());
                }
                // *ptr.field = value — read from memory, modify, write back
                let mut mem_val = self.memory.get(&addr).cloned().ok_or_else(|| {
                    InterpreterError::InvalidOperation(format!(
                        "dangling pointer write at address 0x{addr:x}"
                    ))
                })?;
                Self::write_into_value(&mut mem_val, &place.projection[1..], value, &self.locals)?;
                self.memory.insert(addr, mem_val);
                return Ok(());
            }
        }

        // For projected writes, we need to read the base, modify it, and write it back.
        let mut base = self
            .locals
            .get(&place.local)
            .cloned()
            .ok_or(InterpreterError::UndefinedLocal(place.local))?;

        // Navigate to the parent of the final projection, then write the value
        // into that final projection target.
        Self::write_into_value(&mut base, &place.projection, value, &self.locals)?;

        self.locals.insert(place.local, base);
        Ok(())
    }

    /// Recursively navigate projections and write a value into the target location.
    fn write_into_value(
        target: &mut Value,
        projections: &[PlaceElem],
        value: Value,
        locals: &FxHashMap<LocalId, Value>,
    ) -> Result<(), InterpreterError> {
        match projections {
            [] => {
                *target = value;
                Ok(())
            }
            [PlaceElem::Deref, rest @ ..] => {
                // In the interpreter, references are values, so Deref is a no-op
                Self::write_into_value(target, rest, value, locals)
            }
            [PlaceElem::Field { field_idx }, rest @ ..] => {
                let fields = match target {
                    Value::Struct { fields, .. } => fields,
                    Value::Tuple(fields) => fields,
                    Value::Enum { fields, .. } => fields,
                    _ => {
                        return Err(InterpreterError::InvalidOperation(format!(
                            "cannot write field {} of {:?}",
                            field_idx, target
                        )));
                    }
                };
                if *field_idx >= fields.len() {
                    return Err(InterpreterError::InvalidOperation(format!(
                        "field index {} out of bounds (len {})",
                        field_idx,
                        fields.len()
                    )));
                }
                let field = &mut fields[*field_idx];
                Self::write_into_value(field, rest, value, locals)
            }
            [PlaceElem::Index(index_local), rest @ ..] => {
                let index = match locals.get(index_local) {
                    Some(Value::Int(i)) => *i as usize,
                    Some(other) => {
                        return Err(InterpreterError::TypeMismatch {
                            expected: "integer index".to_string(),
                            got: format!("{other:?}"),
                        });
                    }
                    None => return Err(InterpreterError::UndefinedLocal(*index_local)),
                };
                let elements = match target {
                    Value::Array(elements) => elements,
                    _ => {
                        return Err(InterpreterError::InvalidOperation(format!(
                            "cannot index into {:?}",
                            target
                        )));
                    }
                };
                if index >= elements.len() {
                    return Err(InterpreterError::InvalidOperation(format!(
                        "array index {} out of bounds (len {})",
                        index,
                        elements.len()
                    )));
                }
                let element = &mut elements[index];
                Self::write_into_value(element, rest, value, locals)
            }
        }
    }

    /// Evaluate a binary operation
    ///
    /// # Errors
    /// Returns `InterpreterError` if operation fails
    #[allow(
        clippy::too_many_lines,
        reason = "Comprehensive binary operation handling requires many match arms"
    )]
    fn eval_binary_op(op: BinaryOp, left: Value, right: Value) -> Result<Value, InterpreterError> {
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
            #[allow(
                clippy::float_cmp,
                reason = "Direct float comparison is intentional for interpreter semantics"
            )]
            (BinaryOp::Eq, Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l == r)),
            #[allow(
                clippy::float_cmp,
                reason = "Direct float comparison is intentional for interpreter semantics"
            )]
            (BinaryOp::Ne, Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l != r)),
            (BinaryOp::Lt, Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l < r)),
            (BinaryOp::Le, Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l <= r)),
            (BinaryOp::Gt, Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l > r)),
            (BinaryOp::Ge, Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l >= r)),

            // Boolean operations
            (BinaryOp::Eq, Value::Bool(l), Value::Bool(r)) => Ok(Value::Bool(l == r)),
            (BinaryOp::Ne, Value::Bool(l), Value::Bool(r)) => Ok(Value::Bool(l != r)),
            (BinaryOp::BitAnd | BinaryOp::And, Value::Bool(l), Value::Bool(r)) => {
                Ok(Value::Bool(l & r))
            }
            (BinaryOp::BitOr | BinaryOp::Or, Value::Bool(l), Value::Bool(r)) => {
                Ok(Value::Bool(l | r))
            }
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
            (_, val) => Err(InterpreterError::TypeMismatch {
                expected: format!("compatible type for unary op {:?}", op),
                got: format!("{:?}", val),
            }),
        }
    }

    /// Evaluate a compiler intrinsic
    ///
    /// # Errors
    /// Returns `InterpreterError` if intrinsic evaluation fails
    fn eval_intrinsic(
        &mut self,
        intrinsic: &rv_mir::Intrinsic,
        args: Vec<Value>,
        type_args: &[MirType],
    ) -> Result<Value, InterpreterError> {
        // Resolve intrinsic name from symbol
        let hir_ctx = self.hir_ctx.ok_or_else(|| {
            InterpreterError::InvalidOperation("No HIR context for intrinsic lookup".to_string())
        })?;
        let intrinsic_name = hir_ctx.interner.resolve(&intrinsic.name);

        match intrinsic_name.as_str() {
            // Memory intrinsics
            "size_of" => {
                let ty = type_args.first().ok_or_else(|| {
                    InterpreterError::InvalidOperation(
                        "size_of requires a type argument".to_string(),
                    )
                })?;
                let size = Self::calculate_size_of(ty);
                Ok(Value::Int(size as i64))
            }
            "align_of" => {
                let ty = type_args.first().ok_or_else(|| {
                    InterpreterError::InvalidOperation(
                        "align_of requires a type argument".to_string(),
                    )
                })?;
                let align = Self::calculate_align_of(ty);
                Ok(Value::Int(align as i64))
            }
            "size_of_val" => {
                // For now, use the type of the first argument
                // In a full implementation, this would handle DSTs
                let ty = type_args.first().ok_or_else(|| {
                    InterpreterError::InvalidOperation(
                        "size_of_val requires a type argument".to_string(),
                    )
                })?;
                let size = Self::calculate_size_of(ty);
                Ok(Value::Int(size as i64))
            }
            "align_of_val" => {
                let ty = type_args.first().ok_or_else(|| {
                    InterpreterError::InvalidOperation(
                        "align_of_val requires a type argument".to_string(),
                    )
                })?;
                let align = Self::calculate_align_of(ty);
                Ok(Value::Int(align as i64))
            }
            "transmute" | "transmute_unchecked" => {
                // Transmute reinterprets bits - for interpreter, just pass through
                // Real transmute would need to handle bit representations
                args.into_iter().next().ok_or_else(|| {
                    InterpreterError::InvalidOperation(
                        "transmute requires an argument".to_string(),
                    )
                })
            }
            "forget" => {
                // forget() is a no-op - just don't run the destructor
                Ok(Value::Unit)
            }
            "needs_drop" => {
                // For interpreter, conservatively say yes for structs/enums
                let ty = type_args.first().ok_or_else(|| {
                    InterpreterError::InvalidOperation(
                        "needs_drop requires a type argument".to_string(),
                    )
                })?;
                let needs_drop = Self::type_needs_drop(ty);
                Ok(Value::Bool(needs_drop))
            }
            "copy" | "copy_nonoverlapping" => {
                // Memory copy operations - in interpreter these are handled via Place operations
                // For now, return unit since actual memory handling is abstracted
                Ok(Value::Unit)
            }
            "write_bytes" => {
                // Memory write - abstracted in interpreter
                Ok(Value::Unit)
            }

            // Arithmetic intrinsics
            "add_with_overflow" => {
                let (a, b) = Self::get_two_int_args(&args)?;
                let (result, overflow) = a.overflowing_add(b);
                Ok(Value::Tuple(vec![Value::Int(result), Value::Bool(overflow)]))
            }
            "sub_with_overflow" => {
                let (a, b) = Self::get_two_int_args(&args)?;
                let (result, overflow) = a.overflowing_sub(b);
                Ok(Value::Tuple(vec![Value::Int(result), Value::Bool(overflow)]))
            }
            "mul_with_overflow" => {
                let (a, b) = Self::get_two_int_args(&args)?;
                let (result, overflow) = a.overflowing_mul(b);
                Ok(Value::Tuple(vec![Value::Int(result), Value::Bool(overflow)]))
            }
            "wrapping_add" => {
                let (a, b) = Self::get_two_int_args(&args)?;
                Ok(Value::Int(a.wrapping_add(b)))
            }
            "wrapping_sub" => {
                let (a, b) = Self::get_two_int_args(&args)?;
                Ok(Value::Int(a.wrapping_sub(b)))
            }
            "wrapping_mul" => {
                let (a, b) = Self::get_two_int_args(&args)?;
                Ok(Value::Int(a.wrapping_mul(b)))
            }
            "saturating_add" => {
                let (a, b) = Self::get_two_int_args(&args)?;
                Ok(Value::Int(a.saturating_add(b)))
            }
            "saturating_sub" => {
                let (a, b) = Self::get_two_int_args(&args)?;
                Ok(Value::Int(a.saturating_sub(b)))
            }
            "unchecked_add" => {
                let (a, b) = Self::get_two_int_args(&args)?;
                // UB if overflow, but interpreter just wraps
                Ok(Value::Int(a.wrapping_add(b)))
            }
            "unchecked_sub" => {
                let (a, b) = Self::get_two_int_args(&args)?;
                Ok(Value::Int(a.wrapping_sub(b)))
            }
            "unchecked_mul" => {
                let (a, b) = Self::get_two_int_args(&args)?;
                Ok(Value::Int(a.wrapping_mul(b)))
            }
            "unchecked_div" => {
                let (a, b) = Self::get_two_int_args(&args)?;
                if b == 0 {
                    return Err(InterpreterError::DivisionByZero);
                }
                Ok(Value::Int(a / b))
            }
            "exact_div" => {
                let (a, b) = Self::get_two_int_args(&args)?;
                if b == 0 {
                    return Err(InterpreterError::DivisionByZero);
                }
                Ok(Value::Int(a / b))
            }
            "rotate_left" => {
                let (val, shift) = Self::get_two_int_args(&args)?;
                Ok(Value::Int((val as u64).rotate_left(shift as u32) as i64))
            }
            "rotate_right" => {
                let (val, shift) = Self::get_two_int_args(&args)?;
                Ok(Value::Int((val as u64).rotate_right(shift as u32) as i64))
            }
            "ctlz" => {
                let val = Self::get_one_int_arg(&args)?;
                Ok(Value::Int((val as u64).leading_zeros() as i64))
            }
            "cttz" => {
                let val = Self::get_one_int_arg(&args)?;
                Ok(Value::Int((val as u64).trailing_zeros() as i64))
            }
            "ctpop" => {
                let val = Self::get_one_int_arg(&args)?;
                Ok(Value::Int((val as u64).count_ones() as i64))
            }
            "bitreverse" => {
                let val = Self::get_one_int_arg(&args)?;
                Ok(Value::Int((val as u64).reverse_bits() as i64))
            }
            "bswap" => {
                let val = Self::get_one_int_arg(&args)?;
                Ok(Value::Int((val as u64).swap_bytes() as i64))
            }

            // Float intrinsics
            "sqrtf32" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float((val as f32).sqrt() as f64))
            }
            "sqrtf64" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float(val.sqrt()))
            }
            "sinf32" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float((val as f32).sin() as f64))
            }
            "sinf64" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float(val.sin()))
            }
            "cosf32" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float((val as f32).cos() as f64))
            }
            "cosf64" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float(val.cos()))
            }
            "powf32" => {
                let (base, exp) = Self::get_two_float_args(&args)?;
                Ok(Value::Float((base as f32).powf(exp as f32) as f64))
            }
            "powf64" => {
                let (base, exp) = Self::get_two_float_args(&args)?;
                Ok(Value::Float(base.powf(exp)))
            }
            "expf32" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float((val as f32).exp() as f64))
            }
            "expf64" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float(val.exp()))
            }
            "logf32" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float((val as f32).ln() as f64))
            }
            "logf64" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float(val.ln()))
            }
            "floorf32" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float((val as f32).floor() as f64))
            }
            "floorf64" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float(val.floor()))
            }
            "ceilf32" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float((val as f32).ceil() as f64))
            }
            "ceilf64" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float(val.ceil()))
            }
            "truncf32" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float((val as f32).trunc() as f64))
            }
            "truncf64" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float(val.trunc()))
            }
            "roundf32" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float((val as f32).round() as f64))
            }
            "roundf64" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Float(val.round()))
            }
            "fmaf32" => {
                let (a, b, c) = Self::get_three_float_args(&args)?;
                Ok(Value::Float(
                    (a as f32).mul_add(b as f32, c as f32) as f64,
                ))
            }
            "fmaf64" => {
                let (a, b, c) = Self::get_three_float_args(&args)?;
                Ok(Value::Float(a.mul_add(b, c)))
            }
            "float_to_int_unchecked" => {
                let val = Self::get_one_float_arg(&args)?;
                Ok(Value::Int(val as i64))
            }

            // Control intrinsics
            "unreachable" => Err(InterpreterError::Unreachable),
            "assume" => {
                // assume() hints that condition is true - no-op in interpreter
                Ok(Value::Unit)
            }
            "likely" | "unlikely" => {
                // Branch hints - pass through the boolean
                args.into_iter().next().ok_or_else(|| {
                    InterpreterError::InvalidOperation(
                        "likely/unlikely requires an argument".to_string(),
                    )
                })
            }
            "abort" => {
                Err(InterpreterError::InvalidOperation("abort() called".to_string()))
            }
            "caller_location" => {
                // Return a placeholder location
                // Real implementation would return &'static Location<'static>
                Ok(Value::Tuple(vec![
                    Value::String("unknown".to_string()),
                    Value::Int(0),
                    Value::Int(0),
                ]))
            }
            "type_id" => {
                // Return a hash of the type for type_id
                let ty = type_args.first().ok_or_else(|| {
                    InterpreterError::InvalidOperation(
                        "type_id requires a type argument".to_string(),
                    )
                })?;
                let type_hash = Self::type_hash(ty);
                Ok(Value::Int(type_hash as i64))
            }
            "type_name" => {
                // Return the type name as a string
                let ty = type_args.first().ok_or_else(|| {
                    InterpreterError::InvalidOperation(
                        "type_name requires a type argument".to_string(),
                    )
                })?;
                let name = Self::type_name(ty);
                Ok(Value::String(name))
            }

            // Atomic intrinsics (simplified - no actual atomicity in interpreter)
            "atomic_load" => {
                // Load from pointer
                if let Some(Value::Pointer(addr)) = args.first() {
                    self.memory
                        .get(addr)
                        .cloned()
                        .ok_or_else(|| {
                            InterpreterError::InvalidOperation(format!(
                                "atomic_load: invalid address 0x{:x}",
                                addr
                            ))
                        })
                } else {
                    Err(InterpreterError::InvalidOperation(
                        "atomic_load requires a pointer argument".to_string(),
                    ))
                }
            }
            "atomic_store" => {
                // Store to pointer
                if let (Some(Value::Pointer(addr)), Some(val)) = (args.first(), args.get(1)) {
                    self.memory.insert(*addr, val.clone());
                    Ok(Value::Unit)
                } else {
                    Err(InterpreterError::InvalidOperation(
                        "atomic_store requires pointer and value arguments".to_string(),
                    ))
                }
            }
            "atomic_xchg" => {
                // Exchange: return old value, store new value
                if let (Some(Value::Pointer(addr)), Some(new_val)) = (args.first(), args.get(1)) {
                    let old = self.memory.get(addr).cloned().unwrap_or(Value::Int(0));
                    self.memory.insert(*addr, new_val.clone());
                    Ok(old)
                } else {
                    Err(InterpreterError::InvalidOperation(
                        "atomic_xchg requires pointer and value arguments".to_string(),
                    ))
                }
            }
            "atomic_xadd" => {
                // Fetch-add: return old value, add to memory
                if let (Some(Value::Pointer(addr)), Some(Value::Int(addend))) =
                    (args.first(), args.get(1))
                {
                    let old = match self.memory.get(addr) {
                        Some(Value::Int(v)) => *v,
                        _ => 0,
                    };
                    self.memory.insert(*addr, Value::Int(old + addend));
                    Ok(Value::Int(old))
                } else {
                    Err(InterpreterError::InvalidOperation(
                        "atomic_xadd requires pointer and integer arguments".to_string(),
                    ))
                }
            }
            "atomic_xsub" => {
                // Fetch-sub: return old value, subtract from memory
                if let (Some(Value::Pointer(addr)), Some(Value::Int(subtrahend))) =
                    (args.first(), args.get(1))
                {
                    let old = match self.memory.get(addr) {
                        Some(Value::Int(v)) => *v,
                        _ => 0,
                    };
                    self.memory.insert(*addr, Value::Int(old - subtrahend));
                    Ok(Value::Int(old))
                } else {
                    Err(InterpreterError::InvalidOperation(
                        "atomic_xsub requires pointer and integer arguments".to_string(),
                    ))
                }
            }
            "atomic_cxchg" | "atomic_cxchgweak" => {
                // Compare-exchange: if memory == expected, store desired
                if let (
                    Some(Value::Pointer(addr)),
                    Some(expected),
                    Some(desired),
                ) = (args.first(), args.get(1), args.get(2))
                {
                    let current = self.memory.get(addr).cloned().unwrap_or(Value::Int(0));
                    let success = current == *expected;
                    if success {
                        self.memory.insert(*addr, desired.clone());
                    }
                    Ok(Value::Tuple(vec![current, Value::Bool(success)]))
                } else {
                    Err(InterpreterError::InvalidOperation(
                        "atomic_cxchg requires pointer, expected, and desired arguments"
                            .to_string(),
                    ))
                }
            }
            "atomic_fence" | "atomic_singlethreadfence" => {
                // Memory fences are no-ops in interpreter
                Ok(Value::Unit)
            }

            // Pointer intrinsics
            "offset" | "arith_offset" => {
                // Pointer offset
                if let (Some(Value::Pointer(base)), Some(Value::Int(offset))) =
                    (args.first(), args.get(1))
                {
                    let element_size = type_args
                        .first()
                        .map(|ty| Self::calculate_size_of(ty))
                        .unwrap_or(1);
                    let new_addr = (*base as i64 + offset * element_size as i64) as usize;
                    Ok(Value::Pointer(new_addr))
                } else {
                    Err(InterpreterError::InvalidOperation(
                        "offset requires pointer and integer arguments".to_string(),
                    ))
                }
            }
            "ptr_offset_from" => {
                // Signed pointer difference
                if let (Some(Value::Pointer(a)), Some(Value::Pointer(b))) =
                    (args.first(), args.get(1))
                {
                    let element_size = type_args
                        .first()
                        .map(|ty| Self::calculate_size_of(ty))
                        .unwrap_or(1);
                    let diff = (*a as i64 - *b as i64) / element_size as i64;
                    Ok(Value::Int(diff))
                } else {
                    Err(InterpreterError::InvalidOperation(
                        "ptr_offset_from requires two pointer arguments".to_string(),
                    ))
                }
            }
            "ptr_offset_from_unsigned" => {
                // Unsigned pointer difference
                if let (Some(Value::Pointer(a)), Some(Value::Pointer(b))) =
                    (args.first(), args.get(1))
                {
                    let element_size = type_args
                        .first()
                        .map(|ty| Self::calculate_size_of(ty))
                        .unwrap_or(1);
                    let diff = (a.saturating_sub(*b)) / element_size;
                    Ok(Value::Int(diff as i64))
                } else {
                    Err(InterpreterError::InvalidOperation(
                        "ptr_offset_from_unsigned requires two pointer arguments".to_string(),
                    ))
                }
            }
            "raw_eq" => {
                // Bitwise equality
                if let (Some(a), Some(b)) = (args.first(), args.get(1)) {
                    Ok(Value::Bool(a == b))
                } else {
                    Err(InterpreterError::InvalidOperation(
                        "raw_eq requires two arguments".to_string(),
                    ))
                }
            }
            "compare_bytes" => {
                // memcmp-like comparison - simplified
                Ok(Value::Int(0)) // Placeholder: "equal"
            }
            "volatile_load" => {
                // Same as regular load in interpreter
                if let Some(Value::Pointer(addr)) = args.first() {
                    self.memory.get(addr).cloned().ok_or_else(|| {
                        InterpreterError::InvalidOperation(format!(
                            "volatile_load: invalid address 0x{:x}",
                            addr
                        ))
                    })
                } else {
                    Err(InterpreterError::InvalidOperation(
                        "volatile_load requires a pointer argument".to_string(),
                    ))
                }
            }
            "volatile_store" => {
                // Same as regular store in interpreter
                if let (Some(Value::Pointer(addr)), Some(val)) = (args.first(), args.get(1)) {
                    self.memory.insert(*addr, val.clone());
                    Ok(Value::Unit)
                } else {
                    Err(InterpreterError::InvalidOperation(
                        "volatile_store requires pointer and value arguments".to_string(),
                    ))
                }
            }

            // Unknown intrinsic - return first arg or unit as fallback
            _ => {
                args.into_iter().next().ok_or_else(|| {
                    InterpreterError::InvalidOperation(format!(
                        "Unknown intrinsic with no arguments: {}",
                        intrinsic_name
                    ))
                })
            }
        }
    }

    /// Calculate the size of a MIR type in bytes
    fn calculate_size_of(ty: &MirType) -> usize {
        match ty {
            MirType::Unit => 0,
            MirType::Bool => 1,
            MirType::Char => 4,
            MirType::Int(width, _) => match width {
                rv_hir::IntWidth::I8 => 1,
                rv_hir::IntWidth::I16 => 2,
                rv_hir::IntWidth::I32 => 4,
                rv_hir::IntWidth::I64 => 8,
                rv_hir::IntWidth::I128 => 16,
                rv_hir::IntWidth::Isize => 8, // Assume 64-bit platform
            },
            MirType::Float(width) => match width {
                rv_hir::FloatWidth::F32 => 4,
                rv_hir::FloatWidth::F64 => 8,
            },
            MirType::String => 16, // Fat pointer (ptr + len)
            MirType::Ref { inner, .. } => {
                if inner.is_unsized() {
                    16 // Fat pointer
                } else {
                    8 // Thin pointer
                }
            }
            MirType::Pointer { inner, .. } => {
                if inner.is_unsized() {
                    16
                } else {
                    8
                }
            }
            MirType::Box { inner } => {
                if inner.is_unsized() {
                    16
                } else {
                    8
                }
            }
            MirType::Tuple(elements) => {
                // Sum of aligned elements
                let mut offset = 0;
                for elem in elements {
                    let align = Self::calculate_align_of(elem);
                    offset = (offset + align - 1) & !(align - 1);
                    offset += Self::calculate_size_of(elem);
                }
                // Final alignment to tuple's alignment
                let align = Self::calculate_align_of(ty);
                (offset + align - 1) & !(align - 1)
            }
            MirType::Array { element, size } => Self::calculate_size_of(element) * size,
            MirType::Slice { .. } => 16, // Fat pointer (ptr + len)
            MirType::Struct { fields, .. } => {
                let mut offset = 0;
                for field in fields {
                    let align = Self::calculate_align_of(field);
                    offset = (offset + align - 1) & !(align - 1);
                    offset += Self::calculate_size_of(field);
                }
                let align = Self::calculate_align_of(ty);
                (offset + align - 1) & !(align - 1)
            }
            MirType::Enum { variants, .. } => {
                // Size is discriminant + max variant payload
                let discriminant_size = if variants.len() <= 256 { 1 } else { 4 };
                let max_payload: usize = variants
                    .iter()
                    .map(|v| {
                        v.fields.iter().map(Self::calculate_size_of).sum::<usize>()
                    })
                    .max()
                    .unwrap_or(0);
                let align = Self::calculate_align_of(ty);
                let size = discriminant_size + max_payload;
                (size + align - 1) & !(align - 1)
            }
            MirType::Named(_) | MirType::ImplTrait { .. } => 8, // Conservative default
            MirType::DynTrait { .. } => 16, // Fat pointer
            MirType::Function { .. } | MirType::FunctionPointer { .. } => 8,
            MirType::Never => 0, // ZST
        }
    }

    /// Calculate the alignment of a MIR type in bytes
    fn calculate_align_of(ty: &MirType) -> usize {
        match ty {
            MirType::Unit | MirType::Never => 1,
            MirType::Bool => 1,
            MirType::Char => 4,
            MirType::Int(width, _) => match width {
                rv_hir::IntWidth::I8 => 1,
                rv_hir::IntWidth::I16 => 2,
                rv_hir::IntWidth::I32 => 4,
                rv_hir::IntWidth::I64 => 8,
                rv_hir::IntWidth::I128 => 16,
                rv_hir::IntWidth::Isize => 8,
            },
            MirType::Float(width) => match width {
                rv_hir::FloatWidth::F32 => 4,
                rv_hir::FloatWidth::F64 => 8,
            },
            MirType::String | MirType::Slice { .. } => 8, // Pointer alignment
            MirType::Ref { .. }
            | MirType::Pointer { .. }
            | MirType::Box { .. }
            | MirType::DynTrait { .. } => 8,
            MirType::Tuple(elements) => {
                elements.iter().map(Self::calculate_align_of).max().unwrap_or(1)
            }
            MirType::Array { element, .. } => Self::calculate_align_of(element),
            MirType::Struct { fields, .. } => {
                fields.iter().map(Self::calculate_align_of).max().unwrap_or(1)
            }
            MirType::Enum { variants, .. } => {
                // Max alignment of all variant fields
                variants
                    .iter()
                    .flat_map(|v| v.fields.iter())
                    .map(Self::calculate_align_of)
                    .max()
                    .unwrap_or(1)
                    .max(1) // At least 1 for discriminant
            }
            MirType::Named(_) | MirType::ImplTrait { .. } => 8,
            MirType::Function { .. } | MirType::FunctionPointer { .. } => 8,
        }
    }

    /// Check if a type needs drop (has a destructor)
    fn type_needs_drop(ty: &MirType) -> bool {
        match ty {
            // Primitives and ZSTs don't need drop
            MirType::Unit
            | MirType::Bool
            | MirType::Char
            | MirType::Int(_, _)
            | MirType::Float(_)
            | MirType::Never => false,
            // Pointers don't need drop (they don't own data)
            MirType::Pointer { .. } | MirType::FunctionPointer { .. } | MirType::Function { .. } => {
                false
            }
            // References don't need drop
            MirType::Ref { .. } => false,
            // Box needs drop (heap deallocation)
            MirType::Box { .. } => true,
            // String needs drop
            MirType::String => true,
            // Aggregates need drop if any element needs drop
            MirType::Tuple(elements) => elements.iter().any(Self::type_needs_drop),
            MirType::Array { element, .. } => Self::type_needs_drop(element),
            MirType::Struct { fields, .. } => fields.iter().any(Self::type_needs_drop),
            MirType::Enum { variants, .. } => variants
                .iter()
                .any(|v| v.fields.iter().any(Self::type_needs_drop)),
            // Slices and trait objects: depends on element type
            MirType::Slice { element } => Self::type_needs_drop(element),
            MirType::DynTrait { .. } => true, // Conservative: might have drop
            // Named types: conservatively assume yes
            MirType::Named(_) | MirType::ImplTrait { .. } => true,
        }
    }

    /// Calculate a simple hash for a type (for type_id)
    fn type_hash(ty: &MirType) -> u64 {
        use std::hash::{Hash, Hasher};
        use std::collections::hash_map::DefaultHasher;
        let mut hasher = DefaultHasher::new();
        ty.hash(&mut hasher);
        hasher.finish()
    }

    /// Get the type name as a string (for type_name)
    fn type_name(ty: &MirType) -> String {
        match ty {
            MirType::Unit => "()".to_string(),
            MirType::Bool => "bool".to_string(),
            MirType::Char => "char".to_string(),
            MirType::Int(width, sign) => {
                let prefix = match sign {
                    rv_hir::Signedness::Signed => "i",
                    rv_hir::Signedness::Unsigned => "u",
                };
                let bits = match width {
                    rv_hir::IntWidth::I8 => "8",
                    rv_hir::IntWidth::I16 => "16",
                    rv_hir::IntWidth::I32 => "32",
                    rv_hir::IntWidth::I64 => "64",
                    rv_hir::IntWidth::I128 => "128",
                    rv_hir::IntWidth::Isize => "size",
                };
                format!("{prefix}{bits}")
            }
            MirType::Float(width) => match width {
                rv_hir::FloatWidth::F32 => "f32".to_string(),
                rv_hir::FloatWidth::F64 => "f64".to_string(),
            },
            MirType::String => "str".to_string(),
            MirType::Ref { mutable, inner, .. } => {
                let prefix = if *mutable { "&mut " } else { "&" };
                format!("{}{}", prefix, Self::type_name(inner))
            }
            MirType::Pointer { mutable, inner } => {
                let prefix = if *mutable { "*mut " } else { "*const " };
                format!("{}{}", prefix, Self::type_name(inner))
            }
            MirType::Box { inner } => format!("Box<{}>", Self::type_name(inner)),
            MirType::Tuple(elements) => {
                let inner: Vec<_> = elements.iter().map(Self::type_name).collect();
                format!("({})", inner.join(", "))
            }
            MirType::Array { element, size } => {
                format!("[{}; {}]", Self::type_name(element), size)
            }
            MirType::Slice { element } => format!("[{}]", Self::type_name(element)),
            MirType::Struct { name, .. } => format!("{:?}", name),
            MirType::Enum { name, .. } => format!("{:?}", name),
            MirType::Named(name) => format!("{:?}", name),
            MirType::DynTrait { principal, .. } => format!("dyn {:?}", principal),
            MirType::ImplTrait { principal } => format!("impl {:?}", principal),
            MirType::Function { params, ret } => {
                let params: Vec<_> = params.iter().map(Self::type_name).collect();
                format!("fn({}) -> {}", params.join(", "), Self::type_name(ret))
            }
            MirType::FunctionPointer { params, ret, abi } => {
                let params: Vec<_> = params.iter().map(Self::type_name).collect();
                let abi_str = abi
                    .as_ref()
                    .map(|a| format!("extern \"{}\" ", a))
                    .unwrap_or_default();
                format!("{}fn({}) -> {}", abi_str, params.join(", "), Self::type_name(ret))
            }
            MirType::Never => "!".to_string(),
        }
    }

    /// Helper to extract two integer arguments
    fn get_two_int_args(args: &[Value]) -> Result<(i64, i64), InterpreterError> {
        match (args.first(), args.get(1)) {
            (Some(Value::Int(a)), Some(Value::Int(b))) => Ok((*a, *b)),
            _ => Err(InterpreterError::InvalidOperation(
                "expected two integer arguments".to_string(),
            )),
        }
    }

    /// Helper to extract one integer argument
    fn get_one_int_arg(args: &[Value]) -> Result<i64, InterpreterError> {
        match args.first() {
            Some(Value::Int(v)) => Ok(*v),
            _ => Err(InterpreterError::InvalidOperation(
                "expected an integer argument".to_string(),
            )),
        }
    }

    /// Helper to extract one float argument
    fn get_one_float_arg(args: &[Value]) -> Result<f64, InterpreterError> {
        match args.first() {
            Some(Value::Float(v)) => Ok(*v),
            Some(Value::Int(v)) => Ok(*v as f64), // Allow int → float
            _ => Err(InterpreterError::InvalidOperation(
                "expected a float argument".to_string(),
            )),
        }
    }

    /// Helper to extract two float arguments
    fn get_two_float_args(args: &[Value]) -> Result<(f64, f64), InterpreterError> {
        let a = match args.first() {
            Some(Value::Float(v)) => *v,
            Some(Value::Int(v)) => *v as f64,
            _ => {
                return Err(InterpreterError::InvalidOperation(
                    "expected first float argument".to_string(),
                ))
            }
        };
        let b = match args.get(1) {
            Some(Value::Float(v)) => *v,
            Some(Value::Int(v)) => *v as f64,
            _ => {
                return Err(InterpreterError::InvalidOperation(
                    "expected second float argument".to_string(),
                ))
            }
        };
        Ok((a, b))
    }

    /// Helper to extract three float arguments
    fn get_three_float_args(args: &[Value]) -> Result<(f64, f64, f64), InterpreterError> {
        let a = match args.first() {
            Some(Value::Float(v)) => *v,
            Some(Value::Int(v)) => *v as f64,
            _ => {
                return Err(InterpreterError::InvalidOperation(
                    "expected first float argument".to_string(),
                ))
            }
        };
        let b = match args.get(1) {
            Some(Value::Float(v)) => *v,
            Some(Value::Int(v)) => *v as f64,
            _ => {
                return Err(InterpreterError::InvalidOperation(
                    "expected second float argument".to_string(),
                ))
            }
        };
        let c = match args.get(2) {
            Some(Value::Float(v)) => *v,
            Some(Value::Int(v)) => *v as f64,
            _ => {
                return Err(InterpreterError::InvalidOperation(
                    "expected third float argument".to_string(),
                ))
            }
        };
        Ok((a, b, c))
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
        // Check if this function was pre-registered (e.g., from cross-module compilation)
        if let Some(mir_func) = self.registered_functions.get(&func_id).cloned() {
            // Save current locals state
            let saved_locals = self.locals.clone();

            // Initialize function parameters with argument values
            for (param_idx, arg_value) in args.iter().enumerate() {
                let param_local = LocalId(param_idx as u32);
                self.locals.insert(param_local, arg_value.clone());
            }

            // Execute the pre-registered function
            let result = self.execute(&mir_func);

            // Restore previous locals
            self.locals = saved_locals;

            return result;
        }

        // Get HIR context for on-demand lowering
        let hir_ctx = self.hir_ctx.ok_or_else(|| {
            InterpreterError::InvalidOperation(
                "No HIR context available for function calls".to_string(),
            )
        })?;

        // Look up the function in HIR
        let hir_func = hir_ctx.functions.get(&func_id).ok_or_else(|| {
            InterpreterError::InvalidOperation(format!("Function {:?} not found", func_id))
        })?;

        // Infer MIR types from argument values for monomorphization
        let type_args: Vec<MirType> = args
            .iter()
            .map(|val| Self::value_to_mir_type(val))
            .collect();

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
                            "ICE: Generic function called with insufficient type arguments. \
                             Expected at least {} type arguments for parameter {}, got {}.",
                            param_idx + 1,
                            param_idx,
                            type_args.len()
                        )
                    });

                    // Create TyId for this concrete type
                    let concrete_ty_id = match mir_ty {
                        MirType::Struct { name, fields } => {
                            // Struct needs HIR context for TypeDefId and field names
                            let (def_id, struct_def) = hir_ctx
                                .structs
                                .iter()
                                .find(|(_, s)| s.name == *name)
                                .map(|(id, s)| (*id, s))
                                .unwrap_or_else(|| {
                                    panic!(
                                        "ICE: Struct '{}' not found in HIR context during \
                                         generic instantiation.",
                                        hir_ctx.interner.resolve(name)
                                    )
                                });
                            let ty_fields: Vec<(rv_intern::Symbol, rv_ty::TyId)> = struct_def
                                .fields
                                .iter()
                                .zip(fields.iter())
                                .map(|(hir_field, mir_field_ty)| {
                                    let field_ty =
                                        convert_mir_type_to_ty_id(mir_field_ty, &mut ty_ctx_clone);
                                    (hir_field.name, field_ty)
                                })
                                .collect();
                            ty_ctx_clone.types.alloc(rv_ty::TyKind::Struct {
                                def_id,
                                fields: ty_fields,
                            })
                        }
                        // All other types handled by the shared helper
                        other => convert_mir_type_to_ty_id(other, &mut ty_ctx_clone),
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
                &hir_ctx.interner,
                ty_ctx_clone,
            );
            type_inference.infer_function(hir_func);
            let inference_result = type_inference.finish();
            let mut ty_ctx_with_inference = inference_result.ctx;

            // Evaluate const and static items
            let const_values =
                rv_const_eval::evaluate_const_items(&hir_ctx.const_items, &hir_ctx.interner);
            let static_values = rv_const_eval::evaluate_static_items(
                &hir_ctx.static_items,
                &hir_ctx.const_items,
                &const_values,
                &hir_ctx.interner,
            );

            // Now lower with inferred types
            let mir_result = rv_mir_lower::LoweringContext::lower_function(
                hir_func,
                &mut ty_ctx_with_inference,
                &hir_ctx.structs,
                &hir_ctx.enums,
                &hir_ctx.impl_blocks,
                &hir_ctx.functions,
                &hir_ctx.types,
                &hir_ctx.traits,
                &hir_ctx.interner,
                &hir_ctx.lang_items,
                &const_values,
                &static_values,
            );

            self.mono_cache
                .insert(cache_key.clone(), mir_result.function);
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

    /// Convert a runtime Value to its corresponding MirType
    fn value_to_mir_type(val: &Value) -> MirType {
        match val {
            Value::Int(_) => MirType::Int(rv_hir::IntWidth::I64, rv_hir::Signedness::Signed),
            Value::Float(_) => MirType::Float(rv_hir::FloatWidth::F64),
            Value::Bool(_) => MirType::Bool,
            Value::String(_) => MirType::String,
            Value::Unit => MirType::Unit,
            Value::Tuple(fields) => {
                MirType::Tuple(fields.iter().map(Self::value_to_mir_type).collect())
            }
            Value::Struct { name, fields } => MirType::Struct {
                name: *name,
                fields: fields.iter().map(Self::value_to_mir_type).collect(),
            },
            Value::Enum { name, .. } => MirType::Named(*name),
            Value::Pointer(_) => MirType::Pointer {
                mutable: false,
                inner: Box::new(MirType::Unit),
            },
            Value::Array(elements) => {
                let element_ty = elements
                    .first()
                    .map_or(MirType::Unit, Self::value_to_mir_type);
                MirType::Array {
                    element: Box::new(element_ty),
                    size: elements.len(),
                }
            }
        }
    }
}

impl<'ctx> Default for Interpreter<'ctx> {
    fn default() -> Self {
        Self::new()
    }
}
