//! Bytecode interpreter.
//!
//! A simple register-machine VM over [`rv_codegen::Bytecode`]. Each call gets a
//! frame: a flat vector of [`Value`] register slots. Parameters bind to registers
//! `0..nparams`; everything else starts as `Unit`. We run instructions by program
//! counter within the callee's flat code stream until a `Ret`.
//!
//! Recursion in the interpreter mirrors recursion in the program, so `Call`
//! simply evaluates the callee with a fresh frame and writes the result back.

use rv_codegen::{BinOpKind as BinOp, Bytecode, CompiledFn, Const, Instr, UnOpKind as UnOp};

/// A runtime value.
///
/// `Adt` (an aggregate: a struct or enum variant) holds owned field values, so
/// `Value` can no longer be `Copy`; we `clone` at the few sites that previously
/// relied on copy semantics.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Int(i64),
    Bool(bool),
    Unit,
    /// An algebraic data value. `tag` is the enum variant index (0 for structs);
    /// `fields` are the constructor's arguments in declaration order.
    Adt { tag: u32, fields: Vec<Value> },
    /// A reference: an index into the frame's store (heap of cells). Produced by
    /// `&x` / `&mut x`; followed by `Load`/`Store` to read or mutate the cell. Both
    /// shared and mutable borrows share this representation.
    Ref(usize),
    /// A first-class closure: the lifted function (`fn_idx` into [`Bytecode::funcs`])
    /// together with the values it captured by value. Calling it (`CallClosure`)
    /// runs `fn_idx` with `captured` prepended to the call arguments.
    Closure { fn_idx: usize, captured: Vec<Value> },
}

/// Run function `entry` with `args`, returning its result or a runtime error.
pub fn run(bc: &Bytecode, entry: &str, args: &[Value]) -> Result<Value, String> {
    let idx = bc
        .func_index(entry)
        .ok_or_else(|| format!("no such function: {entry}"))?;
    exec_fn(bc, idx, args)
}

/// Execute one function with the given arguments.
fn exec_fn(bc: &Bytecode, fn_idx: usize, args: &[Value]) -> Result<Value, String> {
    let f: &CompiledFn = &bc.funcs[fn_idx];
    if args.len() != f.nparams {
        return Err(format!(
            "{}: expected {} args, got {}",
            f.name,
            f.nparams,
            args.len()
        ));
    }

    // Frame: one slot per register. Parameters occupy the first slots.
    let mut regs = vec![Value::Unit; f.nregs];
    for (slot, v) in regs.iter_mut().zip(args.iter()) {
        *slot = v.clone();
    }

    // The frame's store ("heap of cells"): addresses produced by `Alloc`/`&x` index
    // here. Each boxed local owns a cell; a `Value::Ref(addr)` points at one. Cells
    // live for the duration of the call, so references cannot dangle within a frame.
    let mut store: Vec<Value> = Vec::new();

    let mut pc = f.entry_off;
    loop {
        let instr = f
            .code
            .get(pc)
            .ok_or_else(|| format!("{}: pc {pc} out of bounds", f.name))?;
        match instr {
            Instr::Const(dst, c) => {
                regs[*dst as usize] = const_to_value(*c);
                pc += 1;
            }
            Instr::Move(dst, src) => {
                regs[*dst as usize] = regs[*src as usize].clone();
                pc += 1;
            }
            Instr::Bin(dst, op, a, b) => {
                let va = regs[*a as usize].clone();
                let vb = regs[*b as usize].clone();
                regs[*dst as usize] = eval_bin(*op, va, vb)?;
                pc += 1;
            }
            Instr::Un(dst, op, src) => {
                let v = regs[*src as usize].clone();
                regs[*dst as usize] = eval_un(*op, v)?;
                pc += 1;
            }
            Instr::Call(dst, callee, arg_regs) => {
                let call_args: Vec<Value> =
                    arg_regs.iter().map(|r| regs[*r as usize].clone()).collect();
                let result = exec_fn(bc, *callee, &call_args)?;
                regs[*dst as usize] = result;
                pc += 1;
            }
            Instr::MakeClosure(dst, fn_idx, capture_regs) => {
                let captured: Vec<Value> =
                    capture_regs.iter().map(|r| regs[*r as usize].clone()).collect();
                regs[*dst as usize] = Value::Closure { fn_idx: *fn_idx, captured };
                pc += 1;
            }
            Instr::CallClosure(dst, closure_reg, arg_regs) => {
                // Read the closure, then call its lifted function with the captured
                // environment prepended to the explicit arguments.
                let (fn_idx, mut call_args) = match &regs[*closure_reg as usize] {
                    Value::Closure { fn_idx, captured } => (*fn_idx, captured.clone()),
                    other => {
                        return Err(format!("indirect call of non-closure: {other:?}"));
                    }
                };
                call_args.extend(arg_regs.iter().map(|r| regs[*r as usize].clone()));
                let result = exec_fn(bc, fn_idx, &call_args)?;
                regs[*dst as usize] = result;
                pc += 1;
            }
            Instr::Jump(off) => {
                pc = *off;
            }
            Instr::Branch(cond, then_off, else_off) => match &regs[*cond as usize] {
                Value::Bool(true) => pc = *then_off,
                Value::Bool(false) => pc = *else_off,
                other => return Err(format!("branch on non-bool: {other:?}")),
            },
            Instr::MakeAdt(dst, tag, field_regs) => {
                // Collect the field registers into an owned aggregate value.
                let fields: Vec<Value> =
                    field_regs.iter().map(|r| regs[*r as usize].clone()).collect();
                regs[*dst as usize] = Value::Adt { tag: *tag, fields };
                pc += 1;
            }
            Instr::Field(dst, src, field) => {
                // Project one field out of an Adt value.
                let v = match &regs[*src as usize] {
                    Value::Adt { fields, .. } => fields
                        .get(*field as usize)
                        .cloned()
                        .ok_or_else(|| format!("field index {field} out of range"))?,
                    other => {
                        return Err(format!("field projection on non-Adt: {other:?}"));
                    }
                };
                regs[*dst as usize] = v;
                pc += 1;
            }
            Instr::IndexGet(dst, base, idx) => {
                // Read element `idx` out of the aggregate (tuple/array) in `base`.
                // The verifier proves the index in-range; the bounds check here is a
                // runtime safety net.
                let i = as_int(regs[*idx as usize].clone())?;
                let v = match &regs[*base as usize] {
                    Value::Adt { fields, .. } => {
                        let i: usize = i
                            .try_into()
                            .map_err(|_| format!("index {i} out of range"))?;
                        fields
                            .get(i)
                            .cloned()
                            .ok_or_else(|| format!("index {i} out of range"))?
                    }
                    other => {
                        return Err(format!("index projection on non-Adt: {other:?}"));
                    }
                };
                regs[*dst as usize] = v;
                pc += 1;
            }
            Instr::IndexSet(base, idx, val) => {
                // Write `val` into element `idx` of the array in local `base`,
                // mutating it in place. OOB is a runtime safety net (the verifier is
                // expected to have proven the index in-range).
                let i = as_int(regs[*idx as usize].clone())?;
                let v = regs[*val as usize].clone();
                match &mut regs[*base as usize] {
                    Value::Adt { fields, .. } => {
                        let i: usize = i
                            .try_into()
                            .map_err(|_| format!("index {i} out of range"))?;
                        let cell = fields
                            .get_mut(i)
                            .ok_or_else(|| format!("index {i} out of range"))?;
                        *cell = v;
                    }
                    other => {
                        return Err(format!("indexed store into non-Adt: {other:?}"));
                    }
                }
                pc += 1;
            }
            Instr::VecLen(dst, vec_reg) => {
                // Read the vec's `Adt` and put its element count into `dst`.
                let n = match &regs[*vec_reg as usize] {
                    Value::Adt { fields, .. } => fields.len() as i64,
                    other => {
                        return Err(format!("VecLen on non-Adt: {other:?}"));
                    }
                };
                regs[*dst as usize] = Value::Int(n);
                pc += 1;
            }
            Instr::VecPush(dst, vec_reg, val) => {
                // Functionally append: clone the vec's fields, push `val`, and write
                // the new `Adt` (same tag) into `dst`. Cloning first makes this correct
                // even when `dst` aliases `vec_reg`.
                let v = regs[*val as usize].clone();
                let new_val = match &regs[*vec_reg as usize] {
                    Value::Adt { tag, fields } => {
                        let mut fields = fields.clone();
                        fields.push(v);
                        Value::Adt { tag: *tag, fields }
                    }
                    other => {
                        return Err(format!("VecPush on non-Adt: {other:?}"));
                    }
                };
                regs[*dst as usize] = new_val;
                pc += 1;
            }
            Instr::Switch(src, table, otherwise) => {
                // Read the scrutinee's tag and jump to the matching arm.
                let tag = match &regs[*src as usize] {
                    Value::Adt { tag, .. } => *tag,
                    other => {
                        return Err(format!("match on non-Adt scrutinee: {other:?}"));
                    }
                };
                match table.iter().find(|(t, _)| *t == tag) {
                    Some((_, off)) => pc = *off,
                    None => match otherwise {
                        Some(off) => pc = *off,
                        None => return Err("no matching arm".to_string()),
                    },
                }
            }
            Instr::Alloc(local) => {
                // Box the local: move its current value into a fresh store cell and
                // overwrite the register with a `Ref` to that cell.
                let addr = store.len();
                let v = std::mem::replace(&mut regs[*local as usize], Value::Ref(addr));
                store.push(v);
                pc += 1;
            }
            Instr::Load(dst, src) => {
                // `src` holds a `Ref(addr)`; copy the cell's value into `dst`.
                let addr = as_ref(&regs[*src as usize])?;
                let v = store
                    .get(addr)
                    .ok_or_else(|| format!("load: bad store address {addr}"))?
                    .clone();
                regs[*dst as usize] = v;
                pc += 1;
            }
            Instr::Store(ref_reg, val) => {
                // `ref_reg` holds a `Ref(addr)`; write `val` into that cell so the
                // mutation is visible at the original (boxed) location.
                let addr = as_ref(&regs[*ref_reg as usize])?;
                let v = regs[*val as usize].clone();
                let cell = store
                    .get_mut(addr)
                    .ok_or_else(|| format!("store: bad store address {addr}"))?;
                *cell = v;
                pc += 1;
            }
            Instr::Trap(msg) => {
                return Err(msg.clone());
            }
            Instr::Ret(src) => {
                return Ok(regs[*src as usize].clone());
            }
        }
    }
}

/// Read a reference's store address, or error if the value is not a `Ref`
/// (e.g. dereferencing a non-reference).
fn as_ref(v: &Value) -> Result<usize, String> {
    match v {
        Value::Ref(addr) => Ok(*addr),
        other => Err(format!("expected a reference, got {other:?}")),
    }
}

fn const_to_value(c: Const) -> Value {
    match c {
        Const::Int(i) => Value::Int(i),
        Const::Bool(b) => Value::Bool(b),
        Const::Unit => Value::Unit,
    }
}

/// Evaluate a binary op under i64 / bool semantics.
fn eval_bin(op: BinOp, a: Value, b: Value) -> Result<Value, String> {
    use BinOp::*;
    match op {
        Add | Sub | Mul | Div | Mod => {
            let (x, y) = (as_int(a)?, as_int(b)?);
            let r = match op {
                Add => x.wrapping_add(y),
                Sub => x.wrapping_sub(y),
                Mul => x.wrapping_mul(y),
                Div => {
                    if y == 0 {
                        return Err("division by zero".to_string());
                    }
                    x.wrapping_div(y)
                }
                Mod => {
                    if y == 0 {
                        return Err("division by zero".to_string());
                    }
                    x.wrapping_rem(y)
                }
                _ => unreachable!(),
            };
            Ok(Value::Int(r))
        }
        BitAnd | BitOr | BitXor | Shl | Shr => {
            let (x, y) = (as_int(a)?, as_int(b)?);
            let r = match op {
                BitAnd => x & y,
                BitOr => x | y,
                BitXor => x ^ y,
                Shl => x.wrapping_shl(y as u32),
                Shr => x.wrapping_shr(y as u32),
                _ => unreachable!(),
            };
            Ok(Value::Int(r))
        }
        And => Ok(Value::Bool(as_bool(a)? && as_bool(b)?)),
        Or => Ok(Value::Bool(as_bool(a)? || as_bool(b)?)),
        Eq => Ok(Value::Bool(a == b)),
        Ne => Ok(Value::Bool(a != b)),
        Lt | Le | Gt | Ge => {
            let (x, y) = (as_int(a)?, as_int(b)?);
            let r = match op {
                Lt => x < y,
                Le => x <= y,
                Gt => x > y,
                Ge => x >= y,
                _ => unreachable!(),
            };
            Ok(Value::Bool(r))
        }
    }
}

fn eval_un(op: UnOp, v: Value) -> Result<Value, String> {
    match op {
        UnOp::Neg => Ok(Value::Int(as_int(v)?.wrapping_neg())),
        UnOp::Not => Ok(Value::Bool(!as_bool(v)?)),
    }
}

fn as_int(v: Value) -> Result<i64, String> {
    match v {
        Value::Int(i) => Ok(i),
        other => Err(format!("expected Int, got {other:?}")),
    }
}

fn as_bool(v: Value) -> Result<bool, String> {
    match v {
        Value::Bool(b) => Ok(b),
        other => Err(format!("expected Bool, got {other:?}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rv_codegen::compile;
    use rv_core::{BinOp, Prop, Symbols};
    use rv_ir::{
        AggKind, Block, BlockId, BorrowKind, Const, FieldDef, Function, LocalDecl, LocalId,
        Lowerable, MatchArm, Operand, Place, Proj, Program, RValue, Stmt, Terminator, TypeDef,
    };

    /// Helper: an Int-typed local decl.
    fn int_local() -> LocalDecl<Lowerable> {
        LocalDecl { name: None, ty: rv_core::Ty::Int }
    }
    fn bool_local() -> LocalDecl<Lowerable> {
        LocalDecl { name: None, ty: rv_core::Ty::Bool }
    }

    fn copy(l: u32) -> Operand {
        Operand::Copy(Place::local(LocalId(l)))
    }

    /// `main()` computes `(10 / 2) + 1` and returns it. Then asserts == 6.
    #[test]
    fn arithmetic_div_add() {
        let mut syms = Symbols::new();
        let name = syms.intern("main");

        // locals: 0 = result accumulator
        let func = Function::<Lowerable> {
            type_params: vec![],
            name,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![int_local()], // l0
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![
                    // l0 = 10 / 2
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Bin(
                            BinOp::Div,
                            Operand::Const(Const::Int(10)),
                            Operand::Const(Const::Int(2)),
                        ),
                    ),
                    // l0 = l0 + 1
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Bin(BinOp::Add, copy(0), Operand::Const(Const::Int(1))),
                    ),
                    // ghost: erased
                    Stmt::Assert(Prop::True),
                ],
                term: Terminator::Return(copy(0)),
            }],
            entry: BlockId(0),
        };

        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        let result = run(&bc, "main", &[]).unwrap();
        assert_eq!(result, Value::Int(6));
    }

    /// Division by zero surfaces as a runtime error.
    #[test]
    fn div_by_zero_errors() {
        let mut syms = Symbols::new();
        let name = syms.intern("main");
        let func = Function::<Lowerable> {
            type_params: vec![],
            name,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![int_local()],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![Stmt::Assign(
                    Place::local(LocalId(0)),
                    RValue::Bin(
                        BinOp::Div,
                        Operand::Const(Const::Int(1)),
                        Operand::Const(Const::Int(0)),
                    ),
                )],
                term: Terminator::Return(copy(0)),
            }],
            entry: BlockId(0),
        };
        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "main", &[]), Err("division by zero".to_string()));
    }

    /// `abs(x)`: if x < 0 return -x else return x. Tests branch + neg.
    #[test]
    fn branch_if() {
        let mut syms = Symbols::new();
        let name = syms.intern("abs");
        // params: l0 = x. locals: l0 = x, l1 = cond, l2 = result
        let func = Function::<Lowerable> {
            type_params: vec![],
            name,
            params: vec![LocalId(0)],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![int_local(), bool_local(), int_local()],
            blocks: vec![
                // b0: l1 = x < 0; branch l1 -> b1 (neg), b2 (id)
                Block {
                    id: BlockId(0),
                    stmts: vec![Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Bin(BinOp::Lt, copy(0), Operand::Const(Const::Int(0))),
                    )],
                    term: Terminator::Branch {
                        cond: copy(1),
                        then_blk: BlockId(1),
                        else_blk: BlockId(2),
                    },
                },
                // b1: l2 = -x; return l2
                Block {
                    id: BlockId(1),
                    stmts: vec![Stmt::Assign(
                        Place::local(LocalId(2)),
                        RValue::Un(rv_core::UnOp::Neg, copy(0)),
                    )],
                    term: Terminator::Return(copy(2)),
                },
                // b2: return x
                Block {
                    id: BlockId(2),
                    stmts: vec![],
                    term: Terminator::Return(copy(0)),
                },
            ],
            entry: BlockId(0),
        };
        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "abs", &[Value::Int(-7)]).unwrap(), Value::Int(7));
        assert_eq!(run(&bc, "abs", &[Value::Int(5)]).unwrap(), Value::Int(5));
    }

    /// A function call: `main()` calls `add(4, 5)` and returns 9.
    #[test]
    fn function_call() {
        let mut syms = Symbols::new();
        let add = syms.intern("add");
        let main = syms.intern("main");

        // add(a, b): l0=a, l1=b, l2=sum
        let add_fn = Function::<Lowerable> {
            type_params: vec![],
            name: add,
            params: vec![LocalId(0), LocalId(1)],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![int_local(), int_local(), int_local()],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![Stmt::Assign(
                    Place::local(LocalId(2)),
                    RValue::Bin(BinOp::Add, copy(0), copy(1)),
                )],
                term: Terminator::Return(copy(2)),
            }],
            entry: BlockId(0),
        };

        // main(): l0 = add(4, 5); return l0
        let main_fn = Function::<Lowerable> {
            type_params: vec![],
            name: main,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![int_local()],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![Stmt::Assign(
                    Place::local(LocalId(0)),
                    RValue::Call(
                        add,
                        vec![Operand::Const(Const::Int(4)), Operand::Const(Const::Int(5))],
                    ),
                )],
                term: Terminator::Return(copy(0)),
            }],
            entry: BlockId(0),
        };

        let prog = Program { types: vec![], funcs: vec![add_fn, main_fn] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "main", &[]).unwrap(), Value::Int(9));
    }

    /// The headline example: `(10 / 2) + 1 == 6` evaluates to `true`.
    #[test]
    fn equals_six() {
        let mut syms = Symbols::new();
        let name = syms.intern("main");
        let func = Function::<Lowerable> {
            type_params: vec![],
            name,
            params: vec![],
            ret: rv_core::Ty::Bool,
            pre: Prop::True,
            post: Prop::True,
            // l0 = (10/2)+1, l1 = bool result
            locals: vec![int_local(), bool_local()],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Bin(
                            BinOp::Div,
                            Operand::Const(Const::Int(10)),
                            Operand::Const(Const::Int(2)),
                        ),
                    ),
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Bin(BinOp::Add, copy(0), Operand::Const(Const::Int(1))),
                    ),
                    Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Bin(BinOp::Eq, copy(0), Operand::Const(Const::Int(6))),
                    ),
                ],
                term: Terminator::Return(copy(1)),
            }],
            entry: BlockId(0),
        };
        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "main", &[]).unwrap(), Value::Bool(true));
    }

    /// Construct a struct `Point { x, y }` from two ints, then read field `0`
    /// (x) back out and return it. Exercises `MakeAdt` + `Field` projection.
    #[test]
    fn struct_construct_and_field() {
        let mut syms = Symbols::new();
        let main = syms.intern("main");
        let point = syms.intern("Point");

        // locals: l0 = the Point value, l1 = the extracted field
        let func = Function::<Lowerable> {
            type_params: vec![],
            name: main,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![
                LocalDecl { name: None, ty: rv_core::Ty::Adt(point) }, // l0: Point
                int_local(),                                          // l1: x
            ],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![
                    // l0 = Point { 3, 4 }  (struct tag is 0)
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Aggregate(
                            AggKind::Struct(point),
                            vec![
                                Operand::Const(Const::Int(3)),
                                Operand::Const(Const::Int(4)),
                            ],
                        ),
                    ),
                    // l1 = l0.0   (read field 0 via a Field projection)
                    Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Use(Operand::Copy(Place {
                            local: LocalId(0),
                            proj: vec![Proj::Field(0)],
                        })),
                    ),
                ],
                term: Terminator::Return(copy(1)),
            }],
            entry: BlockId(0),
        };

        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "main", &[]).unwrap(), Value::Int(3));
    }

    /// Build an `Option`-like enum value `Some(7)` (variant index 1), `match` on
    /// it, and return the payload in the `Some` arm (7) or a sentinel in `None`.
    /// Exercises `MakeAdt` (tagged), `Switch`, and `Downcast`+`Field` binding.
    #[test]
    fn enum_match_some() {
        let mut syms = Symbols::new();
        let main = syms.intern("main");
        let option = syms.intern("Option");

        // Variant indices: None = 0, Some = 1.
        // locals: l0 = the Option value, l1 = the result.
        let func = Function::<Lowerable> {
            type_params: vec![],
            name: main,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![
                LocalDecl { name: None, ty: rv_core::Ty::Adt(option) }, // l0: Option
                int_local(),                                           // l1: result
            ],
            blocks: vec![
                // b0: l0 = Some(7); match l0 { None => b1, Some => b2 }
                Block {
                    id: BlockId(0),
                    stmts: vec![Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Aggregate(
                            AggKind::Variant(option, 1),
                            vec![Operand::Const(Const::Int(7))],
                        ),
                    )],
                    term: Terminator::Match {
                        scrutinee: copy(0),
                        arms: vec![
                            MatchArm { variant: 0, target: BlockId(1) },
                            MatchArm { variant: 1, target: BlockId(2) },
                        ],
                        otherwise: None,
                    },
                },
                // b1 (None): l1 = -1; return l1
                Block {
                    id: BlockId(1),
                    stmts: vec![Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Use(Operand::Const(Const::Int(-1))),
                    )],
                    term: Terminator::Return(copy(1)),
                },
                // b2 (Some): l1 = l0 downcast-to-Some .field(0); return l1
                Block {
                    id: BlockId(2),
                    stmts: vec![Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Use(Operand::Copy(Place {
                            local: LocalId(0),
                            proj: vec![Proj::Downcast(1), Proj::Field(0)],
                        })),
                    )],
                    term: Terminator::Return(copy(1)),
                },
            ],
            entry: BlockId(0),
        };

        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "main", &[]).unwrap(), Value::Int(7));
    }

    // --- Reference tests ---

    fn deref(l: u32) -> Place {
        Place { local: LocalId(l), proj: vec![Proj::Deref] }
    }

    /// `let x = 1; let r = &mut x; *r = 5; return x;` -> mutation through the `&mut`
    /// is visible at `x`, so the result is `Int(5)`. `x` is boxed (address-taken).
    #[test]
    fn mutate_through_mut_ref() {
        let mut syms = Symbols::new();
        let main = syms.intern("main");
        // locals: l0 = x, l1 = r (a reference to x)
        let func = Function::<Lowerable> {
            type_params: vec![],
            name: main,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![int_local(), int_local()],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![
                    // x = 1
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Use(Operand::Const(Const::Int(1))),
                    ),
                    // r = &mut x
                    Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Ref(BorrowKind::Mut, Place::local(LocalId(0))),
                    ),
                    // *r = 5
                    Stmt::Assign(deref(1), RValue::Use(Operand::Const(Const::Int(5)))),
                ],
                // return x  (reads the boxed local through its cell)
                term: Terminator::Return(copy(0)),
            }],
            entry: BlockId(0),
        };
        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "main", &[]).unwrap(), Value::Int(5));
    }

    /// `let x = 7; let r = &x; return *r;` -> reading through a shared reference
    /// yields `Int(7)`.
    #[test]
    fn read_through_shared_ref() {
        let mut syms = Symbols::new();
        let main = syms.intern("main");
        // locals: l0 = x, l1 = r, l2 = the dereffed value
        let func = Function::<Lowerable> {
            type_params: vec![],
            name: main,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![int_local(), int_local(), int_local()],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![
                    // x = 7
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Use(Operand::Const(Const::Int(7))),
                    ),
                    // r = &x
                    Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Ref(BorrowKind::Shared, Place::local(LocalId(0))),
                    ),
                    // l2 = *r
                    Stmt::Assign(
                        Place::local(LocalId(2)),
                        RValue::Use(Operand::Copy(deref(1))),
                    ),
                ],
                term: Terminator::Return(copy(2)),
            }],
            entry: BlockId(0),
        };
        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "main", &[]).unwrap(), Value::Int(7));
    }

    /// Reading a field of a struct *through* a reference: `r = &p; return (*r).0`.
    /// Exercises a `Deref` followed by a `Field` projection.
    #[test]
    fn read_field_through_ref() {
        let mut syms = Symbols::new();
        let main = syms.intern("main");
        let point = syms.intern("Point");
        // locals: l0 = p (a Point), l1 = r, l2 = field
        let func = Function::<Lowerable> {
            type_params: vec![],
            name: main,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![
                LocalDecl { name: None, ty: rv_core::Ty::Adt(point) },
                int_local(),
                int_local(),
            ],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![
                    // p = Point { 3, 4 }
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Aggregate(
                            AggKind::Struct(point),
                            vec![
                                Operand::Const(Const::Int(3)),
                                Operand::Const(Const::Int(4)),
                            ],
                        ),
                    ),
                    // r = &p
                    Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Ref(BorrowKind::Shared, Place::local(LocalId(0))),
                    ),
                    // l2 = (*r).1
                    Stmt::Assign(
                        Place::local(LocalId(2)),
                        RValue::Use(Operand::Copy(Place {
                            local: LocalId(1),
                            proj: vec![Proj::Deref, Proj::Field(1)],
                        })),
                    ),
                ],
                term: Terminator::Return(copy(2)),
            }],
            entry: BlockId(0),
        };
        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "main", &[]).unwrap(), Value::Int(4));
    }

    /// A whole-pointee store overwriting a struct value through a `&mut`:
    /// `r = &mut p; *r = Point{9,9}; return p.0` -> `Int(9)`.
    #[test]
    fn store_whole_pointee_through_ref() {
        let mut syms = Symbols::new();
        let main = syms.intern("main");
        let point = syms.intern("Point");
        // locals: l0 = p, l1 = r, l2 = field read-back
        let func = Function::<Lowerable> {
            type_params: vec![],
            name: main,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![
                LocalDecl { name: None, ty: rv_core::Ty::Adt(point) },
                int_local(),
                int_local(),
            ],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Aggregate(
                            AggKind::Struct(point),
                            vec![
                                Operand::Const(Const::Int(1)),
                                Operand::Const(Const::Int(2)),
                            ],
                        ),
                    ),
                    Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Ref(BorrowKind::Mut, Place::local(LocalId(0))),
                    ),
                    // *r = Point { 9, 9 }
                    Stmt::Assign(
                        deref(1),
                        RValue::Aggregate(
                            AggKind::Struct(point),
                            vec![
                                Operand::Const(Const::Int(9)),
                                Operand::Const(Const::Int(9)),
                            ],
                        ),
                    ),
                    // l2 = p.0
                    Stmt::Assign(
                        Place::local(LocalId(2)),
                        RValue::Use(Operand::Copy(Place {
                            local: LocalId(0),
                            proj: vec![Proj::Field(0)],
                        })),
                    ),
                ],
                term: Terminator::Return(copy(2)),
            }],
            entry: BlockId(0),
        };
        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "main", &[]).unwrap(), Value::Int(9));
    }

    /// Borrowing a sub-place is unsupported in this slice and traps at runtime.
    #[test]
    fn borrow_subplace_traps() {
        let mut syms = Symbols::new();
        let main = syms.intern("main");
        let point = syms.intern("Point");
        // r = &p.0  (a field sub-borrow) -> should trap
        let func = Function::<Lowerable> {
            type_params: vec![],
            name: main,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![
                LocalDecl { name: None, ty: rv_core::Ty::Adt(point) },
                int_local(),
            ],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Aggregate(
                            AggKind::Struct(point),
                            vec![
                                Operand::Const(Const::Int(3)),
                                Operand::Const(Const::Int(4)),
                            ],
                        ),
                    ),
                    Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Ref(
                            BorrowKind::Shared,
                            Place { local: LocalId(0), proj: vec![Proj::Field(0)] },
                        ),
                    ),
                ],
                term: Terminator::Return(copy(1)),
            }],
            entry: BlockId(0),
        };
        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        assert!(run(&bc, "main", &[]).is_err());
    }

    /// A `main` whose body is just `Terminator::Panic` aborts cleanly: the VM
    /// returns an `Err` whose message contains "panic", with no Rust panic.
    #[test]
    fn panic_terminator_aborts() {
        let mut syms = Symbols::new();
        let name = syms.intern("main");
        let func = Function::<Lowerable> {
            type_params: vec![],
            name,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![int_local()],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![],
                term: Terminator::Panic,
            }],
            entry: BlockId(0),
        };
        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        let err = run(&bc, "main", &[]).unwrap_err();
        assert!(err.contains("panic"), "expected a panic error, got {err:?}");
    }

    /// A `main` that branches and only panics on the *not-taken* path still
    /// returns the normal value: the taken path returns `42`, and the panic on
    /// the other arm is never reached.
    #[test]
    fn panic_on_not_taken_path_returns_value() {
        let mut syms = Symbols::new();
        let name = syms.intern("main");
        // l0 = cond, l1 = result
        let func = Function::<Lowerable> {
            type_params: vec![],
            name,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![bool_local(), int_local()],
            blocks: vec![
                // b0: cond = true; branch cond -> b1 (return 42), b2 (panic)
                Block {
                    id: BlockId(0),
                    stmts: vec![Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Use(Operand::Const(Const::Bool(true))),
                    )],
                    term: Terminator::Branch {
                        cond: copy(0),
                        then_blk: BlockId(1),
                        else_blk: BlockId(2),
                    },
                },
                // b1 (taken): l1 = 42; return l1
                Block {
                    id: BlockId(1),
                    stmts: vec![Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Use(Operand::Const(Const::Int(42))),
                    )],
                    term: Terminator::Return(copy(1)),
                },
                // b2 (not taken): panic
                Block {
                    id: BlockId(2),
                    stmts: vec![],
                    term: Terminator::Panic,
                },
            ],
            entry: BlockId(0),
        };
        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "main", &[]).unwrap(), Value::Int(42));
    }

    // --- Wave-3: generics + methods, after lowering desugars them away ---

    /// A generic identity function `fn id<T>(x: T) -> T { x }`. Generics are
    /// type-erased at runtime, so the `type_params` carry no runtime meaning — the
    /// body simply returns its parameter. Codegen ignores `type_params`; the
    /// function compiles and runs, returning whatever argument it is given.
    #[test]
    fn generic_identity_erases_and_runs() {
        let mut syms = Symbols::new();
        let id = syms.intern("id");
        let t = syms.intern("T"); // the (erased) generic type parameter

        // id<T>(x): l0 = x; return x.
        let func = Function::<Lowerable> {
            name: id,
            type_params: vec![t], // erased — present only to prove codegen ignores it
            params: vec![LocalId(0)],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![int_local()],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![],
                term: Terminator::Return(copy(0)),
            }],
            entry: BlockId(0),
        };

        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        // The argument comes straight back out, regardless of the erased `T`.
        assert_eq!(run(&bc, "id", &[Value::Int(42)]).unwrap(), Value::Int(42));
    }

    /// A "method" `Point::sum(self) -> i64 { self.x + self.y }` as lowering emits
    /// it: a plain free function taking `self` (the receiver struct) as its first
    /// parameter, plus a `main` that builds the `Point` and `Call`s the function —
    /// exactly the shape `p.sum()` desugars to. No new runtime behavior: it is an
    /// ordinary `Call` over an `Adt` argument with two `Field` reads.
    #[test]
    fn desugared_method_runs() {
        let mut syms = Symbols::new();
        let point = syms.intern("Point");
        let point_sum = syms.intern("point_sum");
        let main = syms.intern("main");

        // point_sum(self): l0 = self (a Point), l1 = self.x + self.y.
        // self.x is field 0, self.y is field 1.
        let sum_fn = Function::<Lowerable> {
            name: point_sum,
            type_params: vec![],
            params: vec![LocalId(0)],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![
                LocalDecl { name: None, ty: rv_core::Ty::Adt(point) }, // l0: self
                int_local(),                                          // l1: sum
            ],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![
                    // l1 = self.0 + self.1
                    Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Bin(
                            BinOp::Add,
                            Operand::Copy(Place {
                                local: LocalId(0),
                                proj: vec![Proj::Field(0)],
                            }),
                            Operand::Copy(Place {
                                local: LocalId(0),
                                proj: vec![Proj::Field(1)],
                            }),
                        ),
                    ),
                ],
                term: Terminator::Return(copy(1)),
            }],
            entry: BlockId(0),
        };

        // main(): l0 = Point { 3, 4 }; l1 = point_sum(l0); return l1.
        let main_fn = Function::<Lowerable> {
            name: main,
            type_params: vec![],
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![
                LocalDecl { name: None, ty: rv_core::Ty::Adt(point) }, // l0: the Point
                int_local(),                                          // l1: result
            ],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![
                    // l0 = Point { 3, 4 }
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Aggregate(
                            AggKind::Struct(point),
                            vec![
                                Operand::Const(Const::Int(3)),
                                Operand::Const(Const::Int(4)),
                            ],
                        ),
                    ),
                    // l1 = point_sum(l0)   <-- what `p.sum()` desugars to
                    Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Call(point_sum, vec![copy(0)]),
                    ),
                ],
                term: Terminator::Return(copy(1)),
            }],
            entry: BlockId(0),
        };

        // Declare the (generic-capable) struct type with empty type_params.
        let types = vec![TypeDef::Struct {
            name: point,
            type_params: vec![],
            fields: vec![
                FieldDef { name: syms.intern("x"), ty: rv_core::Ty::Int },
                FieldDef { name: syms.intern("y"), ty: rv_core::Ty::Int },
            ],
        }];

        let prog = Program { types, funcs: vec![sum_fn, main_fn] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "main", &[]).unwrap(), Value::Int(7));
    }

    /// Build an array `[10, 20, 30]`, overwrite element `1` with `99`
    /// (`a[1] = 99`), then read it back through a dynamic index (`a[1]`) and
    /// return it. Exercises array `MakeAdt` + `IndexSet` + `IndexGet`.
    #[test]
    fn array_construct_index_set_get() {
        let mut syms = Symbols::new();
        let main = syms.intern("main");

        // locals: l0 = the array value, l1 = the read-back element.
        let arr_ty = rv_core::Ty::Array(Box::new(rv_core::Ty::Int), 3);
        let func = Function::<Lowerable> {
            type_params: vec![],
            name: main,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![
                LocalDecl { name: None, ty: arr_ty }, // l0: [Int; 3]
                int_local(),                          // l1: read-back element
            ],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![
                    // l0 = [10, 20, 30]
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Aggregate(
                            AggKind::Array,
                            vec![
                                Operand::Const(Const::Int(10)),
                                Operand::Const(Const::Int(20)),
                                Operand::Const(Const::Int(30)),
                            ],
                        ),
                    ),
                    // l0[1] = 99
                    Stmt::Assign(
                        Place {
                            local: LocalId(0),
                            proj: vec![Proj::Index(Operand::Const(Const::Int(1)))],
                        },
                        RValue::Use(Operand::Const(Const::Int(99))),
                    ),
                    // l1 = l0[1]  (dynamic-index read)
                    Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Use(Operand::Copy(Place {
                            local: LocalId(0),
                            proj: vec![Proj::Index(Operand::Const(Const::Int(1)))],
                        })),
                    ),
                ],
                term: Terminator::Return(copy(1)),
            }],
            entry: BlockId(0),
        };

        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "main", &[]).unwrap(), Value::Int(99));
    }

    /// Construct a tuple `(5, 6)`, read element `1` back out, and return it.
    /// Exercises tuple `MakeAdt` + `Field` projection.
    #[test]
    fn tuple_construct_and_project() {
        let mut syms = Symbols::new();
        let main = syms.intern("main");

        let tup_ty = rv_core::Ty::Tuple(vec![rv_core::Ty::Int, rv_core::Ty::Int]);
        let func = Function::<Lowerable> {
            type_params: vec![],
            name: main,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![
                LocalDecl { name: None, ty: tup_ty }, // l0: (Int, Int)
                int_local(),                          // l1: extracted element
            ],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![
                    // l0 = (5, 6)
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Aggregate(
                            AggKind::Tuple,
                            vec![
                                Operand::Const(Const::Int(5)),
                                Operand::Const(Const::Int(6)),
                            ],
                        ),
                    ),
                    // l1 = l0.1   (tuple element via a Field projection)
                    Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Use(Operand::Copy(Place {
                            local: LocalId(0),
                            proj: vec![Proj::Field(1)],
                        })),
                    ),
                ],
                term: Terminator::Return(copy(1)),
            }],
            entry: BlockId(0),
        };

        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "main", &[]).unwrap(), Value::Int(6));
    }

    /// Build an empty `Vec` (`MakeAdt` with no fields), `VecPush` two values onto it,
    /// check `len() == 2`, read element `1` (`v[1]`), then overwrite element `0`
    /// (`v[0] = 99`) via `IndexSet` and read it back. Exercises the Vec aggregate,
    /// `VecPush`, `VecLen`, and the reused `IndexGet`/`IndexSet`.
    ///
    /// `which` selects what the built `main` returns, so one body can be exercised
    /// for each of the three observations (len, `v[1]`, `v[0]` after `IndexSet`).
    fn vec_main(name: rv_core::Sym, vec_sym: rv_core::Sym, ret: Terminator<Lowerable>) -> Function<Lowerable> {
        let vec_ty = rv_core::Ty::Adt(vec_sym);
        // locals: l0 = the vec, l1 = len, l2 = read-back element.
        Function::<Lowerable> {
            type_params: vec![],
            name,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![
                LocalDecl { name: None, ty: vec_ty }, // l0: Vec
                int_local(),                          // l1: len
                int_local(),                          // l2: read-back element
            ],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![
                    // l0 = Vec::new()  (empty aggregate, no fields)
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Aggregate(AggKind::Vec, vec![]),
                    ),
                    // l0 = VecPush(l0, 10)
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::VecPush(copy(0), Operand::Const(Const::Int(10))),
                    ),
                    // l0 = VecPush(l0, 20)
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::VecPush(copy(0), Operand::Const(Const::Int(20))),
                    ),
                    // l1 = l0.len()
                    Stmt::Assign(Place::local(LocalId(1)), RValue::VecLen(copy(0))),
                    // l2 = l0[1]  (dynamic-index read; expect 20)
                    Stmt::Assign(
                        Place::local(LocalId(2)),
                        RValue::Use(Operand::Copy(Place {
                            local: LocalId(0),
                            proj: vec![Proj::Index(Operand::Const(Const::Int(1)))],
                        })),
                    ),
                    // l0[0] = 99  (IndexSet on the Vec's Adt)
                    Stmt::Assign(
                        Place {
                            local: LocalId(0),
                            proj: vec![Proj::Index(Operand::Const(Const::Int(0)))],
                        },
                        RValue::Use(Operand::Const(Const::Int(99))),
                    ),
                    // l2 = l0[0]  (read back the element just written; expect 99)
                    Stmt::Assign(
                        Place::local(LocalId(2)),
                        RValue::Use(Operand::Copy(Place {
                            local: LocalId(0),
                            proj: vec![Proj::Index(Operand::Const(Const::Int(0)))],
                        })),
                    ),
                ],
                term: ret,
            }],
            entry: BlockId(0),
        }
    }

    #[test]
    fn vec_push_len_index() {
        let mut syms = Symbols::new();
        let main = syms.intern("main");
        let vec_sym = syms.intern("Vec");

        // len() == 2 (returns l1).
        let prog = Program { types: vec![], funcs: vec![vec_main(main, vec_sym, Terminator::Return(copy(1)))] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "main", &[]).unwrap(), Value::Int(2));

        // After `v[0] = 99` (IndexSet), the final write to l2 is `l0[0]` == 99,
        // so returning l2 verifies both IndexSet and the IndexGet read-back.
        let prog_99 = Program { types: vec![], funcs: vec![vec_main(main, vec_sym, Terminator::Return(copy(2)))] };
        let bc_99 = compile(&prog_99, &syms);
        assert_eq!(run(&bc_99, "main", &[]).unwrap(), Value::Int(99));
    }

    /// Focused check that indexing a freshly-pushed Vec reads the right element:
    /// push 10 then 20, return `v[1]` (== 20). Keeps the `v[1]` observation isolated
    /// from the later `IndexSet`.
    #[test]
    fn vec_index_get_after_push() {
        let mut syms = Symbols::new();
        let main = syms.intern("main");
        let vec_ty = rv_core::Ty::Adt(syms.intern("Vec"));
        let func = Function::<Lowerable> {
            type_params: vec![],
            name: main,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![
                LocalDecl { name: None, ty: vec_ty }, // l0: Vec
                int_local(),                          // l1: element
            ],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Aggregate(AggKind::Vec, vec![]),
                    ),
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::VecPush(copy(0), Operand::Const(Const::Int(10))),
                    ),
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::VecPush(copy(0), Operand::Const(Const::Int(20))),
                    ),
                    // l1 = l0[1]
                    Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Use(Operand::Copy(Place {
                            local: LocalId(0),
                            proj: vec![Proj::Index(Operand::Const(Const::Int(1)))],
                        })),
                    ),
                ],
                term: Terminator::Return(copy(1)),
            }],
            entry: BlockId(0),
        };
        let prog = Program { types: vec![], funcs: vec![func] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "main", &[]).unwrap(), Value::Int(20));
    }

    // --- Closures: first-class function values (closure conversion) ---

    /// Closure conversion end-to-end: a lifted function `add(captured, x) =
    /// captured + x`, a `main` that builds a closure capturing `base = 10`, then
    /// calls it indirectly with `5`. The VM prepends the captured `10` to the call
    /// args, so `add(10, 5) = 15`. Exercises `RValue::Closure`/`CallClosure` ->
    /// `MakeClosure`/`CallClosure` -> `Value::Closure` dispatch.
    #[test]
    fn closure_capture_and_indirect_call() {
        let mut syms = Symbols::new();
        let add = syms.intern("__closure_add");
        let main = syms.intern("main");

        // add(captured, x): l0 = captured, l1 = x, l2 = captured + x.
        let add_fn = Function::<Lowerable> {
            type_params: vec![],
            name: add,
            params: vec![LocalId(0), LocalId(1)],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![int_local(), int_local(), int_local()],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![Stmt::Assign(
                    Place::local(LocalId(2)),
                    RValue::Bin(BinOp::Add, copy(0), copy(1)),
                )],
                term: Terminator::Return(copy(2)),
            }],
            entry: BlockId(0),
        };

        // main(): l0 = 10; l1 = closure(add capturing l0); l2 = l1(5); return l2.
        let main_fn = Function::<Lowerable> {
            type_params: vec![],
            name: main,
            params: vec![],
            ret: rv_core::Ty::Int,
            pre: Prop::True,
            post: Prop::True,
            locals: vec![
                int_local(),                                                 // l0: base
                LocalDecl { name: None, ty: rv_core::Ty::Fn(vec![], Box::new(rv_core::Ty::Int)) }, // l1: closure
                int_local(),                                                 // l2: result
            ],
            blocks: vec![Block {
                id: BlockId(0),
                stmts: vec![
                    // l0 = 10
                    Stmt::Assign(
                        Place::local(LocalId(0)),
                        RValue::Use(Operand::Const(Const::Int(10))),
                    ),
                    // l1 = |x| base + x   (captures base = l0)
                    Stmt::Assign(
                        Place::local(LocalId(1)),
                        RValue::Closure(add, vec![copy(0)]),
                    ),
                    // l2 = l1(5)
                    Stmt::Assign(
                        Place::local(LocalId(2)),
                        RValue::CallClosure(copy(1), vec![Operand::Const(Const::Int(5))]),
                    ),
                ],
                term: Terminator::Return(copy(2)),
            }],
            entry: BlockId(0),
        };

        let prog = Program { types: vec![], funcs: vec![add_fn, main_fn] };
        let bc = compile(&prog, &syms);
        assert_eq!(run(&bc, "main", &[]).unwrap(), Value::Int(15));
    }
}
