//! Codegen: `IR<Lowerable>` -> a small register-based bytecode.
//!
//! Each IR function becomes a [`CompiledFn`] whose locals are registers (indexed
//! by `LocalId`'s `u32`). Each `Block` lowers to a contiguous run of [`Instr`];
//! block ids are resolved to instruction offsets at compile time so the VM never
//! has to search for a block.
//!
//! Ghost statements (`Stmt::Assert` / `Stmt::Assume`) are erased — they emit no
//! code. `Terminator::Drop` lowers to a plain jump (no runtime memory management
//! in this slice).

use rv_core::{BinOp, Symbols, UnOp};
use rv_ir::{
    AggKind, BlockId, BorrowKind, Function, LocalId, Lowerable, Operand, Place, Proj, Program,
    RValue, Stmt, Terminator,
};
use std::collections::HashSet;

// Re-export the types the bytecode embeds, so `rv-vm` (which depends on
// `rv-codegen` but neither `rv-ir` nor `rv-core` at runtime) can name them.
pub use rv_core::{BinOp as BinOpKind, UnOp as UnOpKind};
pub use rv_ir::Const;

/// One bytecode instruction. Operands are mostly local-register indices (`u32`).
///
/// A few instructions need a literal value; rather than invent a separate "load
/// immediate" form for every site, codegen materializes immediates with
/// [`Instr::Const`] into a fresh temporary register and then refers to that
/// register. This keeps the VM's operand model uniform: every operand is a
/// register read.
#[derive(Clone, Debug)]
pub enum Instr {
    /// `dst <- const`.
    Const(u32, Const),
    /// `dst <- src`.
    Move(u32, u32),
    /// `dst <- a <binop> b`.
    Bin(u32, BinOp, u32, u32),
    /// `dst <- <unop> src`.
    Un(u32, UnOp, u32),
    /// `dst <- callee(args...)`. `callee` indexes [`Bytecode::funcs`].
    Call(u32, usize, Vec<u32>),
    /// `dst <- closure of fn `fn_idx` capturing the values in `capture_regs``.
    /// Builds a first-class `Value::Closure`; `fn_idx` indexes [`Bytecode::funcs`].
    MakeClosure(u32, usize, Vec<u32>),
    /// `dst <- (closure in `closure_reg`)(args...)`. Indirect call: the closure's
    /// captured values are prepended to the argument registers before dispatch.
    CallClosure(u32, u32, Vec<u32>),
    /// Unconditional jump to an instruction offset within the current function.
    Jump(usize),
    /// If `cond` register is true jump to `then_off`, else to `else_off`.
    Branch(u32, usize, usize),
    /// Return the value in `src`.
    Ret(u32),
    /// `dst <- Adt { tag, fields: [src...] }`. Builds an algebraic data value from
    /// the given field registers. `tag` is the enum variant index (0 for structs).
    MakeAdt(u32, u32, Vec<u32>),
    /// `dst <- src.fields[field]`. Reads one field out of an `Adt` value. Nested
    /// projections are emitted as a chain of `Field` instructions through temps.
    Field(u32, u32, u32),
    /// `dst <- base.fields[idx]`. Reads one element out of an aggregate `Adt` value
    /// (a tuple or array) where the element position is the runtime integer in the
    /// `idx` register. The dynamic-index analogue of `Field`; emitted for
    /// `Proj::Index`.
    IndexGet(u32, u32, u32),
    /// `base.fields[idx] <- val`. Writes one element of the array `Adt` stored in the
    /// local `base`, using the runtime integer in the `idx` register, mutating the
    /// local in place. The dynamic-index analogue of a whole-local `Store`; emitted
    /// for `local[i] = v`.
    IndexSet(u32, u32, u32),
    /// `dst <- vec.len()`. Reads the `Adt` value in `vec_reg` and puts its element
    /// count (the number of `fields`) into `dst` as an integer `Value`. The runtime
    /// length query for a Vec, which is stored exactly like an array/tuple `Adt`.
    VecLen(u32, u32),
    /// `dst <- Adt { tag: vec.tag, fields: vec.fields ++ [val] }`. Functionally appends
    /// the value in `val_reg` to the `Adt` in `vec_reg`, writing the result to `dst`.
    /// The vec value is cloned, so this is correct whether or not `dst` aliases
    /// `vec_reg`; emitted for `v = VecPush(v, x)`.
    VecPush(u32, u32, u32),
    /// Switch on the `tag` of the `Adt` value in `src`. For each `(tag, off)` in the
    /// table, jump to `off` if `src.tag == tag`. If none match, jump to `otherwise`
    /// when present, else trap with a runtime error.
    Switch(u32, Vec<(u32, usize)>, Option<usize>),

    // --- References (a heap of cells) ---
    //
    // A reference is a `Value::Ref(addr)` indexing the VM's store (`Vec<Value>`).
    // A local that is ever borrowed (address-taken) is "boxed": its register holds
    // a `Value::Ref(addr)` to a store cell that holds the local's real value, and
    // every read/write of that local goes through the cell. Non-boxed locals stay
    // as plain registers (the fast path).
    /// Box `local`: allocate a fresh store cell initialized from the local's current
    /// register value, then overwrite the register with a `Ref` to that cell. Emitted
    /// once per boxed local at function entry (after parameters are in place).
    Alloc(u32),
    /// `dst <- store[addr]`, where `src` holds a `Value::Ref(addr)`. The load that
    /// realizes reading a boxed local's value or dereferencing a reference (`*r`).
    Load(u32, u32),
    /// `store[addr] <- val`, where `ref_reg` holds a `Value::Ref(addr)`. The store
    /// that realizes writing a boxed local (`l = v` when `l` is boxed) or storing
    /// through a reference (`*r = v`).
    Store(u32, u32),
    /// Unconditionally fail at runtime with a fixed message. Emitted by codegen for
    /// reference forms this slice does not support (e.g. borrowing a sub-place), so
    /// that `compile` stays infallible and the program traps cleanly if it reaches
    /// the unsupported construct.
    Trap(String),
}

/// A single compiled function: a flat instruction list plus register count.
#[derive(Clone, Debug)]
pub struct CompiledFn {
    /// Function name (for entry-point lookup / diagnostics).
    pub name: String,
    /// Number of parameters; arguments bind to registers `0..nparams`.
    pub nparams: usize,
    /// Total number of register slots a frame needs.
    pub nregs: usize,
    /// Flat instruction stream. `entry_off` is where execution starts.
    pub code: Vec<Instr>,
    /// Instruction offset of the entry block.
    pub entry_off: usize,
}

/// The compiled program: a table of functions. Function indices are stable and
/// are what [`Instr::Call`] refers to.
#[derive(Clone, Debug)]
pub struct Bytecode {
    pub funcs: Vec<CompiledFn>,
}

impl Bytecode {
    /// Look up a function index by name (used by the VM to resolve `entry`).
    pub fn func_index(&self, name: &str) -> Option<usize> {
        self.funcs.iter().position(|f| f.name == name)
    }
}

/// Compile a lowerable program to bytecode.
pub fn compile(prog: &Program<Lowerable>, syms: &Symbols) -> Bytecode {
    // First pass: assign every function a stable index and resolve callee names.
    let name_to_index: std::collections::HashMap<&str, usize> = prog
        .funcs
        .iter()
        .enumerate()
        .map(|(i, f)| (syms.resolve(f.name), i))
        .collect();

    let funcs = prog
        .funcs
        .iter()
        .map(|f| compile_fn(f, syms, &name_to_index))
        .collect();

    Bytecode { funcs }
}

/// Per-function lowering state.
struct FnBuilder<'a> {
    code: Vec<Instr>,
    /// Number of registers in use. IR locals occupy `0..locals.len()`; temporaries
    /// (for materialized immediates) are allocated above that.
    next_reg: u32,
    /// For each block (by storage slot), its starting instruction offset.
    block_offsets: Vec<Option<usize>>,
    /// Back-patch list: jump/branch targets pointing at a `BlockId`, rewritten to
    /// instruction offsets once every block's offset is known.
    fixups: Vec<Fixup>,
    syms: &'a Symbols,
    name_to_index: &'a std::collections::HashMap<&'a str, usize>,
    /// Locals that are address-taken (ever borrowed as a whole local). Their
    /// register holds a `Value::Ref(addr)` to a store cell; reads/writes go through
    /// the cell. See [`boxed_locals`].
    boxed: HashSet<u32>,
}

/// Compute the set of locals that must be boxed: those that are ever the target of
/// a whole-local borrow (`RValue::Ref(_, place)` with no projections). Sub-place
/// borrows (`&x.f`, `&*r`) are not boxed here — codegen rejects them as unsupported.
fn boxed_locals(f: &Function<Lowerable>) -> HashSet<u32> {
    let mut set = HashSet::new();
    for blk in &f.blocks {
        for stmt in &blk.stmts {
            if let Stmt::Assign(_, RValue::Ref(_, place)) = stmt {
                if place.proj.is_empty() {
                    set.insert(place.local.0);
                }
            }
        }
    }
    set
}

/// A jump/branch target that points at a `BlockId` and must be rewritten to an
/// instruction offset once every block's offset is known.
struct Fixup {
    instr: usize,
    slot: FixupSlot,
    target: BlockId,
}

enum FixupSlot {
    Jump,
    BranchThen,
    BranchElse,
    /// The `n`-th entry of a `Switch`'s `(tag, off)` table.
    SwitchArm(usize),
    /// A `Switch`'s `otherwise` target.
    SwitchOtherwise,
}

fn compile_fn(
    f: &Function<Lowerable>,
    syms: &Symbols,
    name_to_index: &std::collections::HashMap<&str, usize>,
) -> CompiledFn {
    let nlocals = f.locals.len();
    let boxed = boxed_locals(f);
    let mut b = FnBuilder {
        code: Vec::new(),
        next_reg: nlocals as u32,
        block_offsets: vec![None; f.blocks.len()],
        fixups: Vec::new(),
        syms,
        name_to_index,
        boxed,
    };

    // Box every address-taken local at function entry: allocate a store cell from
    // its current register value (a parameter, or the default `Unit`) and replace
    // the register with a `Ref` to that cell. The `Alloc`s form a prelude at offset
    // 0 followed by a `Jump` to the entry block, so they execute exactly once no
    // matter which storage slot holds the entry block (and even if the entry block
    // is a back-edge target, the jump lands *past* the prelude). When there are no
    // boxed locals the prelude is empty and `entry_off` points straight at entry.
    let has_prelude = !b.boxed.is_empty();
    if has_prelude {
        let mut prelude: Vec<u32> = b.boxed.iter().copied().collect();
        prelude.sort_unstable(); // deterministic order
        for local in prelude {
            b.code.push(Instr::Alloc(local));
        }
        let jmp = b.code.len();
        b.code.push(Instr::Jump(usize::MAX)); // patched to the entry block below
        b.fixups.push(Fixup { instr: jmp, slot: FixupSlot::Jump, target: f.entry });
    }

    // BlockId is not guaranteed to equal the storage slot, so map id -> slot.
    let id_to_slot: std::collections::HashMap<u32, usize> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(i, blk)| (blk.id.0, i))
        .collect();

    for blk in &f.blocks {
        // Record where this block begins.
        let slot = id_to_slot[&blk.id.0];
        b.block_offsets[slot] = Some(b.code.len());

        for stmt in &blk.stmts {
            b.lower_stmt(stmt);
        }
        b.lower_terminator(&blk.term);
    }

    // Resolve fixups now that all block offsets are known.
    b.resolve_fixups(&id_to_slot);

    // With a prelude, execution starts at offset 0 (the `Alloc`s) which then jumps
    // into the entry block; otherwise it starts at the entry block directly.
    let entry_off = if has_prelude {
        0
    } else {
        let entry_slot = id_to_slot[&f.entry.0];
        b.block_offsets[entry_slot].expect("entry block emitted")
    };

    CompiledFn {
        name: syms.resolve(f.name).to_string(),
        nparams: f.params.len(),
        nregs: b.next_reg as usize,
        code: b.code,
        entry_off,
    }
}

impl FnBuilder<'_> {
    /// Allocate a fresh temporary register.
    fn fresh(&mut self) -> u32 {
        let r = self.next_reg;
        self.next_reg += 1;
        r
    }

    /// Resolve an operand to a register holding its value, emitting a `Const`
    /// into a temporary when the operand is an immediate, or a chain of `Field`
    /// extracts when the place carries projections.
    fn operand_reg(&mut self, op: &Operand) -> u32 {
        match op {
            Operand::Copy(place) => self.place_reg(place),
            Operand::Const(c) => {
                let r = self.fresh();
                self.code.push(Instr::Const(r, *c));
                r
            }
        }
    }

    /// Materialize a register holding the *value* of a local. For a boxed
    /// (address-taken) local, its register holds a `Ref`, so we `Load` through it;
    /// for a plain local the register *is* the value.
    fn local_value_reg(&mut self, local: LocalId) -> u32 {
        if self.boxed.contains(&local.0) {
            let dst = self.fresh();
            self.code.push(Instr::Load(dst, local.0));
            dst
        } else {
            local.0
        }
    }

    /// Read the value of a `Place` (the local's value projected through `proj`)
    /// into a register. With no projections this is just the local's value register.
    /// `Proj::Field(n)` emits a `Field` extract into a fresh temp; `Proj::Downcast`
    /// is a runtime no-op (the value already carries its tag); `Proj::Deref` follows
    /// a reference by `Load`ing the store cell it points at.
    fn place_reg(&mut self, place: &Place) -> u32 {
        let mut cur = self.local_value_reg(place.local);
        for p in &place.proj {
            match p {
                Proj::Field(n) => {
                    let dst = self.fresh();
                    self.code.push(Instr::Field(dst, cur, *n));
                    cur = dst;
                }
                Proj::Index(idx_operand) => {
                    // Dynamic element read `cur[idx]`: evaluate the index operand,
                    // then extract that element out of the aggregate.
                    let idx = self.operand_reg(idx_operand);
                    let dst = self.fresh();
                    self.code.push(Instr::IndexGet(dst, cur, idx));
                    cur = dst;
                }
                // Downcast just reinterprets the (already tagged) value: no code.
                Proj::Downcast(_) => {}
                Proj::Deref => {
                    // `cur` holds a `Ref(addr)`; load the pointee out of the store.
                    let dst = self.fresh();
                    self.code.push(Instr::Load(dst, cur));
                    cur = dst;
                }
            }
        }
        cur
    }

    fn lower_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            // Ghost statements are erased.
            Stmt::Assert(_) | Stmt::Assume(_) | Stmt::Invariant(_) => {}
            Stmt::Assign(place, rvalue) => self.lower_assign(place, rvalue),
        }
    }

    /// Lower an assignment `place = rvalue`, dispatching on the place's shape:
    ///
    /// * no projection, plain local      -> compute into the local's register;
    /// * no projection, boxed local      -> compute into a temp, `Store` to its cell;
    /// * place ends in `Deref` (`*r = v`)-> evaluate the reference, `Store` through it;
    /// * any other projected store       -> unsupported in this slice (`Trap`).
    fn lower_assign(&mut self, place: &Place, rvalue: &RValue) {
        // Whole-local assignment (no projection).
        if place.proj.is_empty() {
            if self.boxed.contains(&place.local.0) {
                // Boxed local: compute the value, then write it into the store cell.
                let val = self.rvalue_reg(rvalue);
                self.code.push(Instr::Store(place.local.0, val));
            } else {
                // Plain register local: the original fast path.
                self.lower_rvalue(place.local.0, rvalue);
            }
            return;
        }

        // Store through a reference: the place is `*r` (optionally with the deref as
        // the final projection). Evaluate the reference, then store into its cell.
        if matches!(place.proj.last(), Some(Proj::Deref)) {
            // The reference value is the place with the trailing `Deref` removed.
            let base = Place {
                local: place.local,
                proj: place.proj[..place.proj.len() - 1].to_vec(),
            };
            let ref_reg = self.place_reg(&base);
            let val = self.rvalue_reg(rvalue);
            self.code.push(Instr::Store(ref_reg, val));
            return;
        }

        // Indexed store into an array held directly by a local: `local[i] = v`. We
        // support only a single `Index` projection off a bare (unboxed) local; the
        // element is written in place, analogous to a whole-local `Store`.
        if let [Proj::Index(idx_operand)] = place.proj.as_slice() {
            if !self.boxed.contains(&place.local.0) {
                let idx = self.operand_reg(idx_operand);
                let val = self.rvalue_reg(rvalue);
                self.code
                    .push(Instr::IndexSet(place.local.0, idx, val));
                return;
            }
        }

        // Projected stores that are not a whole-pointee `*r = v` (e.g. `l.f = v`,
        // `*r.f = v`) need read-modify-write of an aggregate, which this slice does
        // not implement; trap cleanly rather than silently miscompile.
        self.code.push(Instr::Trap(
            "codegen: unsupported store into a projected place (only `l = v` and \
             `*r = v` are supported)"
                .to_string(),
        ));
    }

    /// Evaluate an `RValue` into a fresh register and return it. Used where we need
    /// the value materialized somewhere other than a destination local (stores).
    fn rvalue_reg(&mut self, rvalue: &RValue) -> u32 {
        // `Use` of an operand can reuse that operand's register directly.
        if let RValue::Use(op) = rvalue {
            return self.operand_reg(op);
        }
        let dst = self.fresh();
        self.lower_rvalue(dst, rvalue);
        dst
    }

    fn lower_rvalue(&mut self, dst: u32, rvalue: &RValue) {
        match rvalue {
            RValue::Use(op) => match op {
                Operand::Const(c) => self.code.push(Instr::Const(dst, *c)),
                Operand::Copy(place) => {
                    let src = self.place_reg(place);
                    if src != dst {
                        self.code.push(Instr::Move(dst, src));
                    }
                }
            },
            // Checked and wrapping binary ops generate identical machine
            // arithmetic; they differ only in which obligations the verifier emits.
            RValue::Bin(op, a, bb) | RValue::WrappingBin(op, a, bb) => {
                let ra = self.operand_reg(a);
                let rb = self.operand_reg(bb);
                self.code.push(Instr::Bin(dst, *op, ra, rb));
            }
            RValue::Un(op, a) => {
                let ra = self.operand_reg(a);
                self.code.push(Instr::Un(dst, *op, ra));
            }
            RValue::Call(callee, args) => {
                let arg_regs: Vec<u32> = args.iter().map(|a| self.operand_reg(a)).collect();
                let idx = *self
                    .name_to_index
                    .get(self.syms.resolve(*callee))
                    .expect("call to undefined function");
                self.code.push(Instr::Call(dst, idx, arg_regs));
            }
            // Closure conversion: resolve the lifted function to its index, evaluate
            // the captured operands, and build a first-class closure value.
            RValue::Closure(func, captures) => {
                let capture_regs: Vec<u32> =
                    captures.iter().map(|c| self.operand_reg(c)).collect();
                let idx = *self
                    .name_to_index
                    .get(self.syms.resolve(*func))
                    .expect("closure over undefined function");
                self.code.push(Instr::MakeClosure(dst, idx, capture_regs));
            }
            // Indirect call through a closure value: evaluate the callee and args; the
            // VM prepends the closure's captured environment before dispatch.
            RValue::CallClosure(callee, args) => {
                let closure_reg = self.operand_reg(callee);
                let arg_regs: Vec<u32> = args.iter().map(|a| self.operand_reg(a)).collect();
                self.code.push(Instr::CallClosure(dst, closure_reg, arg_regs));
            }
            RValue::Aggregate(kind, operands) => {
                // Evaluate each field operand into a register, then build the Adt.
                let field_regs: Vec<u32> =
                    operands.iter().map(|op| self.operand_reg(op)).collect();
                // tag: variant index for enums, 0 for structs.
                let tag = match kind {
                    AggKind::Struct(_) => 0,
                    AggKind::Variant(_, idx) => *idx,
                    // Tuples and arrays are untagged aggregates: build them like a
                    // struct (tag 0) holding their elements as fields, in order.
                    AggKind::Tuple | AggKind::Array | AggKind::Vec => 0,
                };
                self.code.push(Instr::MakeAdt(dst, tag, field_regs));
            }
            // `v.len()`: read the vec's `Adt` and put its element count into `dst`.
            RValue::VecLen(op) => {
                let vec_reg = self.operand_reg(op);
                self.code.push(Instr::VecLen(dst, vec_reg));
            }
            // `v = VecPush(v, x)`: functionally append `val` to the vec, into `dst`.
            RValue::VecPush(vec, val) => {
                let vec_reg = self.operand_reg(vec);
                let val_reg = self.operand_reg(val);
                self.code.push(Instr::VecPush(dst, vec_reg, val_reg));
            }
            RValue::Ref(kind, place) => self.lower_ref(dst, *kind, place),
        }
    }

    /// Lower `&place` / `&mut place` into `dst`. A whole-local borrow yields a
    /// `Ref(addr)` to that local's store cell. Because every borrowed local is boxed
    /// (its register already holds the `Ref`), `&local` is just a register copy —
    /// shared and mutable borrows are represented identically at runtime (the
    /// distinction is enforced earlier, by verification, not by the VM). Borrows of
    /// sub-places (`&x.f`, `&*r`) would need cell addresses this slice does not
    /// compute, so they trap.
    fn lower_ref(&mut self, dst: u32, _kind: BorrowKind, place: &Place) {
        if place.proj.is_empty() {
            // The local is boxed (the pre-pass guarantees this), so its register
            // holds a `Ref` to its cell. Copy it.
            debug_assert!(self.boxed.contains(&place.local.0));
            self.code.push(Instr::Move(dst, place.local.0));
        } else {
            self.code.push(Instr::Trap(
                "codegen: unsupported borrow of a sub-place (only whole-local \
                 `&x` / `&mut x` are supported)"
                    .to_string(),
            ));
        }
    }

    fn lower_terminator(&mut self, term: &Terminator<Lowerable>) {
        match term {
            Terminator::Goto(target) => {
                let instr = self.code.len();
                self.code.push(Instr::Jump(usize::MAX)); // placeholder
                self.fixups.push(Fixup { instr, slot: FixupSlot::Jump, target: *target });
            }
            Terminator::Branch { cond, then_blk, else_blk } => {
                let rc = self.operand_reg(cond);
                let instr = self.code.len();
                self.code.push(Instr::Branch(rc, usize::MAX, usize::MAX));
                self.fixups.push(Fixup {
                    instr,
                    slot: FixupSlot::BranchThen,
                    target: *then_blk,
                });
                self.fixups.push(Fixup {
                    instr,
                    slot: FixupSlot::BranchElse,
                    target: *else_blk,
                });
            }
            Terminator::Match { scrutinee, arms, otherwise } => {
                // Evaluate the scrutinee into a register; the VM reads its tag.
                let src = self.operand_reg(scrutinee);
                let instr = self.code.len();
                // Placeholder table: tags are known now, offsets are back-patched.
                let table: Vec<(u32, usize)> =
                    arms.iter().map(|a| (a.variant, usize::MAX)).collect();
                let otherwise_slot = otherwise.map(|_| usize::MAX);
                self.code.push(Instr::Switch(src, table, otherwise_slot));
                for (i, arm) in arms.iter().enumerate() {
                    self.fixups.push(Fixup {
                        instr,
                        slot: FixupSlot::SwitchArm(i),
                        target: arm.target,
                    });
                }
                if let Some(other) = otherwise {
                    self.fixups.push(Fixup {
                        instr,
                        slot: FixupSlot::SwitchOtherwise,
                        target: *other,
                    });
                }
            }
            Terminator::Return(op) => {
                let r = self.operand_reg(op);
                self.code.push(Instr::Ret(r));
            }
            // Panic aborts the program with a clean runtime error. It has no
            // successors, so we emit a single trapping instruction and stop —
            // execution never falls through past a `Trap` (the VM returns `Err`).
            Terminator::Panic => {
                self.code.push(Instr::Trap("panic".to_string()));
            }
            // Drop is a no-op jump in this slice.
            Terminator::Drop { next, .. } => {
                let instr = self.code.len();
                self.code.push(Instr::Jump(usize::MAX));
                self.fixups.push(Fixup { instr, slot: FixupSlot::Jump, target: *next });
            }
        }
    }

    fn resolve_fixups(&mut self, id_to_slot: &std::collections::HashMap<u32, usize>) {
        for fx in &self.fixups {
            let slot = id_to_slot[&fx.target.0];
            let off = self.block_offsets[slot].expect("target block emitted");
            match (&mut self.code[fx.instr], &fx.slot) {
                (Instr::Jump(t), FixupSlot::Jump) => *t = off,
                (Instr::Branch(_, t, _), FixupSlot::BranchThen) => *t = off,
                (Instr::Branch(_, _, e), FixupSlot::BranchElse) => *e = off,
                (Instr::Switch(_, table, _), FixupSlot::SwitchArm(i)) => table[*i].1 = off,
                (Instr::Switch(_, _, other), FixupSlot::SwitchOtherwise) => *other = Some(off),
                _ => unreachable!("fixup slot/instr mismatch"),
            }
        }
    }
}
