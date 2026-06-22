//! The per-function CFG builder used by lowering.
//!
//! `FnBuilder` maintains a "current block" plus a growing list of finished
//! blocks and locals. Expressions are flattened into a sequence of `Assign`
//! statements over temporary locals; structured statements compile to branches
//! and gotos between freshly allocated blocks.

use std::collections::HashMap;

use rv_core::{BinOp, Sym, Symbols};
use rv_ir::{
    AggKind, Block, BlockId, BorrowKind, Const, LocalDecl, LocalId, MatchArm as IrMatchArm, Operand,
    Parsed, Place, Proj, RValue, Stmt as IrStmt, Terminator,
};
use rv_syntax::ast::{
    Block as AstBlock, Expr, MatchArm as AstMatchArm, PatBind, Pattern, Stmt as AstStmt,
};

use crate::spec;
use crate::types::Types;

pub struct FnBuilder<'a> {
    locals: Vec<LocalDecl<Parsed>>,
    /// Finished blocks, in creation order.
    blocks: Vec<Block<Parsed>>,
    /// Statements for the block currently under construction.
    cur_stmts: Vec<IrStmt>,
    /// Id of the block currently under construction.
    cur_id: BlockId,
    /// Monotonic source of fresh block ids. Block 0 is the entry.
    next_block: u32,
    /// Once the current block diverges (a `return`), further statements/terminators
    /// in the same syntactic block are dead and dropped.
    diverged: bool,
    /// Source-name -> local id, for resolving variable references / assignments.
    /// Last binding wins (shadowing), which is sufficient for this flat scope model.
    names: HashMap<Sym, LocalId>,
    /// Module-level type registry: struct fields, enum variants, ADT kinds.
    types: &'a Types,
    /// Best-effort tracking of a local's ADT (struct/enum) name, learned from
    /// parameter types and from struct-literal / enum-ctor initializers. Used to
    /// resolve field access (`s.f`) and the variant payloads bound in `match`.
    local_adt: HashMap<LocalId, Sym>,
    /// Top-level functions lifted out of closure literals encountered while lowering
    /// this body (lambda lifting). Drained by the caller into the program's function list.
    lifted: Vec<rv_ir::Function<Parsed>>,
    /// Monotonic counter for fresh lifted-closure names within this body.
    closure_ctr: u32,
}

impl<'a> FnBuilder<'a> {
    pub fn new(types: &'a Types) -> Self {
        FnBuilder {
            locals: Vec::new(),
            blocks: Vec::new(),
            cur_stmts: Vec::new(),
            cur_id: BlockId(0),
            next_block: 1, // 0 is the entry, already "in flight".
            diverged: false,
            names: HashMap::new(),
            types,
            local_adt: HashMap::new(),
            lifted: Vec::new(),
            closure_ctr: 0,
        }
    }

    /// Drain the functions lifted out of closure literals in this body.
    pub fn take_lifted(&mut self) -> Vec<rv_ir::Function<Parsed>> {
        std::mem::take(&mut self.lifted)
    }

    /// Record that local `id` holds a value of ADT type `adt` (best-effort).
    pub fn set_local_adt(&mut self, id: LocalId, adt: Sym) {
        self.local_adt.insert(id, adt);
    }

    /// Map currently-bound variable names to their struct type, for resolving
    /// `v.field` inside an `assert` / loop `invariant` spec. Only struct-typed
    /// locals are recorded (enum field projection has no first-order term form).
    fn var_struct_map(&self) -> HashMap<Sym, Sym> {
        let mut m = HashMap::new();
        for (name, id) in &self.names {
            if let Some(adt) = self.local_adt.get(id) {
                if self.types.struct_info(*adt).is_some() {
                    m.insert(*name, *adt);
                }
            }
        }
        m
    }

    /// Lower a spec `Prop` (`assert` / `invariant`) in the current name scope.
    fn lower_spec_prop(
        &self,
        e: &Expr,
        syms: &mut rv_core::Symbols,
    ) -> Result<rv_core::Prop, String> {
        let var_struct = self.var_struct_map();
        let ctx = spec::SpecCtx { types: self.types, var_struct: &var_struct };
        spec::lower_prop(e, syms, &ctx)
    }

    /// Consume the builder, yielding its locals and blocks.
    pub fn into_parts(self) -> (Vec<LocalDecl<Parsed>>, Vec<Block<Parsed>>) {
        (self.locals, self.blocks)
    }

    // ---- local / block / name management -----------------------------------

    /// Allocate a fresh local with an optional source name (type `()` in Parsed).
    pub fn new_local(&mut self, name: Option<Sym>) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(LocalDecl { name, ty: None });
        id
    }

    /// Record that source name `name` currently refers to local `id`.
    pub fn bind(&mut self, name: Sym, id: LocalId) {
        self.names.insert(name, id);
    }

    /// Reserve a fresh block id (not yet started).
    fn fresh_block_id(&mut self) -> BlockId {
        let id = BlockId(self.next_block);
        self.next_block += 1;
        id
    }

    /// Append a statement to the current block (dropped if it has diverged).
    fn push_stmt(&mut self, s: IrStmt) {
        if !self.diverged {
            self.cur_stmts.push(s);
        }
    }

    /// Close the current block with `term`, then begin building block `next`.
    fn finish_block(&mut self, term: Terminator<Parsed>, next: BlockId) {
        let stmts = std::mem::take(&mut self.cur_stmts);
        self.blocks.push(Block { id: self.cur_id, stmts, term });
        self.cur_id = next;
        self.diverged = false;
    }

    /// If the current (final) block never diverged, terminate it with a unit
    /// return so every path ends in `Return`.
    pub fn finish_with_default_return(&mut self) {
        if !self.diverged {
            let stmts = std::mem::take(&mut self.cur_stmts);
            self.blocks.push(Block {
                id: self.cur_id,
                stmts,
                term: Terminator::Return(Operand::Const(Const::Unit)),
            });
            self.diverged = true;
        }
    }

    /// Close the current block by returning the value in `id` (used for a lifted closure body).
    pub fn return_local(&mut self, id: LocalId) {
        if !self.diverged {
            let stmts = std::mem::take(&mut self.cur_stmts);
            self.blocks.push(Block {
                id: self.cur_id,
                stmts,
                term: Terminator::Return(Operand::Copy(Place::local(id))),
            });
            self.diverged = true;
        }
    }

    // ---- statement lowering ------------------------------------------------

    /// Lower a syntactic block's statements into the CFG.
    pub fn lower_block(&mut self, block: &AstBlock, syms: &mut Symbols) -> Result<(), String> {
        for stmt in &block.stmts {
            // Once a block diverged via `return`, the rest of this syntactic
            // block is unreachable; stop emitting it.
            if self.diverged {
                break;
            }
            self.lower_stmt(stmt, syms)?;
        }
        Ok(())
    }

    fn lower_stmt(&mut self, stmt: &AstStmt, syms: &mut Symbols) -> Result<(), String> {
        match stmt {
            AstStmt::Let { name, init, .. } => {
                let dst = self.new_local(Some(*name));
                self.lower_into_local(dst, init, syms)?;
                // Best-effort: propagate a known ADT type from the initializer so
                // later field access / match on this local can resolve.
                if let Some(adt) = self.adt_of_expr(init) {
                    self.set_local_adt(dst, adt);
                }
                self.bind(*name, dst);
                Ok(())
            }
            AstStmt::Assign { name, value } => {
                let dst = *self
                    .names
                    .get(name)
                    .ok_or_else(|| format!("assignment to unbound variable `{}`", syms.resolve(*name)))?;
                self.lower_into_local(dst, value, syms)
            }
            // `*place = value;` — store through a reference. The target is the
            // place of `place` with a `Proj::Deref` appended; assign the rvalue of
            // `value` directly into it.
            AstStmt::DerefAssign { place, value } => {
                let dst_place = self.lower_place(place, syms)?;
                let rvalue = self.lower_rvalue(value, syms)?;
                self.push_stmt(IrStmt::Assign(dst_place, rvalue));
                Ok(())
            }
            AstStmt::Return(opt) => {
                let operand = match opt {
                    Some(e) => self.lower_operand(e, syms)?,
                    None => Operand::Const(Const::Unit),
                };
                // A return needs no successor; route to a dummy fresh id that is
                // never built (the block list simply won't contain it).
                let dead = self.fresh_block_id();
                self.finish_block(Terminator::Return(operand), dead);
                self.diverged = true;
                Ok(())
            }
            AstStmt::Assert(e) => {
                let prop = self.lower_spec_prop(e, syms)?;
                self.push_stmt(IrStmt::Assert(prop));
                Ok(())
            }
            // `panic;` / `panic(expr);` — evaluate any argument for its side effects,
            // then abort. The abort ends the current block (no successors), so any
            // statements following it on this path are dead.
            AstStmt::Panic(arg) => {
                // Evaluate the optional argument into a throwaway temp purely for
                // its effects (the value is discarded). A `?`-bearing argument can
                // even split blocks here, which `lower_into_local` handles.
                if let Some(e) = arg {
                    let tmp = self.new_local(None);
                    self.lower_into_local(tmp, e, syms)?;
                }
                // Terminate the current block with `Panic`. It has no successor, so
                // route to a dummy fresh id that is never built.
                let dead = self.fresh_block_id();
                self.finish_block(Terminator::Panic, dead);
                self.diverged = true;
                Ok(())
            }
            AstStmt::Expr(e) => {
                // Evaluate for side effects. Pure expressions are simply dropped;
                // calls (the only effectful form) get assigned to a throwaway temp.
                match e {
                    Expr::Call { .. } => {
                        let tmp = self.new_local(None);
                        self.lower_into_local(tmp, e, syms)?;
                    }
                    _ => {
                        // No side effects to preserve; nothing to emit.
                    }
                }
                Ok(())
            }
            AstStmt::If { cond, then_blk, else_blk } => {
                self.lower_if(cond, then_blk, else_blk.as_ref(), syms)
            }
            AstStmt::While { cond, invariants, body } => {
                self.lower_while(cond, invariants, body, syms)
            }
            AstStmt::Match { scrut, arms } => self.lower_match(scrut, arms, syms),
        }
    }

    /// Lower `if cond { then } else { els }` into branch/join blocks.
    fn lower_if(
        &mut self,
        cond: &Expr,
        then_blk: &AstBlock,
        else_blk: Option<&AstBlock>,
        syms: &mut Symbols,
    ) -> Result<(), String> {
        let cond_op = self.lower_operand(cond, syms)?;

        let then_id = self.fresh_block_id();
        let else_id = self.fresh_block_id();
        let join_id = self.fresh_block_id();

        // Close the predecessor with the branch; start the `then` block.
        self.finish_block(
            Terminator::Branch { cond: cond_op, then_blk: then_id, else_blk: else_id },
            then_id,
        );

        // then-arm: lower, then jump to join if it didn't diverge.
        self.lower_block(then_blk, syms)?;
        if !self.diverged {
            self.finish_block(Terminator::Goto(join_id), else_id);
        } else {
            // Begin the else block fresh (the then-arm already closed itself).
            self.start_block(else_id);
        }

        // else-arm (possibly empty): lower, then jump to join.
        if let Some(els) = else_blk {
            self.lower_block(els, syms)?;
        }
        if !self.diverged {
            self.finish_block(Terminator::Goto(join_id), join_id);
        } else {
            self.start_block(join_id);
        }

        Ok(())
    }

    /// Lower `while cond (invariant I;)* { body }` into header/body/exit blocks
    /// with a back-edge. Each `invariant` becomes a `Stmt::Invariant` placed at the
    /// very START of the loop header (before the condition is evaluated), so it is
    /// re-established on every header visit (entry and each back-edge).
    fn lower_while(
        &mut self,
        cond: &Expr,
        invariants: &[Expr],
        body: &AstBlock,
        syms: &mut Symbols,
    ) -> Result<(), String> {
        let header_id = self.fresh_block_id();
        let body_id = self.fresh_block_id();
        let exit_id = self.fresh_block_id();

        // Fall into the header from the predecessor.
        self.finish_block(Terminator::Goto(header_id), header_id);

        // Header: invariants first, as the leading statements of the header block.
        for inv in invariants {
            let prop = self.lower_spec_prop(inv, syms)?;
            self.push_stmt(IrStmt::Invariant(prop));
        }
        // Then evaluate the condition and branch body/exit.
        let cond_op = self.lower_operand(cond, syms)?;
        self.finish_block(
            Terminator::Branch { cond: cond_op, then_blk: body_id, else_blk: exit_id },
            body_id,
        );

        // Body: lower, then loop back to the header (unless it diverged).
        self.lower_block(body, syms)?;
        if !self.diverged {
            self.finish_block(Terminator::Goto(header_id), exit_id);
        } else {
            self.start_block(exit_id);
        }

        Ok(())
    }

    /// Lower `match scrut { Pat => block, ... }`.
    ///
    /// Emits `Terminator::Match { scrutinee, arms, otherwise }` where each
    /// `Enum::Variant(binds) => body` arm targets a fresh block whose FIRST
    /// statements bind the pattern's named field binders (via `Downcast`+`Field`
    /// projections off the scrutinee local), and a `_ => body` arm becomes the
    /// `otherwise` target. Every arm block jumps to a shared join block, in which
    /// lowering continues after the match.
    fn lower_match(
        &mut self,
        scrut: &Expr,
        arms: &[AstMatchArm],
        syms: &mut Symbols,
    ) -> Result<(), String> {
        // The scrutinee must be a *local* (we project off it for field binds). If
        // the expression isn't already a plain local, store it into a fresh one.
        let scrut_local = self.expr_to_local(scrut, syms)?;
        // Resolve the scrutinee's enum (needed to bind variant payload fields).
        let scrut_enum = self.local_adt.get(&scrut_local).copied();

        // Allocate the shared join block all arms fall through to.
        let join_id = self.fresh_block_id();

        // First pass: allocate a target block id per arm and build the terminator.
        let mut ir_arms = Vec::new();
        let mut otherwise = None;
        // Store, per arm, (target block id, the arm) so we can lower bodies after
        // closing the scrutinee block with the Match terminator.
        let mut planned: Vec<(BlockId, &AstMatchArm)> = Vec::new();
        for arm in arms {
            let target = self.fresh_block_id();
            planned.push((target, arm));
            match &arm.pat {
                Pattern::Wildcard => {
                    if otherwise.is_some() {
                        return Err("duplicate `_` arm in match".to_string());
                    }
                    otherwise = Some(target);
                }
                Pattern::Variant { enum_name, variant, .. } => {
                    let info = self.types.enum_info(*enum_name).ok_or_else(|| {
                        format!("unknown enum `{}` in match pattern", syms.resolve(*enum_name))
                    })?;
                    let (vidx, _arity) = *info.variant_index.get(variant).ok_or_else(|| {
                        format!(
                            "unknown variant `{}` of enum `{}`",
                            syms.resolve(*variant),
                            syms.resolve(*enum_name)
                        )
                    })?;
                    ir_arms.push(IrMatchArm { variant: vidx, target });
                }
            }
        }

        // Close the scrutinee block with the Match terminator. The next block we
        // build is the first arm target (or the join, if there are no arms).
        let first_target = planned.first().map(|(id, _)| *id).unwrap_or(join_id);
        self.finish_block(
            Terminator::Match {
                scrutinee: Operand::Copy(Place::local(scrut_local)),
                arms: ir_arms,
                otherwise,
            },
            first_target,
        );

        // Second pass: lower each arm body in its own block.
        for (i, (target, arm)) in planned.iter().enumerate() {
            // We are positioned at `target` (the first arm) or must start it.
            if self.cur_id != *target {
                self.start_block(*target);
            }
            // Bind the pattern's named field binders off the scrutinee local.
            if let Pattern::Variant { enum_name, variant, binds } = &arm.pat {
                self.bind_pattern_fields(scrut_local, scrut_enum, *enum_name, *variant, binds, syms)?;
            }
            // Lower the arm body, then jump to the join (unless it diverged).
            self.lower_block(&arm.body, syms)?;
            // Decide what block to begin next: the following arm's target, or the
            // join after the last arm.
            let next = planned.get(i + 1).map(|(id, _)| *id).unwrap_or(join_id);
            if !self.diverged {
                self.finish_block(Terminator::Goto(join_id), next);
            } else {
                self.start_block(next);
            }
        }

        // Continue lowering after the match in the join block. (If every arm
        // diverged we are already positioned at `join_id` via `start_block`.)
        if self.cur_id != join_id {
            self.start_block(join_id);
        }
        Ok(())
    }

    /// Lower the error-propagation operator `e?`, splitting the current block.
    ///
    /// Evaluates `e` into a scrutinee local `s`, resolves its `Result`/`Option`-like
    /// enum (via `local_adt` tracking), and emits a `Terminator::Match` on `s` with
    /// two arms:
    ///   * SUCCESS arm: bind the payload `v = Copy(s.Downcast(success).Field(0))`,
    ///     then `Goto` a fresh continuation block;
    ///   * FAILURE arm: re-aggregate the failure variant from `s`'s payload (or with
    ///     no payload for `None`) and `Return` it from the enclosing function.
    ///
    /// Lowering then continues in the continuation block, and the `?` expression's
    /// value is the success-bound local `v`, whose id is returned.
    fn lower_try(&mut self, inner: &Expr, syms: &mut Symbols) -> Result<LocalId, String> {
        // Evaluate the operand into a local we can project off of (the scrutinee).
        let s = self.expr_to_local(inner, syms)?;
        // Resolve the scrutinee's enum so we can identify its success/failure pair.
        let enum_name = self.local_adt.get(&s).copied().ok_or_else(|| {
            "cannot resolve the enum type of a `?` operand (its value must be a local \
             of a known `Result`/`Option`-like enum)"
                .to_string()
        })?;
        let shape = self.types.try_shape(enum_name, syms)?;

        // Blocks: the two match-arm targets and the success continuation.
        let success_id = self.fresh_block_id();
        let failure_id = self.fresh_block_id();
        let cont_id = self.fresh_block_id();

        // The local that receives the unwrapped success payload — the value of `e?`.
        let v = self.new_local(None);

        // Close the current block with the Match: success -> success arm, failure ->
        // failure arm. We emit BOTH variants explicitly (no `otherwise`).
        self.finish_block(
            Terminator::Match {
                scrutinee: Operand::Copy(Place::local(s)),
                arms: vec![
                    IrMatchArm { variant: shape.success_idx, target: success_id },
                    IrMatchArm { variant: shape.failure_idx, target: failure_id },
                ],
                otherwise: None,
            },
            success_id,
        );

        // --- success arm: bind the payload into `v`, then jump to the continuation.
        let payload = Place {
            local: s,
            proj: vec![Proj::Downcast(shape.success_idx), Proj::Field(0)],
        };
        self.push_stmt(IrStmt::Assign(
            Place::local(v),
            RValue::Use(Operand::Copy(payload)),
        ));
        // Next block to build is the failure arm.
        self.finish_block(Terminator::Goto(cont_id), failure_id);

        // --- failure arm: rebuild the failure variant from `s` and return it.
        // Re-aggregate `Enum::Failure(<payload>?)`: for `Err(e)` (arity 1) we read
        // back the failure payload from `s`; for `None` (arity 0) there is none.
        let mut fail_ops = Vec::new();
        if shape.failure_arity == 1 {
            let fpayload = Place {
                local: s,
                proj: vec![Proj::Downcast(shape.failure_idx), Proj::Field(0)],
            };
            fail_ops.push(Operand::Copy(fpayload));
        }
        // Materialize the rebuilt failure value into a temp, then return it.
        let fail_local = self.new_local(None);
        self.set_local_adt(fail_local, enum_name);
        self.push_stmt(IrStmt::Assign(
            Place::local(fail_local),
            RValue::Aggregate(AggKind::Variant(enum_name, shape.failure_idx), fail_ops),
        ));
        // Early-return the failure. The block has no real successor; positioning at
        // `cont_id` next means success lowering resumes there.
        self.finish_block(
            Terminator::Return(Operand::Copy(Place::local(fail_local))),
            cont_id,
        );

        // We are now building the continuation block; `v` holds the success value.
        Ok(v)
    }

    /// Emit the `Assign`s that bind a variant pattern's named field binders.
    ///
    /// For binder `i` named `x`: `x_local = Copy(scrut.Downcast(V).Field(i))`. `_`
    /// binders are skipped. Requires the scrutinee's enum to be known (best-effort
    /// type tracking); reports an error if it could not be resolved.
    fn bind_pattern_fields(
        &mut self,
        scrut_local: LocalId,
        scrut_enum: Option<Sym>,
        enum_name: Sym,
        variant: Sym,
        binds: &[PatBind],
        syms: &mut Symbols,
    ) -> Result<(), String> {
        if binds.is_empty() {
            return Ok(());
        }
        // The scrutinee's enum must match the pattern's enum.
        if let Some(se) = scrut_enum {
            if se != enum_name {
                return Err(format!(
                    "match scrutinee has type `{}` but pattern names enum `{}`",
                    syms.resolve(se),
                    syms.resolve(enum_name)
                ));
            }
        }
        let info = self.types.enum_info(enum_name).ok_or_else(|| {
            format!("unknown enum `{}` in match pattern", syms.resolve(enum_name))
        })?;
        let (vidx, arity) = *info.variant_index.get(&variant).ok_or_else(|| {
            format!(
                "unknown variant `{}` of enum `{}`",
                syms.resolve(variant),
                syms.resolve(enum_name)
            )
        })?;
        if binds.len() as u32 != arity {
            return Err(format!(
                "variant `{}` binds {} fields but pattern has {}",
                syms.resolve(variant),
                arity,
                binds.len()
            ));
        }
        for (i, b) in binds.iter().enumerate() {
            let PatBind::Name(name) = b else { continue }; // skip `_`
            let dst = self.new_local(Some(*name));
            let src = Place {
                local: scrut_local,
                proj: vec![Proj::Downcast(vidx), Proj::Field(i as u32)],
            };
            self.push_stmt(IrStmt::Assign(
                Place::local(dst),
                RValue::Use(Operand::Copy(src)),
            ));
            self.bind(*name, dst);
        }
        Ok(())
    }

    /// Reduce an expression to a *local* id, materializing it into a fresh local
    /// if it isn't already a bare variable. Used for `match` scrutinees (which must
    /// be a local so field-binders can project off them).
    fn expr_to_local(&mut self, e: &Expr, syms: &mut Symbols) -> Result<LocalId, String> {
        if let Expr::Var(s) = e {
            if let Some(id) = self.names.get(s) {
                return Ok(*id);
            }
        }
        // Otherwise evaluate into a fresh local, carrying any known ADT type.
        let tmp = self.new_local(None);
        self.lower_into_local(tmp, e, syms)?;
        if let Some(adt) = self.adt_of_expr(e) {
            self.set_local_adt(tmp, adt);
        }
        Ok(tmp)
    }

    /// Begin building a new block with the given id (used after a diverging arm
    /// has already closed the previous block, so there is nothing to finish).
    fn start_block(&mut self, id: BlockId) {
        debug_assert!(self.cur_stmts.is_empty());
        self.cur_id = id;
        self.diverged = false;
    }

    // ---- expression lowering -----------------------------------------------

    /// Lower expression `e` and assign its value into local `dst`.
    fn lower_into_local(
        &mut self,
        dst: LocalId,
        e: &Expr,
        syms: &mut Symbols,
    ) -> Result<(), String> {
        let rvalue = self.lower_rvalue(e, syms)?;
        self.push_stmt(IrStmt::Assign(Place::local(dst), rvalue));
        Ok(())
    }

    /// Lower an expression to an [`RValue`], flattening nested subexpressions into
    /// temporaries as needed. Compound forms (binary/unary/call) map directly to
    /// the corresponding `RValue`; everything else becomes `RValue::Use`.
    fn lower_rvalue(&mut self, e: &Expr, syms: &mut Symbols) -> Result<RValue, String> {
        match e {
            Expr::Bin(op, a, b) => {
                let oa = self.lower_operand(a, syms)?;
                let ob = self.lower_operand(b, syms)?;
                Ok(RValue::Bin(*op, oa, ob))
            }
            Expr::Un(op, a) => {
                let oa = self.lower_operand(a, syms)?;
                Ok(RValue::Un(*op, oa))
            }
            Expr::Call { func, args } => {
                // If the callee name is a bound LOCAL, it holds a closure value: this is an
                // indirect call (`f(x)` where `let f = |..| ..`), lowered to `CallClosure`.
                if let Some(&local) = self.names.get(func) {
                    let mut ops = Vec::with_capacity(args.len());
                    for arg in args {
                        ops.push(self.lower_operand(arg, syms)?);
                    }
                    return Ok(RValue::CallClosure(Operand::Copy(Place::local(local)), ops));
                }
                // Wrapping intrinsics `wrapping_add(a, b)` etc. opt out of the
                // checked-overflow obligation (lower to `RValue::WrappingBin`).
                if let Some(op) = wrapping_builtin(syms.resolve(*func)) {
                    if args.len() != 2 {
                        return Err(format!("`{}` takes exactly two arguments", syms.resolve(*func)));
                    }
                    let a = self.lower_operand(&args[0], syms)?;
                    let b = self.lower_operand(&args[1], syms)?;
                    return Ok(RValue::WrappingBin(op, a, b));
                }
                let mut ops = Vec::with_capacity(args.len());
                for arg in args {
                    ops.push(self.lower_operand(arg, syms)?);
                }
                Ok(RValue::Call(*func, ops))
            }
            // `recv.method(args)` desugars to a resolved call on the mangled
            // top-level function, with `recv` passed as the first argument.
            Expr::MethodCall { recv, method, args } => {
                self.lower_method_call(recv, *method, args, syms)
            }
            Expr::StructLit { name, fields } => self.lower_struct_lit(*name, fields, syms),
            Expr::EnumCtor { enum_name, variant, args } => {
                self.lower_enum_ctor(*enum_name, *variant, args, syms)
            }
            Expr::Field { .. } | Expr::Deref(_) => {
                // Field access / dereference are places; read through a `Use` of
                // that place. For `*e`, this composes `place_of(e)` + `Proj::Deref`.
                let place = self.lower_place(e, syms)?;
                Ok(RValue::Use(Operand::Copy(place)))
            }
            // `e?`: lower the try (splitting the current block), then use the
            // success-bound local as this expression's value.
            Expr::Try(inner) => {
                let v = self.lower_try(inner, syms)?;
                Ok(RValue::Use(Operand::Copy(Place::local(v))))
            }
            // `&place` / `&mut place`: take a reference to the operand's place. The
            // operand must be a place; `lower_place` materializes a fresh local for
            // any non-place expression and borrows that local instead.
            Expr::Ref { mutable, expr } => {
                let place = self.lower_place(expr, syms)?;
                let kind = if *mutable { BorrowKind::Mut } else { BorrowKind::Shared };
                Ok(RValue::Ref(kind, place))
            }
            // A closure literal `|params| body`: capture its free variables, lift the body to a
            // fresh top-level function (params = captures ++ closure params), and build a
            // `Closure` value carrying the captured operands.
            Expr::Lambda { params, body } => self.lower_lambda(params, body, syms),
            // Atoms / parenthesized values.
            _ => Ok(RValue::Use(self.lower_operand(e, syms)?)),
        }
    }

    /// Lower a closure literal by lambda-lifting. Free variables of the body (those not bound by
    /// the closure's own parameters) become leading parameters of a generated top-level function
    /// and are captured by value at the closure site.
    fn lower_lambda(
        &mut self,
        params: &[Sym],
        body: &Expr,
        syms: &mut Symbols,
    ) -> Result<RValue, String> {
        // Free variables of the body, minus the closure's parameters, that are bound as locals
        // in the enclosing scope (the values to capture), in deterministic order.
        let mut bound: std::collections::HashSet<Sym> = params.iter().copied().collect();
        let mut frees: Vec<Sym> = Vec::new();
        free_vars(body, &mut bound, &mut frees);
        let captures: Vec<Sym> =
            frees.into_iter().filter(|s| self.names.contains_key(s)).collect();

        // A fresh, unmangleable name for the lifted function.
        let name = syms.intern(&format!("__closure_{}", self.closure_ctr));
        self.closure_ctr += 1;

        // Build the lifted function in its own builder: locals = captures ++ params, body
        // lowered to a returned value.
        let mut b = FnBuilder::new(self.types);
        let mut fparams = Vec::with_capacity(captures.len() + params.len());
        for s in captures.iter().chain(params.iter()) {
            let id = b.new_local(Some(*s));
            b.bind(*s, id);
            fparams.push(id);
        }
        let ret_local = b.expr_to_local(body, syms)?;
        b.return_local(ret_local);
        let nested = b.take_lifted(); // closures nested inside this one
        let (locals, blocks) = b.into_parts();
        self.lifted.extend(nested);
        self.lifted.push(rv_ir::Function {
            name,
            type_params: Vec::new(),
            params: fparams,
            ret: None,
            pre: rv_core::Prop::True,
            post: rv_core::Prop::True,
            locals,
            blocks,
            entry: BlockId(0),
        });

        // The capture operands, read from the enclosing scope.
        let cap_ops: Vec<Operand> = captures
            .iter()
            .map(|s| Operand::Copy(Place::local(self.names[s])))
            .collect();
        Ok(RValue::Closure(name, cap_ops))
    }

    /// Lower a struct literal `S { f: e, ... }`: evaluate each field expression to
    /// an operand, reorder them into the struct's DECLARATION order, and build an
    /// `Aggregate(Struct(s), operands)`.
    fn lower_struct_lit(
        &mut self,
        name: Sym,
        fields: &[(Sym, Expr)],
        syms: &mut Symbols,
    ) -> Result<RValue, String> {
        let info = self
            .types
            .struct_info(name)
            .ok_or_else(|| format!("unknown struct `{}`", syms.resolve(name)))?;
        let n = info.fields.len();
        // Snapshot the field-name -> index map so we don't hold a borrow of `self`
        // while lowering the field expressions.
        let field_index = info.field_index.clone();

        // Slots in declaration order; each must be filled exactly once.
        let mut slots: Vec<Option<Operand>> = (0..n).map(|_| None).collect();
        for (fname, fexpr) in fields {
            let idx = *field_index.get(fname).ok_or_else(|| {
                format!(
                    "struct `{}` has no field `{}`",
                    syms.resolve(name),
                    syms.resolve(*fname)
                )
            })? as usize;
            if slots[idx].is_some() {
                return Err(format!(
                    "field `{}` set twice in `{}` literal",
                    syms.resolve(*fname),
                    syms.resolve(name)
                ));
            }
            slots[idx] = Some(self.lower_operand(fexpr, syms)?);
        }
        // Every field must be provided.
        let mut ops = Vec::with_capacity(n);
        for (i, slot) in slots.into_iter().enumerate() {
            match slot {
                Some(op) => ops.push(op),
                None => {
                    let missing = self.types.struct_info(name).unwrap().fields[i];
                    return Err(format!(
                        "missing field `{}` in `{}` literal",
                        syms.resolve(missing),
                        syms.resolve(name)
                    ));
                }
            }
        }
        Ok(RValue::Aggregate(AggKind::Struct(name), ops))
    }

    /// Lower an enum constructor `E::V(args)` (or unit `E::V`) into an
    /// `Aggregate(Variant(e, v_index), arg_operands)`.
    fn lower_enum_ctor(
        &mut self,
        enum_name: Sym,
        variant: Sym,
        args: &[Expr],
        syms: &mut Symbols,
    ) -> Result<RValue, String> {
        let info = self
            .types
            .enum_info(enum_name)
            .ok_or_else(|| format!("unknown enum `{}`", syms.resolve(enum_name)))?;
        let (vidx, arity) = *info.variant_index.get(&variant).ok_or_else(|| {
            format!(
                "enum `{}` has no variant `{}`",
                syms.resolve(enum_name),
                syms.resolve(variant)
            )
        })?;
        if args.len() as u32 != arity {
            return Err(format!(
                "variant `{}` expects {} field(s), got {}",
                syms.resolve(variant),
                arity,
                args.len()
            ));
        }
        let mut ops = Vec::with_capacity(args.len());
        for a in args {
            ops.push(self.lower_operand(a, syms)?);
        }
        Ok(RValue::Aggregate(AggKind::Variant(enum_name, vidx), ops))
    }

    /// Lower a method call `recv.method(args)`.
    ///
    /// Resolves the receiver's ADT type (via best-effort `local_adt` tracking),
    /// looks up `(adt, method)` in the module's method-resolution table to get the
    /// mangled function name, and emits `Call(mangled, [recv, args...])`. Errors
    /// clearly if the receiver's type is unknown or no matching impl exists.
    fn lower_method_call(
        &mut self,
        recv: &Expr,
        method: Sym,
        args: &[Expr],
        syms: &mut Symbols,
    ) -> Result<RValue, String> {
        // Determine the receiver's ADT type. Restrict receivers to user ADTs.
        let adt = self.adt_of_expr(recv).ok_or_else(|| {
            format!(
                "cannot resolve the receiver type of method call `.{}(..)` \
                 (method receivers must be locals of a known struct/enum type)",
                syms.resolve(method)
            )
        })?;
        let mangled = self.types.method(adt, method).ok_or_else(|| {
            format!(
                "no method `{}` found for type `{}`",
                syms.resolve(method),
                syms.resolve(adt)
            )
        })?;
        // The receiver becomes the first argument, then the explicit arguments.
        let mut ops = Vec::with_capacity(args.len() + 1);
        ops.push(self.lower_operand(recv, syms)?);
        for arg in args {
            ops.push(self.lower_operand(arg, syms)?);
        }
        Ok(RValue::Call(mangled, ops))
    }

    /// Lower an expression that denotes a *place* (currently: a variable, or a
    /// chain of struct field accesses rooted at one). Appends `Proj::Field`s.
    fn lower_place(&mut self, e: &Expr, syms: &mut Symbols) -> Result<Place, String> {
        match e {
            Expr::Var(s) => {
                let id = *self.names.get(s).ok_or_else(|| {
                    format!("use of unbound variable `{}`", syms.resolve(*s))
                })?;
                Ok(Place::local(id))
            }
            Expr::Field { base, field } => {
                // Resolve the base place and its struct type, then append Field(i).
                let base_struct = self.adt_of_expr(base).ok_or_else(|| {
                    "cannot resolve the struct type of a field-access base".to_string()
                })?;
                let info = self.types.struct_info(base_struct).ok_or_else(|| {
                    format!("`{}` is not a struct type", syms.resolve(base_struct))
                })?;
                let idx = *info.field_index.get(field).ok_or_else(|| {
                    format!(
                        "struct `{}` has no field `{}`",
                        syms.resolve(base_struct),
                        syms.resolve(*field)
                    )
                })?;
                let mut place = self.lower_place(base, syms)?;
                place.proj.push(Proj::Field(idx));
                Ok(place)
            }
            // `*inner` is a place: the place of `inner` (the reference) with a
            // `Proj::Deref` appended. Field/deref chains compose in source order.
            Expr::Deref(inner) => {
                let mut place = self.lower_place(inner, syms)?;
                place.proj.push(Proj::Deref);
                Ok(place)
            }
            // Any other expression is not a place; materialize it into a local
            // first and use that local as the (projection-free) place.
            _ => {
                let tmp = self.new_local(None);
                self.lower_into_local(tmp, e, syms)?;
                if let Some(adt) = self.adt_of_expr(e) {
                    self.set_local_adt(tmp, adt);
                }
                Ok(Place::local(tmp))
            }
        }
    }

    /// Best-effort: the ADT (struct/enum) name an expression evaluates to, if we
    /// can determine it statically. Used to track local types and resolve field
    /// access. Returns `None` when unknown (lowering then errors only if the type
    /// is actually needed, e.g. for a field access).
    fn adt_of_expr(&self, e: &Expr) -> Option<Sym> {
        match e {
            Expr::StructLit { name, .. } => Some(*name),
            Expr::EnumCtor { enum_name, .. } => Some(*enum_name),
            Expr::Var(s) => self.names.get(s).and_then(|id| self.local_adt.get(id)).copied(),
            // A call's result ADT comes from the callee's recorded return type.
            Expr::Call { func, .. } => self.types.fn_ret(*func),
            // A method call's result ADT: resolve the receiver's ADT, find the
            // mangled method, then look up its recorded return ADT.
            Expr::MethodCall { recv, method, .. } => {
                let recv_adt = self.adt_of_expr(recv)?;
                let mangled = self.types.method(recv_adt, *method)?;
                self.types.fn_ret(mangled)
            }
            Expr::Field { base, field } => {
                // The field's declared type, if it is itself an ADT.
                let base_struct = self.adt_of_expr(base)?;
                let info = self.types.struct_info(base_struct)?;
                let idx = *info.field_index.get(field)? as usize;
                // Re-read the declared field type from the embedded TypeDef.
                self.types.defs.iter().find_map(|d| match d {
                    rv_ir::TypeDef::Struct { name, fields, .. } if *name == base_struct => {
                        match &fields[idx].ty {
                            rv_core::Ty::Adt(a) => Some(*a),
                            _ => None,
                        }
                    }
                    _ => None,
                })
            }
            // NOTE: `Expr::Try` is intentionally not resolved here. Determining the
            // success payload's ADT would require the symbol table (to name the
            // success variant), which `adt_of_expr` does not hold. Chaining a place
            // operation directly off a `?` (e.g. `e?.field`) is therefore out of
            // scope; bind the result to a `let` first if needed.
            _ => None,
        }
    }

    /// Lower an expression to an [`Operand`]. Atoms produce a constant or a copy
    /// of a local; compound expressions are first evaluated into a fresh temp.
    fn lower_operand(&mut self, e: &Expr, syms: &mut Symbols) -> Result<Operand, String> {
        match e {
            Expr::Int(n) => Ok(Operand::Const(Const::Int(*n))),
            Expr::Float(f) => Ok(Operand::Const(Const::Float(*f))),
            Expr::Str(s) => Ok(Operand::Const(Const::Str(s.clone()))),
            Expr::Bool(b) => Ok(Operand::Const(Const::Bool(*b))),
            Expr::Unit => Ok(Operand::Const(Const::Unit)),
            Expr::Var(s) => {
                let id = *self
                    .names
                    .get(s)
                    .ok_or_else(|| format!("use of unbound variable `{}`", syms.resolve(*s)))?;
                Ok(Operand::Copy(Place::local(id)))
            }
            // Field access and dereference are themselves places: copy directly
            // (no temp needed). `*e` reads through the reference's place.
            Expr::Field { .. } | Expr::Deref(_) => {
                let place = self.lower_place(e, syms)?;
                Ok(Operand::Copy(place))
            }
            // Compound: evaluate into a temp, then copy it out. For struct/enum
            // aggregates, also record the temp's ADT type so it can be matched on
            // or have its fields accessed downstream.
            // `e?` evaluates to its success-bound local directly; copy that out
            // without an extra intermediate temp.
            Expr::Try(inner) => {
                let v = self.lower_try(inner, syms)?;
                Ok(Operand::Copy(Place::local(v)))
            }
            Expr::Bin(..)
            | Expr::Un(..)
            | Expr::Call { .. }
            | Expr::MethodCall { .. }
            | Expr::StructLit { .. }
            | Expr::EnumCtor { .. }
            | Expr::Lambda { .. }
            | Expr::Ref { .. } => {
                let tmp = self.new_local(None);
                let rvalue = self.lower_rvalue(e, syms)?;
                self.push_stmt(IrStmt::Assign(Place::local(tmp), rvalue));
                if let Some(adt) = self.adt_of_expr(e) {
                    self.set_local_adt(tmp, adt);
                }
                Ok(Operand::Copy(Place::local(tmp)))
            }
            // Proof-fragment expression forms never reach the executable lowering
            // (proof declarations route to the kernel).
            Expr::MatchExpr { .. }
            | Expr::Fun { .. }
            | Expr::Forall { .. }
            | Expr::LetIn { .. }
            | Expr::Arrow(..)
            | Expr::Apply { .. }
            | Expr::TypeUniv(_)
            | Expr::Prop
            | Expr::Hole
            | Expr::Rewrite { .. }
            | Expr::Decide
            | Expr::ByCases { .. } => {
                Err("proof-fragment expression cannot be lowered to executable IR".into())
            }
        }
    }
}

/// Map a wrapping-arithmetic builtin name to its `BinOp`. These free calls
/// (`wrapping_add(a, b)`, etc.) lower to `RValue::WrappingBin`, opting out of the
/// checked-overflow obligation.
fn wrapping_builtin(name: &str) -> Option<BinOp> {
    Some(match name {
        "wrapping_add" => BinOp::Add,
        "wrapping_sub" => BinOp::Sub,
        "wrapping_mul" => BinOp::Mul,
        "wrapping_div" => BinOp::Div,
        "wrapping_rem" => BinOp::Mod,
        _ => return None,
    })
}

/// Collect the free variables of `e` (those used but not in `bound`), in first-use order,
/// without duplicates. `bound` is updated in place when descending under a nested closure's
/// parameters. Used by closure lambda-lifting to decide what to capture.
fn free_vars(e: &Expr, bound: &mut std::collections::HashSet<rv_core::Sym>, out: &mut Vec<rv_core::Sym>) {
    match e {
        Expr::Var(s) => {
            if !bound.contains(s) && !out.contains(s) {
                out.push(*s);
            }
        }
        Expr::Int(_) | Expr::Float(_) | Expr::Str(_) | Expr::Bool(_) | Expr::Unit => {}
        Expr::Call { args, .. } | Expr::EnumCtor { args, .. } => {
            for a in args {
                free_vars(a, bound, out);
            }
        }
        Expr::Bin(_, a, b) => {
            free_vars(a, bound, out);
            free_vars(b, bound, out);
        }
        Expr::Un(_, a) | Expr::Field { base: a, .. } | Expr::Deref(a) | Expr::Try(a)
        | Expr::Ref { expr: a, .. } => free_vars(a, bound, out),
        Expr::MethodCall { recv, args, .. } => {
            free_vars(recv, bound, out);
            for a in args {
                free_vars(a, bound, out);
            }
        }
        Expr::StructLit { fields, .. } => {
            for (_, fe) in fields {
                free_vars(fe, bound, out);
            }
        }
        Expr::Lambda { params, body } => {
            // A nested closure binds its own parameters; collect frees of the body under them,
            // then remove the inner params (they are not free in the outer scope).
            let added: Vec<rv_core::Sym> = params.iter().filter(|p| bound.insert(**p)).copied().collect();
            free_vars(body, bound, out);
            for p in added {
                bound.remove(&p);
            }
        }
        // Proof-fragment expression forms never appear in executable closure bodies.
        _ => {}
    }
}
