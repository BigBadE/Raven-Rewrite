//! The per-function CFG builder for the rust-analyzer-based front-end.
//!
//! This is the IR-construction substrate — purely a wrapper over `rv_ir`, with
//! no parser dependency. The lowering logic (in `lower.rs`) drives it with
//! `ra_ap_syntax` AST nodes. It mirrors the tree-sitter front-end's builder, so
//! the two produce shape-identical IR while the parser is swapped underneath.

use std::collections::{HashMap, HashSet};

use rv_core::{Sym, Ty};
use rv_ir::{
    Block, BlockId, Const, Function, LocalDecl, LocalId, Operand, Parsed, Stmt, Terminator,
};

use super::types::Types;

/// Where `break`/`continue` jump for one enclosing loop.
#[derive(Clone, Copy)]
pub struct LoopTargets {
    pub continue_to: BlockId,
    pub break_to: BlockId,
}

pub struct FnBuilder<'a> {
    pub types: &'a Types,
    locals: Vec<LocalDecl<Parsed>>,
    blocks: Vec<Block<Parsed>>,
    cur_stmts: Vec<Stmt>,
    cur_id: BlockId,
    next_block: u32,
    diverged: bool,
    /// Source name -> local id (last binding wins: flat-scope shadowing).
    names: HashMap<Sym, LocalId>,
    /// Best-effort: a local's ADT (struct/enum) name.
    local_adt: HashMap<LocalId, Sym>,
    /// Locals known to hold a `Vec<T>` (gates `v.len()` / `v.push(..)`).
    vec_locals: HashSet<LocalId>,
    /// Enclosing loops' jump targets (innermost last).
    loop_targets: Vec<LoopTargets>,
    /// The ADT `Self` denotes inside an `impl` (so `Self`, `Self::new()`,
    /// `Self { .. }` resolve to the implementing type).
    self_ty: Option<Sym>,
    /// Top-level functions produced *during* this function's lowering by closure
    /// conversion: each `|args| body` lambda is lifted to its own `Function` and
    /// parked here, to be appended to the program alongside the function that
    /// created it. Nested closures drain their inner sink into their parent's.
    lifted: Vec<Function<Parsed>>,
}

impl<'a> FnBuilder<'a> {
    pub fn new(types: &'a Types) -> Self {
        FnBuilder {
            types,
            locals: Vec::new(),
            blocks: Vec::new(),
            cur_stmts: Vec::new(),
            cur_id: BlockId(0),
            next_block: 1, // 0 is the entry, already in flight.
            diverged: false,
            names: HashMap::new(),
            local_adt: HashMap::new(),
            vec_locals: HashSet::new(),
            loop_targets: Vec::new(),
            self_ty: None,
            lifted: Vec::new(),
        }
    }

    /// Park a lifted closure function to be appended to the program.
    pub fn push_lifted(&mut self, f: Function<Parsed>) {
        self.lifted.push(f);
    }
    /// Take the lifted closure functions accumulated so far (drains the sink).
    pub fn take_lifted(&mut self) -> Vec<Function<Parsed>> {
        std::mem::take(&mut self.lifted)
    }

    pub fn set_self_ty(&mut self, ty: Sym) {
        self.self_ty = Some(ty);
    }
    pub fn self_ty(&self) -> Option<Sym> {
        self.self_ty
    }

    pub fn into_parts(self) -> (Vec<LocalDecl<Parsed>>, Vec<Block<Parsed>>) {
        (self.locals, self.blocks)
    }

    // ---- locals / names ----------------------------------------------------

    pub fn new_local(&mut self, name: Option<Sym>) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(LocalDecl { name, ty: None });
        id
    }
    pub fn set_decl_ty(&mut self, id: LocalId, ty: Ty) {
        self.locals[id.0 as usize].ty = Some(ty);
    }
    pub fn set_local_adt(&mut self, id: LocalId, adt: Sym) {
        self.local_adt.insert(id, adt);
    }
    pub fn local_adt(&self, id: LocalId) -> Option<Sym> {
        self.local_adt.get(&id).copied()
    }
    pub fn mark_vec(&mut self, id: LocalId) {
        self.vec_locals.insert(id);
    }
    pub fn is_vec(&self, id: LocalId) -> bool {
        self.vec_locals.contains(&id)
    }
    pub fn bind(&mut self, name: Sym, id: LocalId) {
        self.names.insert(name, id);
    }
    pub fn lookup(&self, name: Sym) -> Option<LocalId> {
        self.names.get(&name).copied()
    }

    // ---- blocks ------------------------------------------------------------

    pub fn diverged(&self) -> bool {
        self.diverged
    }
    pub fn cur_id(&self) -> BlockId {
        self.cur_id
    }
    pub fn fresh_block_id(&mut self) -> BlockId {
        let id = BlockId(self.next_block);
        self.next_block += 1;
        id
    }
    pub fn push_stmt(&mut self, s: Stmt) {
        if !self.diverged {
            self.cur_stmts.push(s);
        }
    }
    pub fn set_diverged(&mut self) {
        self.diverged = true;
    }
    /// Close the current block with `term`, then begin building block `next`.
    pub fn finish_block(&mut self, term: Terminator<Parsed>, next: BlockId) {
        let stmts = std::mem::take(&mut self.cur_stmts);
        self.blocks.push(Block { id: self.cur_id, stmts, term });
        self.cur_id = next;
        self.diverged = false;
    }
    /// Begin a new block after a diverging arm already closed the previous one.
    pub fn start_block(&mut self, id: BlockId) {
        debug_assert!(self.cur_stmts.is_empty());
        self.cur_id = id;
        self.diverged = false;
    }
    /// Append a unit return if control falls off the function's end.
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

    // ---- loop targets ------------------------------------------------------

    pub fn push_loop(&mut self, t: LoopTargets) {
        self.loop_targets.push(t);
    }
    pub fn pop_loop(&mut self) {
        self.loop_targets.pop();
    }
    pub fn innermost_loop(&self) -> Option<LoopTargets> {
        self.loop_targets.last().copied()
    }
}
