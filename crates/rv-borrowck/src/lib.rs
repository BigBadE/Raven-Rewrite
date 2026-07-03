//! # `rv-borrowck` — a first borrow / ownership checker over `IR<Lowerable>`
//!
//! This crate performs an *intraprocedural*, CFG-aware ownership and borrow
//! analysis over each function's typed control-flow graph. The bookkeeping is
//! done directly in the [`rv_borrow`] algebra — the same substrate the kernel's
//! grade discipline is built on — so every judgement here is an instance of an
//! algebraic law rather than an ad-hoc flag:
//!
//! * **Move tracking** is usage accounting in the QTT [`rv_borrow::UsageSemiring`].
//!   Each non-`Copy` local carries a grade ([`rv_borrow::Mult`]): `Zero` while
//!   live-and-unconsumed, bumped by `⊕ One` at every consuming use. The move
//!   discipline is *affine* — `use of moved value` is exactly the failure of
//!   [`rv_borrow::affine_ok`] on the local's grade.
//! * **Borrow conflicts** are validity of composition in the fractional-permission
//!   PCM ([`rv_borrow::FracPerm`]). Each local tracks the permission currently
//!   *lent out* to active borrows. Creating a borrow composes the permission it
//!   requires ([`rv_borrow::BorrowKind::required_perm`]) into the lent total; the
//!   borrow is legal iff the composition stays valid (`≤ 1`). A `&mut` requires
//!   the full permission, so it composes validly only into an un-lent local; a
//!   `&` takes a strictly-halving fraction (½, ¼, …), so any number of shared
//!   borrows stay `< 1` but exclude `&mut`. Moving or assigning requires that
//!   nothing is lent (the owner must hold the whole permission).
//!
//! ## What it checks
//!
//! 1. **Move / use-after-move.** A *by-value* use of a non-`Copy` local consumes
//!    ("moves") it. After a move the local is dead until reassigned; touching it
//!    again is a `use of moved value` error. By-value use means
//!    `Operand::Copy(Place { local, proj: [] })` of a non-`Copy` type appearing
//!    in a *consuming position*: a `Call` argument, the operand of a `Use` RHS
//!    whose destination is a different local, an `Aggregate` field, a `Bin`/`Un`
//!    operand, a `Branch`/`Match` scrutinee, or a `Return`. Reassigning the local
//!    (an `Assign` whose place is that bare local) revives it.
//!
//! 2. **Borrow conflicts.** `RValue::Ref(kind, place)` borrows the *root local*
//!    of `place`. We track, per local, the set of currently-active borrows. The
//!    classic exclusion rules are enforced:
//!      * creating a `&mut` borrow of a local that already has *any* active borrow,
//!      * creating *any* borrow of a local that already has an active `&mut` borrow,
//!      * moving or assigning a local while it is borrowed.
//!
//! 3. **CFG awareness.** Each function is analysed by a forward walk over its
//!    blocks starting from `entry`, recursing into successors. A visited-set
//!    terminates the walk on loops/back-edges (mirroring `rv-infer`).
//!
//! ## Move-state across the CFG (precision)
//!
//! Move state is **path-sensitive within a single forward pass**: we carry a
//! per-local moved/borrowed environment down each branch and clone it at splits,
//! so a value moved in one arm is not reported as moved in a sibling arm. At a
//! back-edge (a block already visited on this path) we simply stop, exactly like
//! `rv-infer`'s loop handling — so we do *not* re-examine loop bodies under the
//! "second iteration" environment. This is sound for straight-line and branching
//! code and for reporting first-iteration moves; it can *miss* a use-after-move
//! that only manifests on a second loop iteration (under-reporting, never a false
//! positive). Documented limitation, acceptable for a first pass.
//!
//! ## Borrow-lifetime heuristic (precision)
//!
//! Borrows are **block-scoped**: a borrow created by `Ref` in a block is active
//! for the remainder of that block (so it can conflict with later statements /
//! the terminator in the same block) and is then *released at the end of the
//! block*. We do **not** propagate active borrows across block boundaries.
//!
//! Rationale: this is the simplest lifetime that (a) catches the intended
//! conflicts — two `&mut` of the same local in one straight-line block, a `&mut`
//! while a `&` is live, a move while borrowed — and (b) provably never fires a
//! false positive on borrow-free code (the existing valid example programs use no
//! `&` at all, so every local's borrow set stays empty throughout). It is
//! deliberately conservative *downward*: a borrow whose reference genuinely
//! escapes its creating block is under-checked rather than over-reported. A real
//! NLL implementation would compute liveness of the reference local and end the
//! borrow at its last use; that is future work.
//!
//! ## Not handled (honest scope)
//!
//! * No liveness-based borrow ends (block-scoped approximation, see above).
//! * No reborrow / two-phase borrow reasoning; a `&place` through a `Deref` still
//!   attributes to the *root* local conservatively.
//! * No cross-block borrow propagation, so borrows held across a `Goto`/`Branch`
//!   are not enforced past the split.
//! * No interprocedural ownership (call effects on arguments beyond "moved").
//! * `Drop`'s strategy field is ignored; we treat `Drop { place, .. }` as not
//!   moving (it consumes a value already accounted for by ownership).

#![forbid(unsafe_code)]

use std::collections::{HashMap, HashSet};

use rv_borrow::{affine_ok, FracPerm, Mult, Perm, UsageSemiring};
use rv_core::{Symbols, Ty};
use rv_logic::{Grades, ResourceAlgebra};
use rv_ir::{
    BlockId, BorrowKind, Function, Lowerable, LocalId, Operand, Place, Program, RValue, Stmt,
    Terminator,
};

/// A single borrow/ownership violation. `func` is the (resolved) function name;
/// `message` is a human-readable description (mirrors Rust's phrasing where it
/// helps: `use of moved value \`x\``, `cannot move \`x\` while borrowed`, …).
#[derive(Debug, Clone)]
pub struct BorrowError {
    pub func: String,
    pub message: String,
}

/// Check every function in `prog`; return all borrow/ownership violations found.
/// An empty vector means the program passed the (first-pass) borrow checker.
pub fn check(prog: &Program<Lowerable>, syms: &Symbols) -> Vec<BorrowError> {
    let mut errors = Vec::new();
    for func in &prog.funcs {
        let fname = syms.resolve(func.name).to_string();
        let mut fc = FuncChecker::new(func, fname, syms);
        fc.run();
        errors.append(&mut fc.errors);
    }
    errors
}

// ===========================================================================
// Copy-vs-move classification.
// ===========================================================================

/// Is `ty` a *Copy* type — one that is duplicated (not moved) on a by-value use?
///
/// Per the spec: `Int`, `Bool`, `Unit`, and shared references `&T` are Copy.
/// Everything else of interest — `Adt(_)` and `&mut T` — is non-Copy and MOVES
/// when used by value. (`Tuple`/`Fn`/`Never` are not produced by the current
/// front-end for value locals; we treat them conservatively as non-Copy so a
/// move is tracked rather than silently duplicated, which can only ever *add* a
/// sound error, never hide one. They do not occur in the test/example corpus.)
fn is_copy(ty: &Ty) -> bool {
    match ty {
        // `Float` is a scalar (Copy); `Str` owns a heap buffer, so it MOVES (non-Copy).
        Ty::Int | Ty::IntN(_) | Ty::Float | Ty::Bool | Ty::Unit => true,
        Ty::Str => false,
        // `&T` shared refs are freely copyable; `&mut T` is not.
        Ty::Ref { mutable, .. } => !mutable,
        // Non-Copy: ADTs move by value.
        Ty::Adt(_) => false,
        // Conservatively non-Copy (see doc comment). A generic `Ty::Param` is
        // opaque — assume non-Copy so moves are tracked (can only add a sound
        // error, never hide one).
        Ty::Tuple(_) | Ty::Array(_, _) | Ty::Vec(_) | Ty::Fn(_, _) | Ty::Never | Ty::Param(_) => false,
    }
}

// ===========================================================================
// Per-function analysis.
// ===========================================================================

/// Algebraic ownership state of one local on one CFG path.
#[derive(Clone)]
struct LocalState {
    /// Consumption grade in the [`UsageSemiring`]: `Zero` = live and unconsumed,
    /// `One` = moved out exactly once. The affine discipline (`grade ≤ One`)
    /// is the move rule; a grade of `Many` is the use-after-move state.
    usage: Mult,
    /// The permission currently *lent out* to active borrows, as an element of
    /// the [`FracPerm`] PCM. `Empty` = un-borrowed; `1` = a live `&mut`;
    /// a fraction in `(0, 1)` = one or more live `&`. The owner may move or
    /// reassign only while this is `Empty` (it holds the whole permission).
    lent: Perm,
    /// The fraction the *next* shared borrow will take: starts at ½ and halves
    /// on every `&`, so shared borrows always compose validly (`Σ < 1`) among
    /// themselves while any of them excludes the full permission.
    next_share: Perm,
}

impl Default for LocalState {
    fn default() -> Self {
        LocalState {
            usage: UsageSemiring::zero(),
            lent: FracPerm::unit(),
            next_share: Perm::half_perm(),
        }
    }
}

/// Per-local ownership/borrow state threaded along a CFG path. Cloned at branch
/// splits so each path reasons independently.
#[derive(Clone, Default)]
struct Env {
    locals: HashMap<LocalId, LocalState>,
}

impl Env {
    fn state(&mut self, local: LocalId) -> &mut LocalState {
        self.locals.entry(local).or_default()
    }

    /// Has `local` been moved out (grade ≥ `One`) on this path?
    fn is_moved(&self, local: LocalId) -> bool {
        self.locals
            .get(&local)
            .is_some_and(|st| UsageSemiring::leq(&Mult::One, &st.usage))
    }

    /// Does `local` currently have any active borrow at all — i.e. is any part
    /// of its permission lent out?
    fn has_any_borrow(&self, local: LocalId) -> bool {
        self.locals.get(&local).is_some_and(|st| st.lent.is_real())
    }

    /// Try to lend `required` out of `local`'s permission. Succeeds iff the
    /// composition of the already-lent permission with `required` stays valid
    /// (`≤ 1`) in the [`FracPerm`] algebra; on success the lent total is updated.
    fn try_lend(&mut self, local: LocalId, required: &Perm) -> bool {
        let st = self.state(local);
        match FracPerm::compose(&st.lent, required) {
            Some(sum) if FracPerm::valid(&sum) => {
                st.lent = sum;
                true
            }
            // Composition undefined (overflow) or over-owned (> 1): reject.
            _ => false,
        }
    }

    /// Record a consuming use of `local`: bump its grade by `⊕ One`.
    fn consume(&mut self, local: LocalId) {
        let st = self.state(local);
        st.usage = UsageSemiring::add(&st.usage, &UsageSemiring::one());
        debug_assert!(
            !affine_ok(&st.usage) || st.usage == Mult::One,
            "a single consume from Zero lands on One"
        );
    }

    /// Reassignment: the local owns a fresh value, so its grade resets to `Zero`.
    fn revive(&mut self, local: LocalId) {
        self.state(local).usage = UsageSemiring::zero();
    }

    /// End-of-block release: every lent permission returns to its owner (the
    /// block-scoped borrow-lifetime heuristic). Usage grades persist — moves
    /// outlive blocks.
    fn release_borrows(&mut self) {
        for st in self.locals.values_mut() {
            st.lent = FracPerm::unit();
            st.next_share = Perm::half_perm();
        }
    }
}

/// Map the IR's surface borrow kind onto the algebra's [`rv_borrow::BorrowKind`],
/// which knows what permission each kind requires.
fn algebra_kind(kind: BorrowKind) -> rv_borrow::BorrowKind {
    match kind {
        BorrowKind::Shared => rv_borrow::BorrowKind::Shared,
        BorrowKind::Mut => rv_borrow::BorrowKind::Mut,
    }
}

struct FuncChecker<'a> {
    f: &'a Function<Lowerable>,
    fname: String,
    syms: &'a Symbols,
    errors: Vec<BorrowError>,
    /// Blocks already visited on the *current* walk; terminates loops/back-edges.
    visited: HashSet<BlockId>,
}

impl<'a> FuncChecker<'a> {
    fn new(f: &'a Function<Lowerable>, fname: String, syms: &'a Symbols) -> Self {
        Self { f, fname, syms, errors: Vec::new(), visited: HashSet::new() }
    }

    fn run(&mut self) {
        // Parameters arrive owned and un-borrowed: the empty env is correct.
        self.walk(self.f.entry, Env::default());
    }

    fn emit(&mut self, message: String) {
        self.errors.push(BorrowError { func: self.fname.clone(), message });
    }

    /// Resolve a local's display name (`name` if present, else `_<id>`).
    fn local_name(&self, local: LocalId) -> String {
        self.f
            .locals
            .get(local.0 as usize)
            .and_then(|d| d.name)
            .map(|s| self.syms.resolve(s).to_string())
            .unwrap_or_else(|| format!("_{}", local.0))
    }

    /// The declared type of `local`, if it is in range.
    fn local_ty(&self, local: LocalId) -> Option<&Ty> {
        self.f.locals.get(local.0 as usize).map(|d| &d.ty)
    }

    /// Is `local` a non-Copy (move) type?
    fn is_move_local(&self, local: LocalId) -> bool {
        self.local_ty(local).map(|t| !is_copy(t)).unwrap_or(false)
    }

    fn block(&self, id: BlockId) -> Option<&rv_ir::Block<Lowerable>> {
        self.f.blocks.iter().find(|b| b.id == id)
    }

    // -- CFG walk -----------------------------------------------------------

    /// Forward-walk a block: process its statements then its terminator,
    /// recursing into successors. A back-edge into an already-visited block
    /// stops the path (loop termination).
    fn walk(&mut self, id: BlockId, mut env: Env) {
        if !self.visited.insert(id) {
            // Already seen on this walk: a back-edge. Stop (see precision note).
            return;
        }
        // Clone what we need so we don't hold a borrow of `self` across the
        // `&mut self` check calls below.
        let Some(block) = self.block(id) else { return };
        let stmts = block.stmts.clone();
        let term = clone_term(&block.term);

        for stmt in &stmts {
            self.check_stmt(stmt, &mut env);
        }
        // Borrows are block-scoped: anything created in this block stays active
        // through the terminator, then is dropped before we enter successors.
        self.check_terminator(&term, &mut env);
        env.release_borrows();

        match &term {
            Terminator::Goto(b) => self.walk(*b, env),
            Terminator::Branch { then_blk, else_blk, .. } => {
                self.walk(*then_blk, env.clone());
                self.walk(*else_blk, env);
            }
            Terminator::Match { arms, otherwise, .. } => {
                for arm in arms {
                    self.walk(arm.target, env.clone());
                }
                if let Some(o) = otherwise {
                    self.walk(*o, env);
                }
            }
            Terminator::Return(_) => {}
            Terminator::Drop { next, .. } => self.walk(*next, env),
            // `Panic` aborts: no successors, nothing to check.
            Terminator::Panic => {}
        }
    }

    // -- Statements ---------------------------------------------------------

    fn check_stmt(&mut self, stmt: &Stmt, env: &mut Env) {
        match stmt {
            Stmt::Assign(place, rvalue) => self.check_assign(place, rvalue, env),
            // Ghost statements carry only `Prop`s (no value operands); nothing
            // to move or borrow.
            Stmt::Assert(_) | Stmt::Assume(_) | Stmt::Invariant(_) => {}
        }
    }

    /// Check an `Assign(place, rvalue)`: first the reads performed by the RHS,
    /// then the write to `place`'s destination.
    fn check_assign(&mut self, dest: &Place, rvalue: &RValue, env: &mut Env) {
        // Destination's root local: a write to a *bare* local revives it (clears
        // moved) and counts as an assignment for the borrow rules.
        let dest_local = dest.local;
        let dest_is_bare = dest.proj.is_empty();

        match rvalue {
            RValue::Use(op) => {
                // Assigning one local to another consumes the source by value.
                self.consume_operand(op, env);
            }
            RValue::Bin(_, a, b) | RValue::WrappingBin(_, a, b) => {
                self.consume_operand(a, env);
                self.consume_operand(b, env);
            }
            RValue::Un(_, a) => {
                self.consume_operand(a, env);
            }
            RValue::VecLen(_a) => {
                // `v.len()` reads the vector without consuming it (a shared use).
            }
            RValue::VecPush(_a, b) => {
                // `v.push(x)` mutates `v` in place (a `&mut`-style use, NOT a move);
                // the assignment back to `v` re-establishes it. Only the pushed
                // value `b` is consumed (moved into the vector).
                self.consume_operand(b, env);
            }
            RValue::Call(_, args) => {
                for a in args {
                    self.consume_operand(a, env);
                }
            }
            // Building a closure moves its captured operands into the closure value.
            RValue::Closure(_, captures) => {
                for c in captures {
                    self.consume_operand(c, env);
                }
            }
            // An indirect call consumes the closure value and its arguments by value.
            RValue::CallClosure(callee, args) => {
                self.consume_operand(callee, env);
                for a in args {
                    self.consume_operand(a, env);
                }
            }
            RValue::Aggregate(_, fields) => {
                for fld in fields {
                    self.consume_operand(fld, env);
                }
            }
            RValue::Ref(kind, borrowed) => {
                self.check_borrow(*kind, borrowed, env);
            }
        }

        // Now perform the write to the destination.
        if dest_is_bare {
            // Cannot assign to a local while it is borrowed.
            if env.has_any_borrow(dest_local) {
                let n = self.local_name(dest_local);
                self.emit(format!("cannot assign `{n}` while borrowed"));
            }
            // Reassignment revives a previously-moved local (grade back to Zero).
            env.revive(dest_local);
        } else {
            // A projected write (e.g. `x.f = ...`, `*p = ...`) reads `x`/`p`'s
            // path; treat it as a use of the root for move purposes, but it does
            // not revive a moved local (it is a partial write into a live place).
            self.use_local_for_read(dest_local, env);
        }
    }

    // -- Borrows ------------------------------------------------------------

    /// Check creating `RValue::Ref(kind, place)`: lend the permission the borrow
    /// requires out of the root local. Exclusion is not a special-cased rule —
    /// it is the validity predicate of the [`FracPerm`] PCM: the borrow is legal
    /// iff `lent ⊕ required` stays `≤ 1`.
    fn check_borrow(&mut self, kind: BorrowKind, place: &Place, env: &mut Env) {
        let local = place.local;

        // Reading through the place to create the reference is itself a (shared)
        // read of the root: borrowing a moved value is an error.
        if self.is_move_local(local) && env.is_moved(local) {
            let n = self.local_name(local);
            self.emit(format!("use of moved value `{n}`"));
        }

        // What this borrow needs to hold while live. A `&mut` needs the full
        // permission; a `&` takes the local's next halving fraction so shared
        // borrows compose among themselves but exclude uniqueness.
        let required = match algebra_kind(kind) {
            k if k.is_unique() => k.required_perm(),
            _ => {
                let st = env.state(local);
                let take = st.next_share;
                // Halve for the next shared borrow; on (absurd) overflow keep
                // the current fraction — still sound, at worst over-excluding.
                st.next_share = st.next_share.half().unwrap_or(take);
                take
            }
        };

        if !env.try_lend(local, &required) {
            let n = self.local_name(local);
            match kind {
                // `&mut` composed to > 1: some permission is already lent.
                BorrowKind::Mut => self.emit(format!(
                    "cannot borrow `{n}` as mutable: it is already borrowed"
                )),
                // A shared fraction only fails to compose against a full lent
                // permission, i.e. a live `&mut` (shared fractions sum < 1).
                BorrowKind::Shared => self.emit(format!(
                    "cannot borrow `{n}` as shared: it is already mutably borrowed"
                )),
            }
        }
    }

    // -- Operand consumption (move semantics) -------------------------------

    /// An operand appearing in a *consuming* position. A bare-local `Copy` of a
    /// non-Copy type MOVES that local; anything else is a non-consuming read.
    fn consume_operand(&mut self, op: &Operand, env: &mut Env) {
        let Operand::Copy(place) = op else {
            // `Const` consumes nothing.
            return;
        };
        let local = place.local;

        // Always validate the read first (use-after-move on the root).
        self.use_local_for_read(local, env);

        // A by-value MOVE requires: a *bare* local (no projection) of a non-Copy
        // type. Projected access (`x.f`, `*p`) reads through and does not move
        // the whole local in this first pass.
        if place.proj.is_empty() && self.is_move_local(local) {
            // Moving requires the whole permission: forbidden while any part of
            // it is lent out to a borrow.
            if env.has_any_borrow(local) {
                let n = self.local_name(local);
                self.emit(format!("cannot move `{n}` while borrowed"));
            }
            env.consume(local);
        }
    }

    /// Register a *read* of `local` (any access of its value or a projection of
    /// it). Reading a non-Copy local whose grade is already ≥ `One` (consumed)
    /// is a use-after-move error — the affine discipline.
    fn use_local_for_read(&mut self, local: LocalId, env: &Env) {
        if self.is_move_local(local) && env.is_moved(local) {
            let n = self.local_name(local);
            // Borrow `self` immutably above, then mutate via emit: collect first.
            let msg = format!("use of moved value `{n}`");
            self.errors.push(BorrowError { func: self.fname.clone(), message: msg });
        }
    }

    // -- Terminators --------------------------------------------------------

    fn check_terminator(&mut self, term: &Terminator<Lowerable>, env: &mut Env) {
        match term {
            Terminator::Return(op) => self.consume_operand(op, env),
            // A branch condition / match scrutinee is *inspected*, not moved: in
            // this IR the `match` arms then read the scrutinee's fields (via
            // `Downcast`+`Field` projections), so moving the scrutinee here would
            // wrongly flag those arm bindings as use-after-move. We read it (which
            // still reports using an already-moved value) without consuming it.
            Terminator::Branch { cond, .. } => {
                if let Operand::Copy(p) = cond {
                    self.use_local_for_read(p.local, env);
                }
            }
            Terminator::Match { scrutinee, .. } => {
                if let Operand::Copy(p) = scrutinee {
                    self.use_local_for_read(p.local, env);
                }
            }
            // `Drop` consumes a value that ownership already accounts for; it is
            // not a *use* that should trip use-after-move, and reading the place
            // is the drop itself. We do not flag it.
            Terminator::Goto(_) | Terminator::Drop { .. } | Terminator::Panic => {}
        }
    }
}

/// `Terminator<Lowerable>` is not `Clone` (it carries `P::Strategy`), so we
/// reconstruct a shallow copy of the fields we traverse. `Drop`'s strategy is a
/// `DisciplineId` (`Copy`), so this is cheap and total.
fn clone_term(t: &Terminator<Lowerable>) -> Terminator<Lowerable> {
    match t {
        Terminator::Goto(b) => Terminator::Goto(*b),
        Terminator::Branch { cond, then_blk, else_blk } => Terminator::Branch {
            cond: cond.clone(),
            then_blk: *then_blk,
            else_blk: *else_blk,
        },
        Terminator::Match { scrutinee, arms, otherwise } => Terminator::Match {
            scrutinee: scrutinee.clone(),
            arms: arms.clone(),
            otherwise: *otherwise,
        },
        Terminator::Return(op) => Terminator::Return(op.clone()),
        Terminator::Drop { place, strategy, next } => Terminator::Drop {
            place: place.clone(),
            strategy: *strategy,
            next: *next,
        },
        Terminator::Panic => Terminator::Panic,
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use rv_ir::{AggKind, Block, Const, DisciplineId, LocalDecl, Proj};

    // -- Builders -----------------------------------------------------------

    /// A minimal single-block function builder.
    struct Build {
        syms: Symbols,
        name: rv_core::Sym,
        locals: Vec<LocalDecl<Lowerable>>,
    }

    impl Build {
        fn new(fname: &str) -> Self {
            let mut syms = Symbols::new();
            let name = syms.intern(fname);
            Build { syms, name, locals: Vec::new() }
        }

        /// Declare a local with `name` and `ty`, returning its id.
        fn local(&mut self, name: &str, ty: Ty) -> LocalId {
            let s = self.syms.intern(name);
            let id = LocalId(self.locals.len() as u32);
            self.locals.push(LocalDecl { name: Some(s), ty });
            id
        }

        /// Finish into a single-block function with terminator `term`.
        fn finish(
            self,
            params: Vec<LocalId>,
            stmts: Vec<Stmt>,
            term: Terminator<Lowerable>,
        ) -> (Program<Lowerable>, Symbols) {
            let entry = BlockId(0);
            let func = Function {
                name: self.name,
                type_params: Vec::new(),
                params,
                ret: Ty::Unit,
                pre: rv_core::Prop::True,
                post: rv_core::Prop::True,
                locals: self.locals,
                blocks: vec![Block { id: entry, stmts, term }],
                entry,
            };
            let prog = Program { types: Vec::new(), funcs: vec![func] };
            (prog, self.syms)
        }
    }

    fn copy(local: LocalId) -> Operand {
        Operand::Copy(Place::local(local))
    }

    // -- (a) clean program → no errors --------------------------------------

    #[test]
    fn clean_program_has_no_errors() {
        // fn f() { let a: Int = 1; let b: Int = a + a; return; }
        // Int is Copy, so using `a` twice is fine.
        let mut b = Build::new("f");
        let a = b.local("a", Ty::Int);
        let bb = b.local("b", Ty::Int);
        let stmts = vec![
            Stmt::Assign(Place::local(a), RValue::Use(Operand::Const(Const::Int(1)))),
            Stmt::Assign(Place::local(bb), RValue::Bin(rv_core::BinOp::Add, copy(a), copy(a))),
        ];
        let (prog, syms) = b.finish(vec![], stmts, Terminator::Return(Operand::Const(Const::Unit)));
        let errs = check(&prog, &syms);
        assert!(errs.is_empty(), "expected no errors, got {errs:?}");
    }

    // -- (b) use-after-move of an Adt local → one error ---------------------

    #[test]
    fn use_after_move_of_adt() {
        // fn f() { let a: Adt(S); let b = a; (move) let c = a; (use after move) }
        let mut b = Build::new("f");
        let s = b.syms.intern("S");
        let a = b.local("a", Ty::Adt(s));
        let bb = b.local("b", Ty::Adt(s));
        let cc = b.local("c", Ty::Adt(s));
        let stmts = vec![
            // b = a  -> moves a
            Stmt::Assign(Place::local(bb), RValue::Use(copy(a))),
            // c = a  -> use of moved value `a`
            Stmt::Assign(Place::local(cc), RValue::Use(copy(a))),
        ];
        let (prog, syms) = b.finish(vec![], stmts, Terminator::Return(Operand::Const(Const::Unit)));
        let errs = check(&prog, &syms);
        assert_eq!(errs.len(), 1, "expected exactly one error, got {errs:?}");
        assert!(errs[0].message.contains("use of moved value `a`"), "{:?}", errs[0]);
    }

    // -- (c) two simultaneous &mut of the same local → one error ------------

    #[test]
    fn double_mut_borrow() {
        // fn f() { let a: Int; let r1 = &mut a; let r2 = &mut a; }  (one conflict)
        let mut b = Build::new("f");
        let a = b.local("a", Ty::Int);
        let r1 = b.local("r1", Ty::Ref { mutable: true, inner: Box::new(Ty::Int) });
        let r2 = b.local("r2", Ty::Ref { mutable: true, inner: Box::new(Ty::Int) });
        let stmts = vec![
            Stmt::Assign(Place::local(r1), RValue::Ref(BorrowKind::Mut, Place::local(a))),
            Stmt::Assign(Place::local(r2), RValue::Ref(BorrowKind::Mut, Place::local(a))),
        ];
        let (prog, syms) = b.finish(vec![], stmts, Terminator::Return(Operand::Const(Const::Unit)));
        let errs = check(&prog, &syms);
        assert_eq!(errs.len(), 1, "expected exactly one error, got {errs:?}");
        assert!(errs[0].message.contains("as mutable"), "{:?}", errs[0]);
    }

    // -- (d) shared & + read → no error -------------------------------------

    #[test]
    fn shared_borrow_then_read_is_ok() {
        // fn f() { let a: Int; let r1 = &a; let r2 = &a; let x = a; }
        // Multiple shared borrows + a Copy read of an Int: all fine.
        let mut b = Build::new("f");
        let a = b.local("a", Ty::Int);
        let r1 = b.local("r1", Ty::Ref { mutable: false, inner: Box::new(Ty::Int) });
        let r2 = b.local("r2", Ty::Ref { mutable: false, inner: Box::new(Ty::Int) });
        let x = b.local("x", Ty::Int);
        let stmts = vec![
            Stmt::Assign(Place::local(r1), RValue::Ref(BorrowKind::Shared, Place::local(a))),
            Stmt::Assign(Place::local(r2), RValue::Ref(BorrowKind::Shared, Place::local(a))),
            Stmt::Assign(Place::local(x), RValue::Use(copy(a))),
        ];
        let (prog, syms) = b.finish(vec![], stmts, Terminator::Return(Operand::Const(Const::Unit)));
        let errs = check(&prog, &syms);
        assert!(errs.is_empty(), "expected no errors, got {errs:?}");
    }

    // -- Extra: reassignment revives a moved local --------------------------

    #[test]
    fn reassignment_clears_moved() {
        // let a: Adt; b = a (move); a = S{} (revive); c = a (ok)
        let mut b = Build::new("f");
        let s = b.syms.intern("S");
        let a = b.local("a", Ty::Adt(s));
        let bb = b.local("b", Ty::Adt(s));
        let cc = b.local("c", Ty::Adt(s));
        let stmts = vec![
            Stmt::Assign(Place::local(bb), RValue::Use(copy(a))),
            // a = S{}  -> revives a
            Stmt::Assign(Place::local(a), RValue::Aggregate(AggKind::Struct(s), vec![])),
            Stmt::Assign(Place::local(cc), RValue::Use(copy(a))),
        ];
        let (prog, syms) = b.finish(vec![], stmts, Terminator::Return(Operand::Const(Const::Unit)));
        let errs = check(&prog, &syms);
        assert!(errs.is_empty(), "expected no errors after revive, got {errs:?}");
    }

    // -- Extra: &mut while shared-borrowed ----------------------------------

    #[test]
    fn mut_while_shared_borrowed() {
        let mut b = Build::new("f");
        let a = b.local("a", Ty::Int);
        let r1 = b.local("r1", Ty::Ref { mutable: false, inner: Box::new(Ty::Int) });
        let r2 = b.local("r2", Ty::Ref { mutable: true, inner: Box::new(Ty::Int) });
        let stmts = vec![
            Stmt::Assign(Place::local(r1), RValue::Ref(BorrowKind::Shared, Place::local(a))),
            Stmt::Assign(Place::local(r2), RValue::Ref(BorrowKind::Mut, Place::local(a))),
        ];
        let (prog, syms) = b.finish(vec![], stmts, Terminator::Return(Operand::Const(Const::Unit)));
        let errs = check(&prog, &syms);
        assert_eq!(errs.len(), 1, "{errs:?}");
        assert!(errs[0].message.contains("as mutable"), "{:?}", errs[0]);
    }

    // -- Extra: move while borrowed -----------------------------------------

    #[test]
    fn move_while_borrowed() {
        let mut b = Build::new("f");
        let s = b.syms.intern("S");
        let a = b.local("a", Ty::Adt(s));
        let r = b.local("r", Ty::Ref { mutable: false, inner: Box::new(Ty::Adt(s)) });
        let bb = b.local("b", Ty::Adt(s));
        let stmts = vec![
            Stmt::Assign(Place::local(r), RValue::Ref(BorrowKind::Shared, Place::local(a))),
            // b = a while a is borrowed -> error
            Stmt::Assign(Place::local(bb), RValue::Use(copy(a))),
        ];
        let (prog, syms) = b.finish(vec![], stmts, Terminator::Return(Operand::Const(Const::Unit)));
        let errs = check(&prog, &syms);
        assert_eq!(errs.len(), 1, "{errs:?}");
        assert!(errs[0].message.contains("cannot move `a` while borrowed"), "{:?}", errs[0]);
    }

    // -- Extra: branch independence (move in one arm only) ------------------

    #[test]
    fn move_in_one_branch_is_independent() {
        // b0: cond branch on c -> b1 / b2
        // b1: x = a (move a)        b2: y = a (move a)   — independent paths
        // Neither path re-uses a after its own move, so no error.
        let mut b = Build::new("f");
        let s = b.syms.intern("S");
        let a = b.local("a", Ty::Adt(s));
        let c = b.local("c", Ty::Bool);
        let x = b.local("x", Ty::Adt(s));
        let y = b.local("y", Ty::Adt(s));

        let entry = BlockId(0);
        let b1 = BlockId(1);
        let b2 = BlockId(2);
        let exit = BlockId(3);

        let blocks = vec![
            Block {
                id: entry,
                stmts: vec![],
                term: Terminator::Branch { cond: copy(c), then_blk: b1, else_blk: b2 },
            },
            Block {
                id: b1,
                stmts: vec![Stmt::Assign(Place::local(x), RValue::Use(copy(a)))],
                term: Terminator::Goto(exit),
            },
            Block {
                id: b2,
                stmts: vec![Stmt::Assign(Place::local(y), RValue::Use(copy(a)))],
                term: Terminator::Goto(exit),
            },
            Block { id: exit, stmts: vec![], term: Terminator::Return(Operand::Const(Const::Unit)) },
        ];
        let func = Function {
            name: b.name,
            type_params: Vec::new(),
            params: vec![],
            ret: Ty::Unit,
            pre: rv_core::Prop::True,
            post: rv_core::Prop::True,
            locals: b.locals,
            blocks,
            entry,
        };
        let prog = Program { types: Vec::new(), funcs: vec![func] };
        let errs = check(&prog, &b.syms);
        assert!(errs.is_empty(), "expected no errors, got {errs:?}");
    }

    // -- Extra: Drop carries a strategy and is handled ----------------------

    #[test]
    fn drop_terminator_is_handled() {
        let mut b = Build::new("f");
        let s = b.syms.intern("S");
        let a = b.local("a", Ty::Adt(s));
        let entry = BlockId(0);
        let exit = BlockId(1);
        let blocks = vec![
            Block {
                id: entry,
                stmts: vec![Stmt::Assign(
                    Place::local(a),
                    RValue::Aggregate(AggKind::Struct(s), vec![]),
                )],
                term: Terminator::Drop {
                    place: Place::local(a),
                    strategy: DisciplineId(0),
                    next: exit,
                },
            },
            Block { id: exit, stmts: vec![], term: Terminator::Return(Operand::Const(Const::Unit)) },
        ];
        let func = Function {
            name: b.name,
            type_params: Vec::new(),
            params: vec![],
            ret: Ty::Unit,
            pre: rv_core::Prop::True,
            post: rv_core::Prop::True,
            locals: b.locals,
            blocks,
            entry,
        };
        let prog = Program { types: Vec::new(), funcs: vec![func] };
        let errs = check(&prog, &b.syms);
        assert!(errs.is_empty(), "{errs:?}");
    }

    // -- Algebra: many shared borrows compose (Σ halvings < 1) --------------

    #[test]
    fn many_shared_borrows_stay_valid() {
        // Eight `&a` in one block: fractions ½ + ¼ + … always compose validly.
        let mut b = Build::new("f");
        let a = b.local("a", Ty::Int);
        let mut stmts = Vec::new();
        for i in 0..8 {
            let r = b.local(&format!("r{i}"), Ty::Ref { mutable: false, inner: Box::new(Ty::Int) });
            stmts.push(Stmt::Assign(Place::local(r), RValue::Ref(BorrowKind::Shared, Place::local(a))));
        }
        let (prog, syms) = b.finish(vec![], stmts, Terminator::Return(Operand::Const(Const::Unit)));
        let errs = check(&prog, &syms);
        assert!(errs.is_empty(), "shared borrows must compose, got {errs:?}");
    }

    // -- Algebra: any outstanding fraction excludes the full permission -----

    #[test]
    fn mut_after_many_shared_borrows_fails() {
        // Several `&a` then one `&mut a`: lent < 1 but full no longer fits.
        let mut b = Build::new("f");
        let a = b.local("a", Ty::Int);
        let mut stmts = Vec::new();
        for i in 0..3 {
            let r = b.local(&format!("r{i}"), Ty::Ref { mutable: false, inner: Box::new(Ty::Int) });
            stmts.push(Stmt::Assign(Place::local(r), RValue::Ref(BorrowKind::Shared, Place::local(a))));
        }
        let m = b.local("m", Ty::Ref { mutable: true, inner: Box::new(Ty::Int) });
        stmts.push(Stmt::Assign(Place::local(m), RValue::Ref(BorrowKind::Mut, Place::local(a))));
        let (prog, syms) = b.finish(vec![], stmts, Terminator::Return(Operand::Const(Const::Unit)));
        let errs = check(&prog, &syms);
        assert_eq!(errs.len(), 1, "{errs:?}");
        assert!(errs[0].message.contains("as mutable"), "{:?}", errs[0]);
    }

    // -- Algebra: borrows release at block end (permission returns whole) ---

    #[test]
    fn borrow_released_at_block_end_allows_mut() {
        // b0: r = &a; goto b1.  b1: m = &mut a.  The shared fraction is returned
        // at the end of b0, so the full permission is available in b1.
        let mut b = Build::new("f");
        let a = b.local("a", Ty::Int);
        let r = b.local("r", Ty::Ref { mutable: false, inner: Box::new(Ty::Int) });
        let m = b.local("m", Ty::Ref { mutable: true, inner: Box::new(Ty::Int) });
        let entry = BlockId(0);
        let b1 = BlockId(1);
        let blocks = vec![
            Block {
                id: entry,
                stmts: vec![Stmt::Assign(Place::local(r), RValue::Ref(BorrowKind::Shared, Place::local(a)))],
                term: Terminator::Goto(b1),
            },
            Block {
                id: b1,
                stmts: vec![Stmt::Assign(Place::local(m), RValue::Ref(BorrowKind::Mut, Place::local(a)))],
                term: Terminator::Return(Operand::Const(Const::Unit)),
            },
        ];
        let func = Function {
            name: b.name,
            type_params: Vec::new(),
            params: vec![],
            ret: Ty::Unit,
            pre: rv_core::Prop::True,
            post: rv_core::Prop::True,
            locals: b.locals,
            blocks,
            entry,
        };
        let prog = Program { types: Vec::new(), funcs: vec![func] };
        let errs = check(&prog, &b.syms);
        assert!(errs.is_empty(), "{errs:?}");
    }

    // -- Algebra: moves persist across blocks while borrows do not ----------

    #[test]
    fn move_grade_persists_across_blocks() {
        // b0: b = a (move); goto b1.  b1: c = a  → use of moved value.
        let mut bd = Build::new("f");
        let s = bd.syms.intern("S");
        let a = bd.local("a", Ty::Adt(s));
        let bb = bd.local("b", Ty::Adt(s));
        let cc = bd.local("c", Ty::Adt(s));
        let entry = BlockId(0);
        let b1 = BlockId(1);
        let blocks = vec![
            Block {
                id: entry,
                stmts: vec![Stmt::Assign(Place::local(bb), RValue::Use(copy(a)))],
                term: Terminator::Goto(b1),
            },
            Block {
                id: b1,
                stmts: vec![Stmt::Assign(Place::local(cc), RValue::Use(copy(a)))],
                term: Terminator::Return(Operand::Const(Const::Unit)),
            },
        ];
        let func = Function {
            name: bd.name,
            type_params: Vec::new(),
            params: vec![],
            ret: Ty::Unit,
            pre: rv_core::Prop::True,
            post: rv_core::Prop::True,
            locals: bd.locals,
            blocks,
            entry,
        };
        let prog = Program { types: Vec::new(), funcs: vec![func] };
        let errs = check(&prog, &bd.syms);
        assert_eq!(errs.len(), 1, "{errs:?}");
        assert!(errs[0].message.contains("use of moved value `a`"), "{:?}", errs[0]);
    }

    // -- Extra: projected read of a moved value is caught -------------------

    #[test]
    fn projected_read_after_move() {
        // b = a (move a); c = a.0 (use of moved a via projection)
        let mut b = Build::new("f");
        let s = b.syms.intern("S");
        let a = b.local("a", Ty::Adt(s));
        let bb = b.local("b", Ty::Adt(s));
        let cc = b.local("c", Ty::Int);
        let proj_place = Place { local: a, proj: vec![Proj::Field(0)] };
        let stmts = vec![
            Stmt::Assign(Place::local(bb), RValue::Use(copy(a))),
            Stmt::Assign(Place::local(cc), RValue::Use(Operand::Copy(proj_place))),
        ];
        let (prog, syms) = b.finish(vec![], stmts, Terminator::Return(Operand::Const(Const::Unit)));
        let errs = check(&prog, &syms);
        assert_eq!(errs.len(), 1, "{errs:?}");
        assert!(errs[0].message.contains("use of moved value `a`"), "{:?}", errs[0]);
    }
}
