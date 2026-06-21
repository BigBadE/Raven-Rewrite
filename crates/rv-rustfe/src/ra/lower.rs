//! Statement / expression lowering from `ra_ap_syntax` AST to `rv_ir`.

use ra_ap_syntax::ast::{self, HasArgList, HasLoopBody, HasName};
use ra_ap_syntax::AstNode;

use std::collections::HashSet;

use rv_core::{BinOp, Prop, Sym, Symbols, UnOp};
use rv_ir::{
    BlockId, BorrowKind, Const, Function, LocalId, Operand, Place, Proj, RValue, Stmt,
    Terminator,
};

use super::build::{FnBuilder, LoopTargets};

type R<T> = Result<T, String>;

/// Where the value of a structured expression (`if`/`match`/block tail, arm) goes.
/// This is what makes the same CFG-builders serve both statement and value
/// position: a function-body tail *returns*, a `let x = if …` branch *assigns to
/// `x`*, and a statement-position `if …;` *discards*.
#[derive(Clone, Copy)]
enum Dst {
    /// Implicit return — the tail/arm value is the function's result.
    Return,
    /// Assign the tail/arm value to this local (value position).
    Local(LocalId),
    /// Statement position: evaluate for effect, produce no value, fall through.
    Discard,
}

impl FnBuilder<'_> {
    /// Lower a function body: its tail expression is the implicit return value.
    pub fn lower_fn_body(&mut self, block: &ast::BlockExpr, syms: &mut Symbols) -> R<()> {
        self.lower_block(block, Dst::Return, syms)
    }

    /// Lower a block's statements and (optionally) its tail expression. The tail's
    /// value goes to `dst` (return / local / discarded).
    fn lower_block(&mut self, block: &ast::BlockExpr, dst: Dst, syms: &mut Symbols) -> R<()> {
        let Some(list) = block.stmt_list() else {
            self.assign_unit_if_local(dst);
            return Ok(());
        };
        for stmt in list.statements() {
            if self.diverged() {
                break;
            }
            self.lower_stmt(&stmt, syms)?;
        }
        if !self.diverged() {
            if let Some(tail) = list.tail_expr() {
                self.finish_tail(dst, &tail, syms)?;
            } else {
                // A block with no tail has value `()`.
                self.assign_unit_if_local(dst);
            }
        }
        Ok(())
    }

    /// Direct a block tail / non-block arm value to its destination.
    fn finish_tail(&mut self, dst: Dst, tail: &ast::Expr, syms: &mut Symbols) -> R<()> {
        match dst {
            Dst::Return => {
                if is_structured(tail) {
                    self.lower_expr_value(tail, Dst::Return, syms)
                } else {
                    let op = self.lower_operand(tail, syms)?;
                    let dead = self.fresh_block_id();
                    self.finish_block(Terminator::Return(op), dead);
                    self.set_diverged();
                    Ok(())
                }
            }
            Dst::Local(d) => self.lower_into_local(d, tail, syms),
            Dst::Discard => self.lower_expr_stmt(tail, syms),
        }
    }

    /// In value position, a structured expression that produces no useful value
    /// (loop / macro) still has type `()`.
    fn assign_unit_if_local(&mut self, dst: Dst) {
        if let Dst::Local(d) = dst {
            if !self.diverged() {
                self.push_stmt(Stmt::Assign(
                    Place::local(d),
                    RValue::Use(Operand::Const(Const::Unit)),
                ));
            }
        }
    }

    fn lower_stmt(&mut self, stmt: &ast::Stmt, syms: &mut Symbols) -> R<()> {
        match stmt {
            ast::Stmt::LetStmt(l) => self.lower_let(l, syms),
            ast::Stmt::ExprStmt(e) => {
                if let Some(expr) = e.expr() {
                    self.lower_expr_stmt(&expr, syms)?;
                }
                Ok(())
            }
            ast::Stmt::Item(_) => Ok(()), // nested items: ignore for now
        }
    }

    /// `let pat (: ty)? = init;`. Supports identifier, `_`, tuple, and struct
    /// destructuring patterns.
    fn lower_let(&mut self, l: &ast::LetStmt, syms: &mut Symbols) -> R<()> {
        let pat = l.pat().ok_or("let without pattern")?;
        match pat {
            ast::Pat::IdentPat(ip) => {
                let name = syms.intern(&ident_pat_name(&ip)?);
                let dst = self.new_local(Some(name));
                let decl_vec = l.ty().map(|t| is_vec_ty(&t)).unwrap_or(false);
                if let Some(init) = l.initializer() {
                    self.lower_into_local(dst, &init, syms)?;
                    if let Some(adt) = self.adt_of_expr(&init, syms) {
                        self.set_local_adt(dst, adt);
                    }
                    if expr_yields_vec(&init) {
                        self.mark_vec(dst);
                    }
                }
                if decl_vec {
                    self.mark_vec(dst);
                }
                self.bind(name, dst);
                Ok(())
            }
            ast::Pat::WildcardPat(_) => {
                if let Some(init) = l.initializer() {
                    let tmp = self.new_local(None);
                    self.lower_into_local(tmp, &init, syms)?;
                }
                Ok(())
            }
            ast::Pat::TuplePat(tp) => {
                let init = l.initializer().ok_or("tuple `let` needs an initialiser")?;
                let base = self.expr_to_local(&init, syms)?;
                for (i, sub) in tp.fields().enumerate() {
                    if let ast::Pat::IdentPat(ip) = sub {
                        let name = syms.intern(&ident_pat_name(&ip)?);
                        let dst = self.new_local(Some(name));
                        let src = Place { local: base, proj: vec![Proj::Field(i as u32)] };
                        self.push_stmt(Stmt::Assign(Place::local(dst), RValue::Use(Operand::Copy(src))));
                        self.bind(name, dst);
                    }
                }
                Ok(())
            }
            ast::Pat::RecordPat(rp) => self.lower_let_record(rp, l, syms),
            other => Err(format!("unsupported `let` pattern `{:?}`", other.syntax().kind())),
        }
    }

    fn lower_let_record(&mut self, rp: ast::RecordPat, l: &ast::LetStmt, syms: &mut Symbols) -> R<()> {
        let init = l.initializer().ok_or("struct `let` needs an initialiser")?;
        let base = self.expr_to_local(&init, syms)?;
        let struct_name = syms.intern(&path_last(&rp.path().ok_or("record pattern without path")?)?);
        let info = self
            .types
            .struct_info(struct_name)
            .ok_or_else(|| format!("unknown struct `{}` in pattern", syms.resolve(struct_name)))?;
        let field_index = info.field_index.clone();
        self.set_local_adt(base, struct_name);
        if let Some(fl) = rp.record_pat_field_list() {
            for f in fl.fields() {
                let fname = f
                    .field_name()
                    .map(|n| n.to_string())
                    .ok_or("record pattern field without name")?;
                let fsym = syms.intern(&fname);
                let idx = *field_index
                    .get(&fsym)
                    .ok_or_else(|| format!("struct `{}` has no field `{fname}`", syms.resolve(struct_name)))?;
                // Binding name: `field: binding` or shorthand `field`.
                let bind_name = match f.pat() {
                    Some(ast::Pat::IdentPat(ip)) => syms.intern(&ident_pat_name(&ip)?),
                    None => fsym,
                    Some(_) => return Err("only simple field bindings supported".to_string()),
                };
                let dst = self.new_local(Some(bind_name));
                let src = Place { local: base, proj: vec![Proj::Field(idx)] };
                self.push_stmt(Stmt::Assign(Place::local(dst), RValue::Use(Operand::Copy(src))));
                self.bind(bind_name, dst);
            }
        }
        Ok(())
    }

    /// An expression used in statement position.
    fn lower_expr_stmt(&mut self, e: &ast::Expr, syms: &mut Symbols) -> R<()> {
        match e {
            ast::Expr::ReturnExpr(r) => {
                let operand = match r.expr() {
                    Some(v) => self.lower_operand(&v, syms)?,
                    None => Operand::Const(Const::Unit),
                };
                let dead = self.fresh_block_id();
                self.finish_block(Terminator::Return(operand), dead);
                self.set_diverged();
                Ok(())
            }
            ast::Expr::BinExpr(b) if is_assign(b) => self.lower_assign(b, syms),
            _ if is_structured(e) => self.lower_expr_value(e, Dst::Discard, syms),
            // Evaluate for side effects (calls / method calls).
            _ => {
                let tmp = self.new_local(None);
                self.lower_into_local(tmp, e, syms)
            }
        }
    }

    /// Lower a structured expression (`if`/`while`/`loop`/`for`/`match`/`break`/
    /// `continue`), building its CFG and directing its value to `dst`.
    fn lower_expr_value(&mut self, e: &ast::Expr, dst: Dst, syms: &mut Symbols) -> R<()> {
        match e {
            ast::Expr::IfExpr(i) => self.lower_if(i, dst, syms),
            ast::Expr::MatchExpr(m) => self.lower_match(m, dst, syms),
            ast::Expr::BlockExpr(b) => self.lower_block(b, dst, syms),
            ast::Expr::WhileExpr(w) => {
                self.lower_while(w, syms)?;
                self.assign_unit_if_local(dst);
                Ok(())
            }
            ast::Expr::LoopExpr(l) => {
                self.lower_loop(l, syms)?;
                self.assign_unit_if_local(dst);
                Ok(())
            }
            ast::Expr::ForExpr(f) => {
                self.lower_for(f, syms)?;
                self.assign_unit_if_local(dst);
                Ok(())
            }
            ast::Expr::BreakExpr(_) => self.lower_break(),
            ast::Expr::ContinueExpr(_) => self.lower_continue(),
            ast::Expr::MacroExpr(m) => {
                self.lower_macro_stmt(m, syms)?;
                self.assign_unit_if_local(dst);
                Ok(())
            }
            other => Err(format!("unsupported structured expression `{:?}`", other.syntax().kind())),
        }
    }

    fn lower_assign(&mut self, b: &ast::BinExpr, syms: &mut Symbols) -> R<()> {
        let lhs = b.lhs().ok_or("assignment without lhs")?;
        let rhs = b.rhs().ok_or("assignment without rhs")?;
        let dst = self.lower_place(&lhs, syms)?;
        // Compound `x op= y` desugars to `x = x op y`.
        if let Some(ast::BinaryOp::Assignment { op: Some(arith) }) = b.op_kind() {
            let op = arith_to_binop(arith).ok_or("unsupported compound assignment")?;
            let cur = Operand::Copy(dst.clone());
            let rv = self.lower_operand(&rhs, syms)?;
            self.push_stmt(Stmt::Assign(dst, RValue::Bin(op, cur, rv)));
        } else {
            let rv = self.lower_rvalue(&rhs, syms)?;
            self.push_stmt(Stmt::Assign(dst, rv));
        }
        Ok(())
    }

    fn lower_if(&mut self, node: &ast::IfExpr, dst: Dst, syms: &mut Symbols) -> R<()> {
        let cond = node.condition().ok_or("if without condition")?;
        // `if let Pat = scrut { .. } else { .. }` desugars to a one-arm match.
        if let ast::Expr::LetExpr(le) = &cond {
            return self.lower_if_let(le, node, dst, syms);
        }
        let cond_op = self.lower_operand(&cond, syms)?;
        let then_id = self.fresh_block_id();
        let else_id = self.fresh_block_id();
        let join_id = self.fresh_block_id();
        self.finish_block(
            Terminator::Branch { cond: cond_op, then_blk: then_id, else_blk: else_id },
            then_id,
        );
        // then
        let then_blk = node.then_branch().ok_or("if without then-block")?;
        self.lower_block(&then_blk, dst, syms)?;
        if !self.diverged() {
            self.finish_block(Terminator::Goto(join_id), else_id);
        } else {
            self.start_block(else_id);
        }
        self.lower_else(node.else_branch(), dst, syms)?;
        if !self.diverged() {
            self.finish_block(Terminator::Goto(join_id), join_id);
        } else {
            self.start_block(join_id);
        }
        Ok(())
    }

    /// `if let Pat = scrut { then } else { els }`.
    fn lower_if_let(
        &mut self,
        le: &ast::LetExpr,
        node: &ast::IfExpr,
        dst: Dst,
        syms: &mut Symbols,
    ) -> R<()> {
        let scrut = le.expr().ok_or("`if let` without scrutinee")?;
        let pat = le.pat().ok_or("`if let` without pattern")?;
        let mp = self.parse_pat(&pat, syms)?;
        let scrut_local = self.expr_to_local(&scrut, syms)?;
        let then_id = self.fresh_block_id();
        let else_id = self.fresh_block_id();
        let join_id = self.fresh_block_id();
        match &mp {
            Some(p) => self.finish_block(
                Terminator::Match {
                    scrutinee: Operand::Copy(Place::local(scrut_local)),
                    arms: vec![rv_ir::MatchArm { variant: p.variant_idx, target: then_id }],
                    otherwise: Some(else_id),
                },
                then_id,
            ),
            // Irrefutable binder (`if let x = ..`): always takes the `then` branch.
            None => self.finish_block(Terminator::Goto(then_id), then_id),
        }
        // then: bind the matched fields, then lower the block.
        if let Some(p) = &mp {
            self.bind_pattern_fields(scrut_local, p, syms);
        }
        let then_blk = node.then_branch().ok_or("`if let` without then-block")?;
        self.lower_block(&then_blk, dst, syms)?;
        if !self.diverged() {
            self.finish_block(Terminator::Goto(join_id), else_id);
        } else {
            self.start_block(else_id);
        }
        self.lower_else(node.else_branch(), dst, syms)?;
        if !self.diverged() {
            self.finish_block(Terminator::Goto(join_id), join_id);
        } else {
            self.start_block(join_id);
        }
        Ok(())
    }

    /// Lower an `else` (block or `else if`), or synthesize `()` in value position
    /// when there is no `else`.
    fn lower_else(&mut self, els: Option<ast::ElseBranch>, dst: Dst, syms: &mut Symbols) -> R<()> {
        match els {
            Some(ast::ElseBranch::Block(b)) => self.lower_block(&b, dst, syms),
            Some(ast::ElseBranch::IfExpr(i)) => self.lower_if(&i, dst, syms),
            None => {
                self.assign_unit_if_local(dst);
                Ok(())
            }
        }
    }

    fn lower_while(&mut self, node: &ast::WhileExpr, syms: &mut Symbols) -> R<()> {
        let header = self.fresh_block_id();
        let body = self.fresh_block_id();
        let exit = self.fresh_block_id();
        self.finish_block(Terminator::Goto(header), header);
        let cond = node.condition().ok_or("while without condition")?;
        let cond_op = self.lower_operand(&cond, syms)?;
        self.finish_block(
            Terminator::Branch { cond: cond_op, then_blk: body, else_blk: exit },
            body,
        );
        self.push_loop(LoopTargets { continue_to: header, break_to: exit });
        if let Some(b) = node.loop_body() {
            self.lower_block(&b, Dst::Discard, syms)?;
        }
        self.pop_loop();
        if !self.diverged() {
            self.finish_block(Terminator::Goto(header), exit);
        } else {
            self.start_block(exit);
        }
        Ok(())
    }

    fn lower_loop(&mut self, node: &ast::LoopExpr, syms: &mut Symbols) -> R<()> {
        let header = self.fresh_block_id();
        let exit = self.fresh_block_id();
        self.finish_block(Terminator::Goto(header), header);
        self.push_loop(LoopTargets { continue_to: header, break_to: exit });
        if let Some(b) = node.loop_body() {
            self.lower_block(&b, Dst::Discard, syms)?;
        }
        self.pop_loop();
        if !self.diverged() {
            self.finish_block(Terminator::Goto(header), exit);
        } else {
            self.start_block(exit);
        }
        Ok(())
    }

    fn lower_for(&mut self, node: &ast::ForExpr, syms: &mut Symbols) -> R<()> {
        let pat = node.pat().ok_or("for without pattern")?;
        let iter = node.iterable().ok_or("for without iterable")?;
        // `for i in a..b` — a counted range loop.
        if let (ast::Pat::IdentPat(ip), ast::Expr::RangeExpr(range)) = (&pat, &iter) {
            if range_bounds(range).is_ok() {
                let var = syms.intern(&ident_pat_name(ip)?);
                return self.lower_for_range(node, var, range.clone(), syms);
            }
        }
        // `for x in xs` / `for x in xs.iter()` / `for x in &xs` — iterate a known
        // Vec / slice / array by index: a faithful desugaring to
        // `i = 0; while i < xs.len() { let x = xs[i]; <body>; i += 1; }`.
        if let Some(seq) = self.seq_local_of(&iter, syms) {
            return self.lower_for_seq(node, &pat, seq, syms);
        }
        Err("`for` supports an integer range `a..b` or iterating a Vec/slice/array".to_string())
    }

    /// Iterate a sequence local by index (real sequence-`for` desugaring).
    fn lower_for_seq(
        &mut self,
        node: &ast::ForExpr,
        pat: &ast::Pat,
        seq: LocalId,
        syms: &mut Symbols,
    ) -> R<()> {
        // The element binder: `for x in ..` or `for &x in ..`.
        let name = match pat {
            ast::Pat::IdentPat(ip) => syms.intern(&ident_pat_name(ip)?),
            ast::Pat::RefPat(rp) => match rp.pat() {
                Some(ast::Pat::IdentPat(ip)) => syms.intern(&ident_pat_name(&ip)?),
                _ => return Err("unsupported `for` element pattern".to_string()),
            },
            _ => return Err("unsupported `for` element pattern".to_string()),
        };
        // `i = 0` and `end = seq.len()`.
        let idx = self.new_local(None);
        self.push_stmt(Stmt::Assign(Place::local(idx), RValue::Use(Operand::Const(Const::Int(0)))));
        let end = self.new_local(None);
        self.push_stmt(Stmt::Assign(Place::local(end), RValue::VecLen(Operand::Copy(Place::local(seq)))));

        let header = self.fresh_block_id();
        let step = self.fresh_block_id();
        let body = self.fresh_block_id();
        let exit = self.fresh_block_id();
        self.finish_block(Terminator::Goto(header), header);
        let cond = self.new_local(None);
        self.push_stmt(Stmt::Assign(
            Place::local(cond),
            RValue::Bin(BinOp::Lt, Operand::Copy(Place::local(idx)), Operand::Copy(Place::local(end))),
        ));
        self.finish_block(
            Terminator::Branch { cond: Operand::Copy(Place::local(cond)), then_blk: body, else_blk: exit },
            body,
        );
        // `let x = seq[i];` — the element read is bounds-checked (`0 <= i < len`),
        // discharged by the loop guard `i < end == seq.len()`.
        let elem = self.new_local(Some(name));
        let src = Place { local: seq, proj: vec![Proj::Index(Operand::Copy(Place::local(idx)))] };
        self.push_stmt(Stmt::Assign(Place::local(elem), RValue::Use(Operand::Copy(src))));
        self.bind(name, elem);

        self.push_loop(LoopTargets { continue_to: step, break_to: exit });
        if let Some(b) = node.loop_body() {
            self.lower_block(&b, Dst::Discard, syms)?;
        }
        self.pop_loop();
        if !self.diverged() {
            self.finish_block(Terminator::Goto(step), step);
        } else {
            self.start_block(step);
        }
        self.push_stmt(Stmt::Assign(
            Place::local(idx),
            RValue::Bin(BinOp::Add, Operand::Copy(Place::local(idx)), Operand::Const(Const::Int(1))),
        ));
        self.finish_block(Terminator::Goto(header), exit);
        Ok(())
    }

    fn lower_for_range(
        &mut self,
        node: &ast::ForExpr,
        var: Sym,
        range: ast::RangeExpr,
        syms: &mut Symbols,
    ) -> R<()> {
        let (start, end) = range_bounds(&range)?;
        let inclusive = range_inclusive(&range);

        let var_loc = self.new_local(Some(var));
        self.lower_into_local(var_loc, &start, syms)?;
        self.bind(var, var_loc);
        let end_loc = self.expr_to_local(&end, syms)?;

        let header = self.fresh_block_id();
        let step = self.fresh_block_id();
        let body = self.fresh_block_id();
        let exit = self.fresh_block_id();
        self.finish_block(Terminator::Goto(header), header);
        let cmp = if inclusive { BinOp::Le } else { BinOp::Lt };
        let cond_tmp = self.new_local(None);
        self.push_stmt(Stmt::Assign(
            Place::local(cond_tmp),
            RValue::Bin(cmp, Operand::Copy(Place::local(var_loc)), Operand::Copy(Place::local(end_loc))),
        ));
        self.finish_block(
            Terminator::Branch { cond: Operand::Copy(Place::local(cond_tmp)), then_blk: body, else_blk: exit },
            body,
        );
        self.push_loop(LoopTargets { continue_to: step, break_to: exit });
        if let Some(b) = node.loop_body() {
            self.lower_block(&b, Dst::Discard, syms)?;
        }
        self.pop_loop();
        if !self.diverged() {
            self.finish_block(Terminator::Goto(step), step);
        } else {
            self.start_block(step);
        }
        self.push_stmt(Stmt::Assign(
            Place::local(var_loc),
            RValue::Bin(BinOp::Add, Operand::Copy(Place::local(var_loc)), Operand::Const(Const::Int(1))),
        ));
        self.finish_block(Terminator::Goto(header), exit);
        Ok(())
    }

    fn lower_break(&mut self) -> R<()> {
        let t = self.innermost_loop().ok_or("`break` outside of a loop")?;
        let dead = self.fresh_block_id();
        self.finish_block(Terminator::Goto(t.break_to), dead);
        self.set_diverged();
        Ok(())
    }
    fn lower_continue(&mut self) -> R<()> {
        let t = self.innermost_loop().ok_or("`continue` outside of a loop")?;
        let dead = self.fresh_block_id();
        self.finish_block(Terminator::Goto(t.continue_to), dead);
        self.set_diverged();
        Ok(())
    }

    // ---- expression lowering ----------------------------------------------

    pub fn lower_into_local(&mut self, dst: LocalId, e: &ast::Expr, syms: &mut Symbols) -> R<()> {
        // A value-position `if`/`match`/block builds a CFG whose branches each
        // assign into `dst`; everything else is a direct r-value.
        if is_value_structured(e) {
            return self.lower_expr_value(e, Dst::Local(dst), syms);
        }
        let rv = self.lower_rvalue(e, syms)?;
        self.push_stmt(Stmt::Assign(Place::local(dst), rv));
        Ok(())
    }

    fn expr_to_local(&mut self, e: &ast::Expr, syms: &mut Symbols) -> R<LocalId> {
        if let Some(sym) = simple_path_name(e, syms) {
            if let Some(id) = self.lookup(sym) {
                return Ok(id);
            }
        }
        let tmp = self.new_local(None);
        self.lower_into_local(tmp, e, syms)?;
        if let Some(adt) = self.adt_of_expr(e, syms) {
            self.set_local_adt(tmp, adt);
        }
        Ok(tmp)
    }

    pub fn lower_rvalue(&mut self, e: &ast::Expr, syms: &mut Symbols) -> R<RValue> {
        match e {
            ast::Expr::BinExpr(b) => {
                let op = bin_op(b).ok_or_else(|| "unsupported binary operator".to_string())?;
                let a = self.lower_operand(&b.lhs().ok_or("bin without lhs")?, syms)?;
                let c = self.lower_operand(&b.rhs().ok_or("bin without rhs")?, syms)?;
                Ok(RValue::Bin(op, a, c))
            }
            ast::Expr::PrefixExpr(p) => self.lower_prefix(p, syms),
            ast::Expr::CallExpr(c) => self.lower_call(c, syms),
            ast::Expr::MethodCallExpr(m) => self.lower_method_call(m, syms),
            ast::Expr::RecordExpr(r) => self.lower_record(r, syms),
            ast::Expr::FieldExpr(_) | ast::Expr::IndexExpr(_) => {
                let place = self.lower_place(e, syms)?;
                Ok(RValue::Use(Operand::Copy(place)))
            }
            ast::Expr::RefExpr(r) => {
                let mutable = r.mut_token().is_some();
                let val = r.expr().ok_or("ref without operand")?;
                let place = self.lower_place(&val, syms)?;
                let kind = if mutable { BorrowKind::Mut } else { BorrowKind::Shared };
                Ok(RValue::Ref(kind, place))
            }
            ast::Expr::ParenExpr(p) => self.lower_rvalue(&p.expr().ok_or("empty paren")?, syms),
            // `e as T` — best-effort: numeric casts lower to the inner value (our
            // int model is value-based; a sized-int target keeps the value, and a
            // checked op on it re-establishes range).
            ast::Expr::CastExpr(c) => self.lower_rvalue(&c.expr().ok_or("cast without operand")?, syms),
            ast::Expr::TupleExpr(t) => {
                let mut ops = Vec::new();
                for f in t.fields() {
                    ops.push(self.lower_operand(&f, syms)?);
                }
                Ok(RValue::Aggregate(rv_ir::AggKind::Tuple, ops))
            }
            ast::Expr::ArrayExpr(a) => self.lower_array(a, syms),
            ast::Expr::TryExpr(t) => {
                let inner = t.expr().ok_or("empty `?`")?;
                let v = self.lower_try(&inner, syms)?;
                Ok(RValue::Use(Operand::Copy(Place::local(v))))
            }
            ast::Expr::PathExpr(_) | ast::Expr::Literal(_) => {
                Ok(RValue::Use(self.lower_operand(e, syms)?))
            }
            ast::Expr::MacroExpr(m) => self.lower_macro_rvalue(m, syms),
            ast::Expr::ClosureExpr(c) => self.lower_closure(c, syms),
            other => Err(format!("unsupported expression `{:?}`", other.syntax().kind())),
        }
    }

    /// Closure conversion: lift `|params| body` to a fresh top-level function whose
    /// leading parameters are the variables it captures from the enclosing scope,
    /// then emit a `Closure` value pairing that function with the captured operands.
    /// At runtime the captures are prepended to the call args (see the VM); in
    /// verification the closure is opaque and an indirect call's result is
    /// unconstrained — sound, no havoc.
    fn lower_closure(&mut self, c: &ast::ClosureExpr, syms: &mut Symbols) -> R<RValue> {
        // Closure parameters (simple identifiers only).
        let mut param_names: Vec<Sym> = Vec::new();
        if let Some(pl) = c.param_list() {
            for p in pl.params() {
                match p.pat() {
                    Some(ast::Pat::IdentPat(ip)) => param_names.push(syms.intern(&ident_pat_name(&ip)?)),
                    _ => return Err("only simple identifier closure parameters are supported".to_string()),
                }
            }
        }
        let body = c.body().ok_or("closure without body")?;

        // Capture set: identifiers free in the body that resolve to an enclosing
        // local, excluding the closure's own parameters. Over-approximating (a name
        // shadowed by an inner `let`) is harmless — the inner binding wins inside.
        let param_set: HashSet<Sym> = param_names.iter().copied().collect();
        let mut captures: Vec<Sym> = Vec::new();
        let mut seen: HashSet<Sym> = HashSet::new();
        for sym in free_idents(&body, syms) {
            if param_set.contains(&sym) || !seen.insert(sym) {
                continue;
            }
            if self.lookup(sym).is_some() {
                captures.push(sym);
            }
        }

        // Build the lifted function: params are `[captures.., closure params..]`.
        let id = self.types.fresh_closure_id();
        let fname = syms.intern(&format!("__closure_{id}"));
        let mut b = FnBuilder::new(self.types);
        if let Some(st) = self.self_ty() {
            b.set_self_ty(st);
        }
        let mut params = Vec::new();
        for &cap in &captures {
            let outer = self.lookup(cap).expect("capture resolves");
            let pid = b.new_local(Some(cap));
            // Propagate the captured local's type markers so method/length/Vec
            // resolution works the same inside the closure body.
            if self.is_vec(outer) {
                b.mark_vec(pid);
            }
            if let Some(adt) = self.local_adt(outer) {
                b.set_local_adt(pid, adt);
            }
            b.bind(cap, pid);
            params.push(pid);
        }
        for &pn in &param_names {
            let pid = b.new_local(Some(pn));
            b.bind(pn, pid);
            params.push(pid);
        }
        // The closure body is the lifted function's implicit return value. A real
        // functional contract for the lifted function (so callers can reason about
        // its result) will come from the kernel's sequence/quantifier work — derived
        // from the body's own IR, not a re-parse — rather than being synthesized
        // here; for now the lifted function carries no contract and an indirect call
        // is sound-but-opaque.
        b.finish_tail(Dst::Return, &body, syms)?;
        b.finish_with_default_return();

        // Drain any nested closures lifted out of this body, then this function.
        let nested = b.take_lifted();
        let (locals, blocks) = b.into_parts();
        let func = Function {
            name: fname,
            type_params: vec![],
            params,
            ret: None,
            pre: Prop::True,
            post: Prop::True,
            locals,
            blocks,
            entry: BlockId(0),
        };
        for f in nested {
            self.push_lifted(f);
        }
        self.push_lifted(func);

        // The closure value captures the enclosing locals by value (the `Closure`
        // r-value reads each at construction time, so later mutation of a source
        // local does not change an already-built closure).
        let cap_ops: Vec<Operand> = captures
            .iter()
            .map(|&cap| Operand::Copy(Place::local(self.lookup(cap).expect("capture resolves"))))
            .collect();
        Ok(RValue::Closure(fname, cap_ops))
    }

    /// A macro in value position. Only `vec![..]` is modeled — it expands to a
    /// real `Vec` aggregate; every other macro fails-first.
    fn lower_macro_rvalue(&mut self, m: &ast::MacroExpr, syms: &mut Symbols) -> R<RValue> {
        let mc = m.macro_call().ok_or("empty macro")?;
        let name = mc
            .path()
            .and_then(|p| p.segment())
            .and_then(|s| s.name_ref())
            .map(|n| n.text().to_string())
            .unwrap_or_default();
        if name != "vec" {
            return Err(format!("unsupported macro `{name}!` in expression position"));
        }
        let tt = mc.token_tree().map(|t| t.syntax().text().to_string()).unwrap_or_default();
        self.lower_vec_macro(strip_delims(&tt), syms)
    }

    /// Expand `vec![a, b, c]` / `vec![x; N]` to a `Vec` aggregate by re-parsing the
    /// macro body as an array literal and lowering its elements in the current
    /// scope — this is exactly what the real `vec!` expansion builds.
    fn lower_vec_macro(&mut self, inner: &str, syms: &mut Symbols) -> R<RValue> {
        let wrapped = format!("fn __m() {{ [{inner}] }}");
        let parse = ra_ap_syntax::SourceFile::parse(&wrapped, ra_ap_syntax::Edition::Edition2021);
        if parse.errors().first().is_some() {
            return Err("could not parse `vec!` contents".to_string());
        }
        let arr = parse
            .tree()
            .syntax()
            .descendants()
            .find_map(ast::ArrayExpr::cast)
            .ok_or("`vec!` contents are not a list")?;
        let exprs: Vec<ast::Expr> = arr.exprs().collect();
        if arr.semicolon_token().is_some() {
            let elem = exprs.first().ok_or("`vec!` repeat needs an element")?;
            let n = exprs
                .get(1)
                .and_then(super::types::int_literal_usize)
                .ok_or("`vec!` repeat length must be an integer literal")?;
            let op = self.lower_operand(elem, syms)?;
            let ops = std::iter::repeat(op).take(n).collect();
            Ok(RValue::Aggregate(rv_ir::AggKind::Vec, ops))
        } else {
            let mut ops = Vec::new();
            for e in &exprs {
                ops.push(self.lower_operand(e, syms)?);
            }
            Ok(RValue::Aggregate(rv_ir::AggKind::Vec, ops))
        }
    }

    fn lower_prefix(&mut self, p: &ast::PrefixExpr, syms: &mut Symbols) -> R<RValue> {
        let inner = p.expr().ok_or("prefix without operand")?;
        match p.op_kind() {
            Some(ast::UnaryOp::Neg) => Ok(RValue::Un(UnOp::Neg, self.lower_operand(&inner, syms)?)),
            Some(ast::UnaryOp::Not) => Ok(RValue::Un(UnOp::Not, self.lower_operand(&inner, syms)?)),
            Some(ast::UnaryOp::Deref) => {
                let place = self.lower_place(&ast::Expr::PrefixExpr(p.clone()), syms)?;
                Ok(RValue::Use(Operand::Copy(place)))
            }
            None => Err("unsupported prefix operator".to_string()),
        }
    }

    fn lower_call(&mut self, c: &ast::CallExpr, syms: &mut Symbols) -> R<RValue> {
        let callee = c.expr().ok_or("call without callee")?;
        let args: Vec<ast::Expr> = c.arg_list().map(|a| a.args().collect()).unwrap_or_default();
        // Path callee: free function, enum ctor, assoc fn, or `Vec::new`.
        let ast::Expr::PathExpr(pe) = &callee else {
            return Err("unsupported call target".to_string());
        };
        let path = pe.path().ok_or("call path missing")?;
        let segs = path_segments(&path);
        if segs.len() == 1 {
            // Free function `f(args)`.
            let name = syms.intern(&segs[0]);
            if let Some(op) = wrapping_op(&segs[0]) {
                if args.len() == 2 {
                    let a = self.lower_operand(&args[0], syms)?;
                    let b = self.lower_operand(&args[1], syms)?;
                    return Ok(RValue::WrappingBin(op, a, b));
                }
            }
            // Unqualified enum-variant constructor (`Some(x)`, `Ok(v)`, ...).
            if let Some(en) = self.types.variant_enum(name) {
                return self.lower_enum_ctor(en, name, &args, syms);
            }
            // A local in scope holds a closure value: dispatch indirectly.
            if let Some(local) = self.lookup(name) {
                let mut ops = Vec::new();
                for a in &args {
                    ops.push(self.lower_operand(a, syms)?);
                }
                return Ok(RValue::CallClosure(Operand::Copy(Place::local(local)), ops));
            }
            let mut ops = Vec::new();
            for a in &args {
                ops.push(self.lower_operand(a, syms)?);
            }
            return Ok(RValue::Call(name, ops));
        }
        // `Head::tail(args)` (`Self::` resolves to the impl type).
        let head = self.type_name(&segs[segs.len() - 2], syms);
        let tail = syms.intern(&segs[segs.len() - 1]);
        if syms.resolve(head) == "Vec" && matches!(syms.resolve(tail), "new" | "with_capacity") {
            return Ok(RValue::Aggregate(rv_ir::AggKind::Vec, Vec::new()));
        }
        if let Some(info) = self.types.enum_info(head) {
            if info.variant_index.contains_key(&tail) {
                return self.lower_enum_ctor(head, tail, &args, syms);
            }
        }
        let callee_sym = self.mangle(head, tail, syms).unwrap_or(tail);
        let mut ops = Vec::new();
        for a in &args {
            ops.push(self.lower_operand(a, syms)?);
        }
        Ok(RValue::Call(callee_sym, ops))
    }

    fn lower_method_call(&mut self, m: &ast::MethodCallExpr, syms: &mut Symbols) -> R<RValue> {
        let recv = m.receiver().ok_or("method call without receiver")?;
        let method = m.name_ref().ok_or("method call without name")?.text().to_string();
        let args: Vec<ast::Expr> = m.arg_list().map(|a| a.args().collect()).unwrap_or_default();

        // Wrapping intrinsics.
        if let Some(op) = wrapping_op(&method) {
            if args.len() == 1 {
                let a = self.lower_operand(&recv, syms)?;
                let b = self.lower_operand(&args[0], syms)?;
                return Ok(RValue::WrappingBin(op, a, b));
            }
        }
        // Vec intrinsics on a known vector local.
        if let Some(vloc) = self.vec_local_of(&recv, syms) {
            match method.as_str() {
                "len" => return Ok(RValue::VecLen(Operand::Copy(Place::local(vloc)))),
                "push" => {
                    if args.len() == 1 {
                        let x = self.lower_operand(&args[0], syms)?;
                        self.push_stmt(Stmt::Assign(
                            Place::local(vloc),
                            RValue::VecPush(Operand::Copy(Place::local(vloc)), x),
                        ));
                        return Ok(RValue::Use(Operand::Const(Const::Unit)));
                    }
                }
                _ => {}
            }
        }
        // Option/Result combinators.
        if let Some(kind) = combinator_kind(&method) {
            if let Some(adt) = self.adt_of_expr(&recv, syms) {
                if self.types.try_shape(adt, syms).is_ok() {
                    let v = self.lower_combinator(&recv, kind, &args, syms)?;
                    return Ok(RValue::Use(Operand::Copy(Place::local(v))));
                }
            }
        }
        // User method: desugar to `Type::method(recv, args)`.
        let method_sym = syms.intern(&method);
        let adt = self
            .adt_of_expr(&recv, syms)
            .ok_or_else(|| format!("cannot resolve receiver type of `.{method}(..)`"))?;
        let mangled = self
            .mangle(adt, method_sym, syms)
            .ok_or_else(|| format!("no method `{method}` for `{}`", syms.resolve(adt)))?;
        let mut ops = vec![self.lower_operand(&recv, syms)?];
        for a in &args {
            ops.push(self.lower_operand(a, syms)?);
        }
        Ok(RValue::Call(mangled, ops))
    }

    fn lower_record(&mut self, r: &ast::RecordExpr, syms: &mut Symbols) -> R<RValue> {
        let path = r.path().ok_or("record without path")?;
        let last = path_last(&path)?;
        // Enum record-variant construction is unsupported; this is a struct literal.
        let name = self.type_name(&last, syms);
        let info = self
            .types
            .struct_info(name)
            .ok_or_else(|| format!("unknown struct `{last}`"))?;
        let n = info.fields.len();
        let field_index = info.field_index.clone();
        let mut slots: Vec<Option<Operand>> = (0..n).map(|_| None).collect();
        if let Some(fl) = r.record_expr_field_list() {
            for f in fl.fields() {
                let fname = f
                    .field_name()
                    .map(|n| n.to_string())
                    .ok_or("record field without name")?;
                let fsym = syms.intern(&fname);
                let idx = *field_index
                    .get(&fsym)
                    .ok_or_else(|| format!("struct `{last}` has no field `{fname}`"))? as usize;
                let val = f.expr().ok_or("record field without value")?;
                slots[idx] = Some(self.lower_operand(&val, syms)?);
            }
        }
        let mut ops = Vec::with_capacity(n);
        for (i, slot) in slots.into_iter().enumerate() {
            match slot {
                Some(op) => ops.push(op),
                None => {
                    let missing = info.fields[i];
                    return Err(format!("missing field `{}` in `{last}` literal", syms.resolve(missing)));
                }
            }
        }
        Ok(RValue::Aggregate(rv_ir::AggKind::Struct(name), ops))
    }

    fn lower_enum_ctor(&mut self, enum_name: Sym, variant: Sym, args: &[ast::Expr], syms: &mut Symbols) -> R<RValue> {
        let info = self.types.enum_info(enum_name).ok_or("unknown enum")?;
        let (vidx, arity) = *info.variant_index.get(&variant).ok_or("unknown variant")?;
        if args.len() as u32 != arity {
            return Err(format!("variant `{}` expects {arity} field(s), got {}", syms.resolve(variant), args.len()));
        }
        let mut ops = Vec::new();
        for a in args {
            ops.push(self.lower_operand(a, syms)?);
        }
        Ok(RValue::Aggregate(rv_ir::AggKind::Variant(enum_name, vidx), ops))
    }

    /// Lower an expression that denotes a place (variable / field / index / deref).
    pub fn lower_place(&mut self, e: &ast::Expr, syms: &mut Symbols) -> R<Place> {
        match e {
            ast::Expr::PathExpr(_) => {
                let sym = simple_path_name(e, syms).ok_or("non-local path in place")?;
                let id = self.lookup(sym).ok_or_else(|| format!("unbound variable `{}`", syms.resolve(sym)))?;
                Ok(Place::local(id))
            }
            ast::Expr::FieldExpr(fe) => {
                let base = fe.expr().ok_or("field access without base")?;
                let mut place = self.lower_place(&base, syms)?;
                if let Some(nr) = fe.name_ref() {
                    // Named struct field, or a tuple index like `.0`.
                    let text = nr.text().to_string();
                    if let Ok(n) = text.parse::<u32>() {
                        place.proj.push(Proj::Field(n));
                    } else {
                        let base_struct = self
                            .adt_of_expr(&base, syms)
                            .ok_or("cannot resolve struct of field base")?;
                        let info = self
                            .types
                            .struct_info(base_struct)
                            .ok_or_else(|| format!("`{}` is not a struct", syms.resolve(base_struct)))?;
                        let fsym = syms.intern(&text);
                        let idx = *info
                            .field_index
                            .get(&fsym)
                            .ok_or_else(|| format!("struct `{}` has no field `{text}`", syms.resolve(base_struct)))?;
                        place.proj.push(Proj::Field(idx));
                    }
                }
                Ok(place)
            }
            ast::Expr::IndexExpr(ie) => {
                let base = ie.base().ok_or("index without base")?;
                let idx = ie.index().ok_or("index without index")?;
                let mut place = self.lower_place(&base, syms)?;
                let idx_op = self.lower_operand(&idx, syms)?;
                place.proj.push(Proj::Index(idx_op));
                Ok(place)
            }
            ast::Expr::PrefixExpr(p) if matches!(p.op_kind(), Some(ast::UnaryOp::Deref)) => {
                let inner = p.expr().ok_or("deref without operand")?;
                let mut place = self.lower_place(&inner, syms)?;
                place.proj.push(Proj::Deref);
                Ok(place)
            }
            ast::Expr::ParenExpr(p) => self.lower_place(&p.expr().ok_or("empty paren")?, syms),
            _ => {
                let tmp = self.new_local(None);
                self.lower_into_local(tmp, e, syms)?;
                if let Some(adt) = self.adt_of_expr(e, syms) {
                    self.set_local_adt(tmp, adt);
                }
                Ok(Place::local(tmp))
            }
        }
    }

    pub fn lower_operand(&mut self, e: &ast::Expr, syms: &mut Symbols) -> R<Operand> {
        match e {
            ast::Expr::Literal(lit) => lower_literal(lit),
            ast::Expr::PathExpr(_) => {
                if let Some(sym) = simple_path_name(e, syms) {
                    if let Some(id) = self.lookup(sym) {
                        return Ok(Operand::Copy(Place::local(id)));
                    }
                    // A bare path that isn't a local: a unit enum ctor (`E::V`)?
                    return self.lower_path_value(e, syms);
                }
                self.lower_path_value(e, syms)
            }
            ast::Expr::FieldExpr(_) | ast::Expr::IndexExpr(_) => Ok(Operand::Copy(self.lower_place(e, syms)?)),
            ast::Expr::PrefixExpr(p) if matches!(p.op_kind(), Some(ast::UnaryOp::Deref)) => {
                Ok(Operand::Copy(self.lower_place(e, syms)?))
            }
            ast::Expr::ParenExpr(p) => self.lower_operand(&p.expr().ok_or("empty paren")?, syms),
            ast::Expr::CastExpr(c) => self.lower_operand(&c.expr().ok_or("cast without operand")?, syms),
            // Anything else (calls, a value-position `if`/`match`) goes through a
            // temporary; `lower_into_local` routes structured exprs to their CFG
            // and errors on genuinely-unsupported expressions.
            _ => {
                let tmp = self.new_local(None);
                self.lower_into_local(tmp, e, syms)?;
                if let Some(adt) = self.adt_of_expr(e, syms) {
                    self.set_local_adt(tmp, adt);
                }
                Ok(Operand::Copy(Place::local(tmp)))
            }
        }
    }

    /// A path used as a value: a multi-segment unit enum constructor (`E::V`).
    fn lower_path_value(&mut self, e: &ast::Expr, syms: &mut Symbols) -> R<Operand> {
        let ast::Expr::PathExpr(pe) = e else { return Err("expected a path".to_string()) };
        let path = pe.path().ok_or("empty path")?;
        let segs = path_segments(&path);
        // A unit enum constructor: qualified `E::V` / `Self::V`, or unqualified `V`.
        let pair = if segs.len() >= 2 {
            Some((self.type_name(&segs[segs.len() - 2], syms), syms.intern(&segs[segs.len() - 1])))
        } else if segs.len() == 1 {
            let v = syms.intern(&segs[0]);
            self.types.variant_enum(v).map(|en| (en, v))
        } else {
            None
        };
        if let Some((head, tail)) = pair {
            if let Some(info) = self.types.enum_info(head) {
                if info.variant_index.contains_key(&tail) {
                    let rv = self.lower_enum_ctor(head, tail, &[], syms)?;
                    let tmp = self.new_local(None);
                    self.push_stmt(Stmt::Assign(Place::local(tmp), rv));
                    self.set_local_adt(tmp, head);
                    return Ok(Operand::Copy(Place::local(tmp)));
                }
            }
        }
        Err(format!("unbound variable `{}`", segs.join("::")))
    }

    // ---- best-effort ADT tracking -----------------------------------------

    pub fn adt_of_expr(&self, e: &ast::Expr, syms: &mut Symbols) -> Option<Sym> {
        match e {
            ast::Expr::RecordExpr(r) => Some(self.type_name(&path_last(&r.path()?).ok()?, syms)),
            ast::Expr::PathExpr(_) => {
                if let Some(sym) = simple_path_name(e, syms) {
                    if let Some(id) = self.lookup(sym) {
                        return self.local_adt(id);
                    }
                }
                // A variant value (`E::V`, `Self::V`, or unqualified `V`): its enum.
                let ast::Expr::PathExpr(pe) = e else { return None };
                self.variant_of_path(&pe.path()?, syms).map(|(en, _)| en)
            }
            ast::Expr::CallExpr(c) => {
                let ast::Expr::PathExpr(pe) = c.expr()? else { return None };
                let segs = path_segments(&pe.path()?);
                if segs.len() == 1 {
                    let name = syms.intern(&segs[0]);
                    // Unqualified variant ctor -> its enum; else a free fn's ret ADT.
                    return self.types.variant_enum(name).or_else(|| self.types.fn_ret(name));
                }
                let head = self.type_name(&segs[segs.len() - 2], syms);
                let tail = syms.intern(&segs[segs.len() - 1]);
                if self.types.is_adt(head) {
                    return Some(head); // enum ctor / assoc result ADT
                }
                self.types.fn_ret(tail)
            }
            ast::Expr::MethodCallExpr(m) => {
                let recv = m.receiver()?;
                let method = syms.intern(&m.name_ref()?.text().to_string());
                let recv_adt = self.adt_of_expr(&recv, syms)?;
                let mangled = self.mangle(recv_adt, method, syms)?;
                self.types.fn_ret(mangled)
            }
            ast::Expr::ParenExpr(p) => self.adt_of_expr(&p.expr()?, syms),
            _ => None,
        }
    }

    fn vec_local_of(&self, recv: &ast::Expr, syms: &mut Symbols) -> Option<LocalId> {
        let sym = simple_path_name(recv, syms)?;
        let id = self.lookup(sym)?;
        self.is_vec(id).then_some(id)
    }

    /// The sequence (Vec/slice/array) local that an iterable expression iterates
    /// over: a bare sequence local, or one viewed through the identity adapters
    /// `.iter()` / `.iter_mut()` / `.into_iter()` / `&` / `&mut`.
    fn seq_local_of(&self, e: &ast::Expr, syms: &mut Symbols) -> Option<LocalId> {
        match e {
            ast::Expr::MethodCallExpr(m) => {
                let method = m.name_ref()?.text().to_string();
                if matches!(method.as_str(), "iter" | "iter_mut" | "into_iter") {
                    self.seq_local_of(&m.receiver()?, syms)
                } else {
                    None
                }
            }
            ast::Expr::RefExpr(r) => self.seq_local_of(&r.expr()?, syms),
            ast::Expr::ParenExpr(p) => self.seq_local_of(&p.expr()?, syms),
            _ => self.vec_local_of(e, syms),
        }
    }

    fn mangle(&self, adt: Sym, method: Sym, syms: &mut Symbols) -> Option<Sym> {
        if !self.types.is_adt(adt) {
            return None;
        }
        let s = format!("{}::{}", syms.resolve(adt), syms.resolve(method));
        Some(syms.intern(&s))
    }

    /// Resolve a type-name path segment, mapping `Self` to the impl type.
    fn type_name(&self, text: &str, syms: &mut Symbols) -> Sym {
        if text == "Self" {
            if let Some(s) = self.self_ty() {
                return s;
            }
        }
        syms.intern(text)
    }

    /// Resolve a variant path to `(enum, variant)`: qualified `E::V` / `Self::V`,
    /// or an unqualified `V` looked up in the variant→enum index.
    fn variant_of_path(&self, path: &ast::Path, syms: &mut Symbols) -> Option<(Sym, Sym)> {
        let segs = path_segments(path);
        if segs.len() >= 2 {
            Some((self.type_name(&segs[segs.len() - 2], syms), syms.intern(&segs[segs.len() - 1])))
        } else if segs.len() == 1 {
            let v = syms.intern(&segs[0]);
            self.types.variant_enum(v).map(|en| (en, v))
        } else {
            None
        }
    }
}

// ============================ free helpers ================================

#[derive(Clone, Copy)]
enum Combinator {
    Unwrap,
    UnwrapOr,
    IsSuccess,
    IsFailure,
}
fn combinator_kind(name: &str) -> Option<Combinator> {
    Some(match name {
        "unwrap" | "expect" => Combinator::Unwrap,
        "unwrap_or" => Combinator::UnwrapOr,
        "is_some" | "is_ok" => Combinator::IsSuccess,
        "is_none" | "is_err" => Combinator::IsFailure,
        _ => return None,
    })
}
fn wrapping_op(name: &str) -> Option<BinOp> {
    Some(match name {
        "wrapping_add" => BinOp::Add,
        "wrapping_sub" => BinOp::Sub,
        "wrapping_mul" => BinOp::Mul,
        "wrapping_div" => BinOp::Div,
        "wrapping_rem" => BinOp::Mod,
        _ => return None,
    })
}

impl FnBuilder<'_> {
    fn lower_combinator(&mut self, recv: &ast::Expr, kind: Combinator, args: &[ast::Expr], syms: &mut Symbols) -> R<LocalId> {
        let s = self.expr_to_local(recv, syms)?;
        let enum_name = self.local_adt(s).ok_or("combinator receiver must be a known Option/Result value")?;
        let shape = self.types.try_shape(enum_name, syms)?;
        let success_id = self.fresh_block_id();
        let failure_id = self.fresh_block_id();
        let join_id = self.fresh_block_id();
        let v = self.new_local(None);
        self.finish_block(
            Terminator::Match {
                scrutinee: Operand::Copy(Place::local(s)),
                arms: vec![
                    rv_ir::MatchArm { variant: shape.success_idx, target: success_id },
                    rv_ir::MatchArm { variant: shape.failure_idx, target: failure_id },
                ],
                otherwise: None,
            },
            success_id,
        );
        let payload = Place { local: s, proj: vec![Proj::Downcast(shape.success_idx), Proj::Field(0)] };
        match kind {
            Combinator::Unwrap | Combinator::UnwrapOr => {
                self.push_stmt(Stmt::Assign(Place::local(v), RValue::Use(Operand::Copy(payload))));
            }
            Combinator::IsSuccess => {
                self.push_stmt(Stmt::Assign(Place::local(v), RValue::Use(Operand::Const(Const::Bool(true)))));
            }
            Combinator::IsFailure => {
                self.push_stmt(Stmt::Assign(Place::local(v), RValue::Use(Operand::Const(Const::Bool(false)))));
            }
        }
        self.finish_block(Terminator::Goto(join_id), failure_id);
        match kind {
            Combinator::Unwrap => {
                let dead = self.fresh_block_id();
                self.finish_block(Terminator::Panic, dead);
            }
            Combinator::UnwrapOr => {
                let d = self.lower_operand(args.first().ok_or("`unwrap_or` needs a default")?, syms)?;
                self.push_stmt(Stmt::Assign(Place::local(v), RValue::Use(d)));
                self.finish_block(Terminator::Goto(join_id), join_id);
            }
            Combinator::IsSuccess => {
                self.push_stmt(Stmt::Assign(Place::local(v), RValue::Use(Operand::Const(Const::Bool(false)))));
                self.finish_block(Terminator::Goto(join_id), join_id);
            }
            Combinator::IsFailure => {
                self.push_stmt(Stmt::Assign(Place::local(v), RValue::Use(Operand::Const(Const::Bool(true)))));
                self.finish_block(Terminator::Goto(join_id), join_id);
            }
        }
        if self.cur_id() != join_id {
            self.start_block(join_id);
        }
        Ok(v)
    }
}

/// A resolved variant pattern.
struct MatchPat {
    variant_idx: u32,
    binds: Vec<Option<Sym>>,
}

impl FnBuilder<'_> {
    fn lower_array(&mut self, a: &ast::ArrayExpr, syms: &mut Symbols) -> R<RValue> {
        let exprs: Vec<ast::Expr> = a.exprs().collect();
        if a.semicolon_token().is_some() {
            // `[elem; N]`
            let elem = exprs.first().ok_or("array repeat needs an element")?;
            let n = exprs
                .get(1)
                .and_then(super::types::int_literal_usize)
                .ok_or("array length must be an integer literal")?;
            let op = self.lower_operand(elem, syms)?;
            let ops = std::iter::repeat(op).take(n).collect();
            Ok(RValue::Aggregate(rv_ir::AggKind::Array, ops))
        } else {
            let mut ops = Vec::new();
            for e in &exprs {
                ops.push(self.lower_operand(e, syms)?);
            }
            Ok(RValue::Aggregate(rv_ir::AggKind::Array, ops))
        }
    }

    /// `e?` — match the Result/Option value, bind the success payload, and
    /// early-return the re-aggregated failure.
    fn lower_try(&mut self, inner: &ast::Expr, syms: &mut Symbols) -> R<LocalId> {
        let s = self.expr_to_local(inner, syms)?;
        let enum_name = self.local_adt(s).ok_or("cannot resolve the enum type of a `?` operand")?;
        let shape = self.types.try_shape(enum_name, syms)?;
        let success_id = self.fresh_block_id();
        let failure_id = self.fresh_block_id();
        let cont_id = self.fresh_block_id();
        let v = self.new_local(None);
        self.finish_block(
            Terminator::Match {
                scrutinee: Operand::Copy(Place::local(s)),
                arms: vec![
                    rv_ir::MatchArm { variant: shape.success_idx, target: success_id },
                    rv_ir::MatchArm { variant: shape.failure_idx, target: failure_id },
                ],
                otherwise: None,
            },
            success_id,
        );
        let payload = Place { local: s, proj: vec![Proj::Downcast(shape.success_idx), Proj::Field(0)] };
        self.push_stmt(Stmt::Assign(Place::local(v), RValue::Use(Operand::Copy(payload))));
        self.finish_block(Terminator::Goto(cont_id), failure_id);
        let mut fail_ops = Vec::new();
        if shape.failure_arity == 1 {
            let fp = Place { local: s, proj: vec![Proj::Downcast(shape.failure_idx), Proj::Field(0)] };
            fail_ops.push(Operand::Copy(fp));
        }
        let fail_local = self.new_local(None);
        self.set_local_adt(fail_local, enum_name);
        self.push_stmt(Stmt::Assign(
            Place::local(fail_local),
            RValue::Aggregate(rv_ir::AggKind::Variant(enum_name, shape.failure_idx), fail_ops),
        ));
        self.finish_block(Terminator::Return(Operand::Copy(Place::local(fail_local))), cont_id);
        Ok(v)
    }

    fn lower_match(&mut self, node: &ast::MatchExpr, dst: Dst, syms: &mut Symbols) -> R<()> {
        let scrut = node.expr().ok_or("match without scrutinee")?;
        let scrut_local = self.expr_to_local(&scrut, syms)?;
        let join_id = self.fresh_block_id();
        let arms: Vec<ast::MatchArm> =
            node.match_arm_list().map(|l| l.arms().collect()).unwrap_or_default();

        let mut ir_arms = Vec::new();
        let mut otherwise = None;
        let mut planned: Vec<(BlockId, ast::MatchArm, Option<MatchPat>)> = Vec::new();
        for arm in &arms {
            let target = self.fresh_block_id();
            let mp = self.parse_match_pat(arm, syms)?;
            match &mp {
                None => {
                    if otherwise.is_some() {
                        return Err("duplicate catch-all arm in match".to_string());
                    }
                    otherwise = Some(target);
                }
                Some(p) => ir_arms.push(rv_ir::MatchArm { variant: p.variant_idx, target }),
            }
            planned.push((target, arm.clone(), mp));
        }
        let first_target = planned.first().map(|(id, ..)| *id).unwrap_or(join_id);
        self.finish_block(
            Terminator::Match {
                scrutinee: Operand::Copy(Place::local(scrut_local)),
                arms: ir_arms,
                otherwise,
            },
            first_target,
        );
        for (i, (target, arm, mp)) in planned.iter().enumerate() {
            if self.cur_id() != *target {
                self.start_block(*target);
            }
            if let Some(p) = mp {
                self.bind_pattern_fields(scrut_local, p, syms);
            }
            // `Pat => body` directs the arm's value to the match's destination: a
            // block lowers in place, a bare expr is the arm value.
            match arm.expr().ok_or("match arm without body")? {
                ast::Expr::BlockExpr(b) => self.lower_block(&b, dst, syms)?,
                other => self.finish_tail(dst, &other, syms)?,
            }
            let next = planned.get(i + 1).map(|(id, ..)| *id).unwrap_or(join_id);
            if !self.diverged() {
                self.finish_block(Terminator::Goto(join_id), next);
            } else {
                self.start_block(next);
            }
        }
        if self.cur_id() != join_id {
            self.start_block(join_id);
        }
        Ok(())
    }

    fn parse_match_pat(&self, arm: &ast::MatchArm, syms: &mut Symbols) -> R<Option<MatchPat>> {
        self.parse_pat(&arm.pat().ok_or("match arm without pattern")?, syms)
    }

    /// Resolve a pattern to a refutable variant test (`None` = always matches:
    /// wildcard or a plain binder). Shared by `match` arms and `if let`.
    fn parse_pat(&self, pat: &ast::Pat, syms: &mut Symbols) -> R<Option<MatchPat>> {
        match pat {
            ast::Pat::WildcardPat(_) => Ok(None),
            // A bare identifier is ambiguous: a unit-variant pattern (`North`) if
            // the name is a known variant, otherwise an irrefutable binder.
            ast::Pat::IdentPat(ip) => {
                let name = syms.intern(&ident_pat_name(ip)?);
                match self.types.variant_enum(name) {
                    Some(en) => self.resolve_variant(en, name, Vec::new(), syms),
                    None => Ok(None),
                }
            }
            ast::Pat::TupleStructPat(tsp) => {
                let path = tsp.path().ok_or("variant pattern without path")?;
                let (en, var) = self.variant_of_path(&path, syms).ok_or("could not resolve variant pattern")?;
                let mut binds = Vec::new();
                for f in tsp.fields() {
                    match f {
                        ast::Pat::IdentPat(ip) => binds.push(Some(syms.intern(&ident_pat_name(&ip)?))),
                        ast::Pat::WildcardPat(_) => binds.push(None),
                        _ => return Err("unsupported binder in variant pattern".to_string()),
                    }
                }
                self.resolve_variant(en, var, binds, syms)
            }
            ast::Pat::PathPat(pp) => {
                let path = pp.path().ok_or("path pattern without path")?;
                let (en, var) = self.variant_of_path(&path, syms).ok_or("could not resolve variant pattern")?;
                self.resolve_variant(en, var, Vec::new(), syms)
            }
            other => Err(format!("unsupported match pattern `{:?}`", other.syntax().kind())),
        }
    }

    fn resolve_variant(&self, en: Sym, var: Sym, binds: Vec<Option<Sym>>, syms: &Symbols) -> R<Option<MatchPat>> {
        let info = self.types.enum_info(en).ok_or_else(|| format!("unknown enum `{}` in pattern", syms.resolve(en)))?;
        let (vidx, arity) = *info
            .variant_index
            .get(&var)
            .ok_or_else(|| format!("unknown variant `{}` of `{}`", syms.resolve(var), syms.resolve(en)))?;
        if !binds.is_empty() && binds.len() as u32 != arity {
            return Err(format!("variant `{}` binds {arity} field(s) but pattern has {}", syms.resolve(var), binds.len()));
        }
        let _ = en;
        Ok(Some(MatchPat { variant_idx: vidx, binds }))
    }

    fn bind_pattern_fields(&mut self, scrut_local: LocalId, mp: &MatchPat, syms: &mut Symbols) {
        let _ = syms;
        for (i, b) in mp.binds.iter().enumerate() {
            let Some(name) = b else { continue };
            let dst = self.new_local(Some(*name));
            let src = Place {
                local: scrut_local,
                proj: vec![Proj::Downcast(mp.variant_idx), Proj::Field(i as u32)],
            };
            self.push_stmt(Stmt::Assign(Place::local(dst), RValue::Use(Operand::Copy(src))));
            self.bind(*name, dst);
        }
    }

    fn lower_macro_stmt(&mut self, m: &ast::MacroExpr, syms: &mut Symbols) -> R<()> {
        let mc = m.macro_call().ok_or("empty macro")?;
        let name = mc
            .path()
            .and_then(|p| p.segment())
            .and_then(|s| s.name_ref())
            .map(|n| n.text().to_string())
            .unwrap_or_default();
        let tt = mc.token_tree().map(|t| t.syntax().text().to_string()).unwrap_or_default();
        let inner = strip_delims(&tt);
        match name.as_str() {
            "panic" | "unreachable" | "todo" | "unimplemented" => {
                let dead = self.fresh_block_id();
                self.finish_block(Terminator::Panic, dead);
                self.set_diverged();
                Ok(())
            }
            "assert" => {
                let cond = first_macro_arg(&inner);
                let prop = super::spec::parse_prop(cond, syms).map_err(|e| format!("in `assert!`: {e}"))?;
                self.push_stmt(Stmt::Assert(prop));
                Ok(())
            }
            "assert_eq" | "assert_ne" => {
                let (a, b) = two_macro_args(&inner).ok_or_else(|| format!("`{name}!` needs two arguments"))?;
                let op = if name == "assert_eq" { "==" } else { "!=" };
                let expr = format!("({a}) {op} ({b})");
                let prop = super::spec::parse_prop(&expr, syms).map_err(|e| format!("in `{name}!`: {e}"))?;
                self.push_stmt(Stmt::Assert(prop));
                Ok(())
            }
            _ => Ok(()), // ignore `println!` etc.
        }
    }
}


/// Strip one outer pair of `()`/`[]`/`{}` delimiters from a token-tree's text.
fn strip_delims(s: &str) -> &str {
    let s = s.trim();
    for (o, c) in [('(', ')'), ('[', ']'), ('{', '}')] {
        if let Some(r) = s.strip_prefix(o).and_then(|r| r.strip_suffix(c)) {
            return r.trim();
        }
    }
    s
}
fn first_macro_arg(s: &str) -> &str {
    split_top_commas(s).into_iter().next().unwrap_or(s).trim()
}
fn two_macro_args(s: &str) -> Option<(&str, &str)> {
    let parts = split_top_commas(s);
    if parts.len() < 2 {
        return None;
    }
    Some((parts[0].trim(), parts[1].trim()))
}
fn split_top_commas(s: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let (mut depth, mut start, mut in_str) = (0i32, 0usize, false);
    for (i, &b) in s.as_bytes().iter().enumerate() {
        match b {
            b'"' => in_str = !in_str,
            b'(' | b'[' | b'{' if !in_str => depth += 1,
            b')' | b']' | b'}' if !in_str => depth -= 1,
            b',' if depth == 0 && !in_str => {
                out.push(&s[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(&s[start..]);
    out
}

fn lower_literal(lit: &ast::Literal) -> R<Operand> {
    match lit.kind() {
        ast::LiteralKind::IntNumber(n) => {
            let v = n.value().map_err(|_| "bad integer literal".to_string())?;
            Ok(Operand::Const(Const::Int(v as i64)))
        }
        ast::LiteralKind::Bool(b) => Ok(Operand::Const(Const::Bool(b))),
        other => Err(format!("unsupported literal `{other:?}`")),
    }
}

/// Whether a structured expression must be lowered as a statement (CFG built)
/// when it appears in statement / tail position.
fn is_structured(e: &ast::Expr) -> bool {
    matches!(
        e,
        ast::Expr::IfExpr(_)
            | ast::Expr::WhileExpr(_)
            | ast::Expr::LoopExpr(_)
            | ast::Expr::ForExpr(_)
            | ast::Expr::BreakExpr(_)
            | ast::Expr::ContinueExpr(_)
            | ast::Expr::BlockExpr(_)
            | ast::Expr::MatchExpr(_)
            | ast::Expr::MacroExpr(_)
    )
}

/// Structured expressions that can yield a value in value position (`let x = …`,
/// operand of a call/operator). Loops and `break`/`continue` are excluded.
fn is_value_structured(e: &ast::Expr) -> bool {
    matches!(
        e,
        ast::Expr::IfExpr(_) | ast::Expr::MatchExpr(_) | ast::Expr::BlockExpr(_)
    )
}

fn is_assign(b: &ast::BinExpr) -> bool {
    matches!(b.op_kind(), Some(ast::BinaryOp::Assignment { .. }))
}

/// Every single-segment path identifier appearing anywhere in `body` — the
/// candidate set for closure captures. Multi-segment paths (`E::V`, `Type::f`) are
/// type/function references, not local captures, so they are skipped. The caller
/// intersects this with the enclosing scope's locals to find the real captures.
fn free_idents(body: &ast::Expr, syms: &mut Symbols) -> Vec<Sym> {
    let mut out = Vec::new();
    for node in body.syntax().descendants() {
        let Some(pe) = ast::PathExpr::cast(node) else { continue };
        let Some(path) = pe.path() else { continue };
        if path.qualifier().is_some() {
            continue;
        }
        if let Some(name) = path.segment().and_then(|s| s.name_ref()) {
            out.push(syms.intern(&name.text().to_string()));
        }
    }
    out
}

/// The interned name of a single-segment path expression (a plain variable).
fn simple_path_name(e: &ast::Expr, syms: &mut Symbols) -> Option<Sym> {
    let ast::Expr::PathExpr(pe) = e else { return None };
    let path = pe.path()?;
    if path.qualifier().is_some() {
        return None;
    }
    let name = path.segment()?.name_ref()?.text().to_string();
    Some(syms.intern(&name))
}

fn path_segments(path: &ast::Path) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = Some(path.clone());
    while let Some(p) = cur {
        if let Some(seg) = p.segment() {
            if let Some(nr) = seg.name_ref() {
                out.push(nr.text().to_string());
            }
        }
        cur = p.qualifier();
    }
    out.reverse();
    out
}

fn path_last(path: &ast::Path) -> R<String> {
    path.segment()
        .and_then(|s| s.name_ref())
        .map(|n| n.text().to_string())
        .ok_or_else(|| "path without a final segment".to_string())
}

fn ident_pat_name(ip: &ast::IdentPat) -> R<String> {
    ip.name().map(|n| n.text().to_string()).ok_or_else(|| "binding without a name".to_string())
}

fn is_vec_ty(ty: &ast::Type) -> bool {
    if let ast::Type::PathType(p) = ty {
        if let Some(seg) = p.path().and_then(|p| p.segment()) {
            return seg.name_ref().map(|n| n.text() == "Vec").unwrap_or(false);
        }
    }
    false
}

fn expr_yields_vec(e: &ast::Expr) -> bool {
    match e {
        ast::Expr::CallExpr(c) => {
            let Some(ast::Expr::PathExpr(pe)) = c.expr() else { return false };
            let Some(path) = pe.path() else { return false };
            path_segments(&path).first().map(|s| s == "Vec").unwrap_or(false)
        }
        // `vec![..]` yields a `Vec`.
        ast::Expr::MacroExpr(m) => m
            .macro_call()
            .and_then(|mc| mc.path())
            .and_then(|p| p.segment())
            .and_then(|s| s.name_ref())
            .map(|n| n.text() == "vec")
            .unwrap_or(false),
        _ => false,
    }
}

fn range_bounds(r: &ast::RangeExpr) -> R<(ast::Expr, ast::Expr)> {
    // RangeExpr exposes start/end via its two operand expressions.
    let mut it = r.syntax().children().filter_map(ast::Expr::cast);
    let start = it.next().ok_or("range without start")?;
    let end = it.next().ok_or("`for` needs a bounded range `a..b`")?;
    Ok((start, end))
}
fn range_inclusive(r: &ast::RangeExpr) -> bool {
    r.syntax().children_with_tokens().any(|t| t.kind() == ra_ap_syntax::SyntaxKind::DOT2EQ)
}

fn arith_to_binop(op: ast::ArithOp) -> Option<BinOp> {
    Some(match op {
        ast::ArithOp::Add => BinOp::Add,
        ast::ArithOp::Sub => BinOp::Sub,
        ast::ArithOp::Mul => BinOp::Mul,
        ast::ArithOp::Div => BinOp::Div,
        ast::ArithOp::Rem => BinOp::Mod,
        ast::ArithOp::BitAnd => BinOp::BitAnd,
        ast::ArithOp::BitOr => BinOp::BitOr,
        ast::ArithOp::BitXor => BinOp::BitXor,
        ast::ArithOp::Shl => BinOp::Shl,
        ast::ArithOp::Shr => BinOp::Shr,
    })
}

fn bin_op(b: &ast::BinExpr) -> Option<BinOp> {
    match b.op_kind()? {
        ast::BinaryOp::ArithOp(a) => arith_to_binop(a),
        ast::BinaryOp::LogicOp(ast::LogicOp::And) => Some(BinOp::And),
        ast::BinaryOp::LogicOp(ast::LogicOp::Or) => Some(BinOp::Or),
        ast::BinaryOp::CmpOp(ast::CmpOp::Eq { negated }) => {
            Some(if negated { BinOp::Ne } else { BinOp::Eq })
        }
        ast::BinaryOp::CmpOp(ast::CmpOp::Ord { ordering, strict }) => Some(match (ordering, strict) {
            (ast::Ordering::Less, true) => BinOp::Lt,
            (ast::Ordering::Less, false) => BinOp::Le,
            (ast::Ordering::Greater, true) => BinOp::Gt,
            (ast::Ordering::Greater, false) => BinOp::Ge,
        }),
        ast::BinaryOp::Assignment { .. } => None,
    }
}
