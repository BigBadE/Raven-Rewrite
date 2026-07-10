//! Fragment classification: split one `.rv` [`Module`](crate::ast::Module) into the
//! **executable** fragment (lowers to `rv-lower` → VM) and the **proof** fragment
//! (translates to the dependent kernel).
//!
//! Raven is one surface with one parser, but a given declaration belongs to one of the
//! two backends. This module is the single source of truth for *which*. It is purely
//! structural over the AST — no name resolution, no types — so both `rv-lower` (to skip
//! proof items) and the driver (to route proof items to the kernel and to decide whether
//! an entry point runs on the VM or the kernel) classify identically.
//!
//! The rules:
//! * `struct` / `trait` / `impl` are always **executable**.
//! * `axiom` / `def` / `instance` / `mutual` are always **proof**.
//! * an `enum` is **proof** when it is an *indexed relation* (`-> Prop`/`-> Type`, or it
//!   has indices); a plain data `enum` is **shared** — both backends may need it (a data
//!   type used by runtime code *and* by proofs about it).
//! * a `fn` is **proof** when it is logical: its return type is a proposition, it takes a
//!   logical parameter, its refinement/spec is dependent, its body uses a proof-only expression
//!   form (`match`-as-expression, `fun`, `forall`, …), or — transitively — it calls a proof
//!   `fn`. Scalar refinements stay executable and become solver obligations.

use crate::ast::{Block, EnumDecl, Expr, Item, Module, Stmt, Ty};
use rv_core::Sym;
use std::collections::HashSet;

/// Which backend a top-level item belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fragment {
    /// Lowers to executable IR (`rv-lower` → VM).
    Exec,
    /// Translates to the dependent kernel (proofs, relations, definitions).
    Proof,
    /// A plain data type needed by *both* backends.
    Shared,
}

impl Fragment {
    /// Should the executable pipeline (`rv-lower`) process this item?
    pub fn is_executable(self) -> bool {
        matches!(self, Fragment::Exec | Fragment::Shared)
    }
    /// Should the proof pipeline (kernel translation) process this item?
    pub fn is_proof(self) -> bool {
        matches!(self, Fragment::Proof | Fragment::Shared)
    }
}

/// Classify every item of `m`, in item order, into its [`Fragment`].
pub fn classify(m: &Module) -> Vec<Fragment> {
    // 1. The proof-fragment *types*. Seeded with indexed relations and every enum inside a
    //    `mutual` block (those route to the kernel wholesale), then grown by a fixpoint: a
    //    plain data enum whose fields mention a proof-fragment type is itself proof (it
    //    cannot be built by the executable pipeline, which never sees those types).
    let mut proof_types: HashSet<Sym> = HashSet::new();
    for it in &m.items {
        match it {
            Item::Enum(e) if is_relation(e) => {
                proof_types.insert(e.name);
            }
            Item::Mutual(es) => {
                for e in es {
                    proof_types.insert(e.name);
                }
            }
            _ => {}
        }
    }
    loop {
        let mut changed = false;
        for it in &m.items {
            if let Item::Enum(e) = it {
                if !proof_types.contains(&e.name) && enum_refs_any(e, &proof_types) {
                    proof_types.insert(e.name);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // 2. Seed: the `fn`s that are *intrinsically* proof (independent of who they call).
    let mut proof_fns: HashSet<Sym> = HashSet::new();
    for it in &m.items {
        if let Item::Fn(f) = it {
            // Proof on its own when it returns a proposition, takes a logical
            // argument, has a dependent refinement/spec, or uses a proof-only body
            // form. A scalar parameter refinement (`x: i64 where x != 0`) is an
            // executable contract, not a reason to route the function away from
            // the VM.
            let takes_proof_arg = f
                .params
                .iter()
                .any(|p| ty_is_logical(Some(&p.ty), &proof_types));
            let has_dependent_refinement = f
                .params
                .iter()
                .filter_map(|p| p.refinement.as_ref())
                .any(expr_is_dependent_spec);
            // A *dependent* spec — one mentioning an enum constructor or a proof form
            // (`result == Nat::Succ(x)`) — is a kernel obligation. A scalar spec
            // (`p.v != 0`, even over a struct field) stays on `rv-solve`'s executable path.
            let has_dependent_spec = f
                .requires
                .iter()
                .chain(&f.ensures)
                .any(expr_is_dependent_spec);
            if takes_proof_arg
                || has_dependent_refinement
                || has_dependent_spec
                || ty_is_logical(f.ret.as_ref(), &proof_types)
                || block_has_proof_form(&f.body)
            {
                proof_fns.insert(f.name);
            }
        }
    }

    // 3. The call graph over `fn`s (callee names per function).
    let mut all_fns: HashSet<Sym> = HashSet::new();
    let mut callees: Vec<(Sym, HashSet<Sym>)> = Vec::new();
    for it in &m.items {
        if let Item::Fn(f) = it {
            all_fns.insert(f.name);
            let mut cs = HashSet::new();
            collect_calls(&f.body, &mut cs);
            callees.push((f.name, cs));
        }
    }

    // 3a. Fixpoint UP the graph: a `fn` that calls a proof `fn` is itself proof.
    loop {
        let mut changed = false;
        for (name, cs) in &callees {
            if !proof_fns.contains(name) && cs.iter().any(|c| proof_fns.contains(c)) {
                proof_fns.insert(*name);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // 3b. Propagate DOWN the graph: any `fn` (transitively) called by a proof `fn` must
    // also be available to the kernel. If it is itself proof, it already is; otherwise it
    // is a plain computational helper needed by *both* backends — mark it Shared (the
    // kernel translates it, the VM still compiles it).
    let mut shared_fns: HashSet<Sym> = HashSet::new();
    let mut worklist: Vec<Sym> = proof_fns.iter().copied().collect();
    let mut seen: HashSet<Sym> = proof_fns.clone();
    while let Some(n) = worklist.pop() {
        if let Some((_, cs)) = callees.iter().find(|(name, _)| *name == n) {
            for c in cs {
                if all_fns.contains(c) && seen.insert(*c) {
                    if !proof_fns.contains(c) {
                        shared_fns.insert(*c);
                    }
                    worklist.push(*c);
                }
            }
        }
    }

    // 4. Emit per-item fragments.
    m.items
        .iter()
        .map(|it| match it {
            Item::Struct(_) | Item::Trait(_) | Item::Impl(_) => Fragment::Exec,
            Item::Axiom(_) | Item::Def(_) | Item::Instance(_) | Item::Mutual(_) => Fragment::Proof,
            Item::Enum(e) => {
                if proof_types.contains(&e.name) {
                    Fragment::Proof
                } else {
                    Fragment::Shared
                }
            }
            Item::Fn(f) => {
                if proof_fns.contains(&f.name) {
                    Fragment::Proof
                } else if shared_fns.contains(&f.name) {
                    Fragment::Shared
                } else {
                    Fragment::Exec
                }
            }
        })
        .collect()
}

/// An `enum` is an indexed relation (proof fragment) when it declares a result sort or
/// carries indices; a plain data `enum` has neither.
fn is_relation(e: &EnumDecl) -> bool {
    e.result_sort.is_some() || !e.indices.is_empty()
}

/// A type is logical (proof-fragment) when it is a dependent term (`Ty::Term`, e.g.
/// `a == b` or `Le(a, b)`) or names a proof-fragment type (a relation or a data type that
/// transitively mentions one). Used for both return types and parameter types.
fn ty_is_logical(t: Option<&Ty>, proof_types: &HashSet<Sym>) -> bool {
    match t {
        Some(Ty::Term(_)) => true,
        Some(Ty::Adt(s)) | Some(Ty::Param(s)) => proof_types.contains(s),
        Some(Ty::Generic { base, .. }) => proof_types.contains(base),
        _ => false,
    }
}

/// Is a spec clause *dependent* — i.e. does it mention an enum constructor or a proof-only
/// form? Such specs (`result == Nat::Succ(x)`) are discharged by the kernel; purely scalar
/// specs (`p.v != 0`) stay on `rv-solve`'s executable path.
fn expr_is_dependent_spec(e: &Expr) -> bool {
    match e {
        Expr::EnumCtor { .. } => true,
        _ if expr_has_proof_form(e) => true,
        // Recurse through the executable connectives a scalar spec is built from.
        Expr::Bin(_, a, b) => expr_is_dependent_spec(a) || expr_is_dependent_spec(b),
        Expr::Un(_, a) | Expr::Deref(a) | Expr::Try(a) | Expr::Ref { expr: a, .. } => {
            expr_is_dependent_spec(a)
        }
        Expr::Field { base, .. } => expr_is_dependent_spec(base),
        Expr::Call { args, .. } => args.iter().any(expr_is_dependent_spec),
        Expr::MethodCall { recv, args, .. } => {
            expr_is_dependent_spec(recv) || args.iter().any(expr_is_dependent_spec)
        }
        Expr::StructLit { fields, .. } => fields.iter().any(|(_, e)| expr_is_dependent_spec(e)),
        _ => false,
    }
}

/// Does any field of `e` (across all variants) reference a type in `proof_types`?
fn enum_refs_any(e: &EnumDecl, proof_types: &HashSet<Sym>) -> bool {
    e.variants
        .iter()
        .flat_map(|v| v.fields.iter())
        .any(|ty| ty_names_proof_type(ty, proof_types))
}

/// Does the (possibly nested) type `ty` name a type in `proof_types`?
fn ty_names_proof_type(ty: &Ty, proof_types: &HashSet<Sym>) -> bool {
    match ty {
        Ty::Adt(s) | Ty::Param(s) => proof_types.contains(s),
        Ty::Generic { base, args } => {
            proof_types.contains(base) || args.iter().any(|a| ty_names_proof_type(a, proof_types))
        }
        Ty::Ref { inner, .. } => ty_names_proof_type(inner, proof_types),
        Ty::Term(_) => true,
        Ty::I64 | Ty::F64 | Ty::Bool | Ty::String | Ty::Unit => false,
    }
}

// --- expression / block walkers ------------------------------------------------------

/// Does any expression in the block use a proof-only form?
fn block_has_proof_form(b: &Block) -> bool {
    b.stmts.iter().any(stmt_has_proof_form)
}

fn stmt_has_proof_form(s: &Stmt) -> bool {
    match s {
        Stmt::Let { init, .. } => expr_has_proof_form(init),
        Stmt::Assign { value, .. } => expr_has_proof_form(value),
        Stmt::DerefAssign { place, value } => {
            expr_has_proof_form(place) || expr_has_proof_form(value)
        }
        Stmt::If { cond, then_blk, else_blk } => {
            expr_has_proof_form(cond)
                || block_has_proof_form(then_blk)
                || else_blk.as_ref().is_some_and(block_has_proof_form)
        }
        Stmt::While { cond, body, .. } => expr_has_proof_form(cond) || block_has_proof_form(body),
        Stmt::Match { scrut, arms } => {
            expr_has_proof_form(scrut) || arms.iter().any(|a| block_has_proof_form(&a.body))
        }
        Stmt::Return(e) | Stmt::Panic(e) => e.as_ref().is_some_and(expr_has_proof_form),
        Stmt::Assert(e) | Stmt::Expr(e) => expr_has_proof_form(e),
    }
}

/// Is `e` (or a sub-expression) a proof-only form? These are exactly the forms the
/// executable lowering rejects (see `rv-lower`'s `build.rs`).
fn expr_has_proof_form(e: &Expr) -> bool {
    match e {
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
        | Expr::ByCases { .. } => true,
        // Recurse through the executable forms.
        Expr::Bin(_, a, b) => expr_has_proof_form(a) || expr_has_proof_form(b),
        Expr::Un(_, a) | Expr::Deref(a) | Expr::Try(a) | Expr::Ref { expr: a, .. } => {
            expr_has_proof_form(a)
        }
        Expr::Call { args, .. } | Expr::EnumCtor { args, .. } => {
            args.iter().any(expr_has_proof_form)
        }
        Expr::MethodCall { recv, args, .. } => {
            expr_has_proof_form(recv) || args.iter().any(expr_has_proof_form)
        }
        Expr::Field { base, .. } => expr_has_proof_form(base),
        Expr::StructLit { fields, .. } => fields.iter().any(|(_, e)| expr_has_proof_form(e)),
        Expr::Lambda { body, .. } => expr_has_proof_form(body),
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Str(_)
        | Expr::Bool(_)
        | Expr::Unit
        | Expr::Var(_) => false,
    }
}

/// Collect every name referenced in a *call position* in the block: direct calls
/// (`f(..)`), method calls (`x.m(..)`), and bare variable references (`Var`) — the last
/// because functions used as first-class values (e.g. `subst(Nat, is_zero, …)` passing
/// `is_zero`) must still be treated as call-graph edges. Constructor names are ignored
/// (they are resolved against enum declarations, not the `fn` set).
fn collect_calls(b: &Block, out: &mut HashSet<Sym>) {
    for s in &b.stmts {
        stmt_calls(s, out);
    }
}

fn stmt_calls(s: &Stmt, out: &mut HashSet<Sym>) {
    match s {
        Stmt::Let { init, .. } => expr_calls(init, out),
        Stmt::Assign { value, .. } => expr_calls(value, out),
        Stmt::DerefAssign { place, value } => {
            expr_calls(place, out);
            expr_calls(value, out);
        }
        Stmt::If { cond, then_blk, else_blk } => {
            expr_calls(cond, out);
            collect_calls(then_blk, out);
            if let Some(b) = else_blk {
                collect_calls(b, out);
            }
        }
        Stmt::While { cond, body, .. } => {
            expr_calls(cond, out);
            collect_calls(body, out);
        }
        Stmt::Match { scrut, arms } => {
            expr_calls(scrut, out);
            for a in arms {
                collect_calls(&a.body, out);
            }
        }
        Stmt::Return(e) | Stmt::Panic(e) => {
            if let Some(e) = e {
                expr_calls(e, out);
            }
        }
        Stmt::Assert(e) | Stmt::Expr(e) => expr_calls(e, out),
    }
}

fn expr_calls(e: &Expr, out: &mut HashSet<Sym>) {
    match e {
        // Call / value-reference positions that become call-graph edges.
        Expr::Var(s) => {
            out.insert(*s);
        }
        Expr::Call { func, args } => {
            out.insert(*func);
            args.iter().for_each(|a| expr_calls(a, out));
        }
        Expr::MethodCall { method, recv, args } => {
            out.insert(*method);
            expr_calls(recv, out);
            args.iter().for_each(|a| expr_calls(a, out));
        }
        Expr::EnumCtor { args, .. } => args.iter().for_each(|a| expr_calls(a, out)),
        Expr::Apply { callee, args } => {
            expr_calls(callee, out);
            args.iter().for_each(|a| expr_calls(a, out));
        }
        Expr::Bin(_, a, b) | Expr::Arrow(a, b) => {
            expr_calls(a, out);
            expr_calls(b, out);
        }
        Expr::Un(_, a)
        | Expr::Deref(a)
        | Expr::Try(a)
        | Expr::Ref { expr: a, .. }
        | Expr::Field { base: a, .. } => expr_calls(a, out),
        Expr::MatchExpr { scrut, arms } => {
            expr_calls(scrut, out);
            arms.iter().for_each(|(_, e)| expr_calls(e, out));
        }
        Expr::Fun { body, .. } | Expr::Lambda { body, .. } => expr_calls(body, out),
        Expr::Forall { params, body } => {
            params.iter().for_each(|(_, t)| expr_calls(t, out));
            expr_calls(body, out);
        }
        Expr::LetIn { ty, init, body, .. } => {
            if let Some(t) = ty {
                expr_calls(t, out);
            }
            expr_calls(init, out);
            expr_calls(body, out);
        }
        Expr::Rewrite { eqn, body } => {
            expr_calls(eqn, out);
            expr_calls(body, out);
        }
        Expr::ByCases { scrut, tbody, fbody } => {
            expr_calls(scrut, out);
            expr_calls(tbody, out);
            expr_calls(fbody, out);
        }
        Expr::StructLit { fields, .. } => fields.iter().for_each(|(_, e)| expr_calls(e, out)),
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Str(_)
        | Expr::Bool(_)
        | Expr::Unit
        | Expr::TypeUniv(_)
        | Expr::Prop
        | Expr::Hole
        | Expr::Decide => {}
    }
}
