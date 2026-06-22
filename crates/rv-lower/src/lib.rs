//! Lowering: surface AST -> `rv_ir::Program<Parsed>`.
//!
//! Each surface function becomes a [`rv_ir::Function<Parsed>`] with an explicit
//! control-flow graph of basic [`rv_ir::Block`]s. Structured control flow
//! (`if`/`while`) is compiled to blocks ending in `Goto`/`Branch`/`Return`.
//!
//! Because the program is in the `Parsed` phase, all `Ty` fields are `()` and no
//! `Drop` terminators are emitted (memory strategy is inferred later).

mod build;
mod spec;
mod types;

use std::collections::HashMap;
use std::collections::HashSet;

use rv_core::Sym;
use rv_ir::{Function, Parsed, Program};
use rv_syntax::ast::{
    Block as AstBlock, Expr as AstExpr, GenericParam, Item, MethodDecl, Module, Param, Ty as AstTy,
};

use build::FnBuilder;
use types::Types;

/// Lower a whole module to an `rv_ir::Program<Parsed>`.
///
/// `struct`/`enum` declarations are collected first into the program's `types`
/// table and a lookup registry, which is then threaded (immutably) through each
/// function's lowering so it can resolve fields, variants, and match arms.
pub fn lower(
    module: &Module,
    syms: &mut rv_core::Symbols,
) -> Result<Program<Parsed>, String> {
    // Partition items: gather all type declarations before any function, so a
    // function may reference types declared later in the module.
    let mut struct_decls = Vec::new();
    let mut enum_decls = Vec::new();
    let mut fn_decls = Vec::new();
    let mut trait_decls = Vec::new();
    let mut impl_decls = Vec::new();
    for item in &module.items {
        match item {
            Item::Struct(s) => struct_decls.push(s),
            Item::Enum(e) => enum_decls.push(e),
            Item::Fn(f) => fn_decls.push(f),
            Item::Trait(t) => trait_decls.push(t),
            Item::Impl(i) => impl_decls.push(i),
        }
    }

    let mut types = Types::build(&struct_decls, &enum_decls, syms)?;

    // Traits produce no IR; record their method-name sets for optional validation.
    for tr in &trait_decls {
        let names: Vec<Sym> = tr.methods.iter().map(|m| m.name).collect();
        types.register_trait(tr.name, names);
    }

    // Register every impl method into the resolution table BEFORE lowering any
    // bodies, so a method may call another method (forward references resolve).
    // We remember the mangled name chosen for each method so we lower its body
    // under that exact symbol.
    let mut planned_methods: Vec<(Sym, &MethodDecl, Sym)> = Vec::new();
    for im in &impl_decls {
        let mut provided: HashSet<Sym> = HashSet::new();
        for m in &im.methods {
            let mangled = types.register_method(im.type_name, m.name, syms)?;
            provided.insert(m.name);
            // (receiver ADT name, the method decl, the mangled function name)
            planned_methods.push((im.type_name, m, mangled));
        }
        // For a trait impl, optionally check the declared methods are all present.
        if let Some(tr) = im.trait_name {
            types.check_trait_impl(tr, im.type_name, &provided, syms)?;
        }
    }

    // Record each function's/method's return ADT (when it returns a struct/enum),
    // so `adt_of_expr` can resolve the ADT of a *call result* — letting `match`,
    // `?`, and method calls compose on call results.
    let ret_adt = |ret: &Option<rv_syntax::ast::Ty>| -> Option<Sym> {
        match ret {
            Some(rv_syntax::ast::Ty::Adt(n)) => Some(*n),
            Some(rv_syntax::ast::Ty::Generic { base, .. }) => Some(*base),
            _ => None,
        }
    };
    for decl in &fn_decls {
        if let Some(a) = ret_adt(&decl.ret) {
            if types.is_adt(a) {
                types.set_fn_ret(decl.name, a);
            }
        }
    }
    for (_, m, mangled) in &planned_methods {
        if let Some(a) = ret_adt(&m.ret) {
            if types.is_adt(a) {
                types.set_fn_ret(*mangled, a);
            }
        }
    }

    let mut funcs = Vec::new();
    // Ordinary functions first, then desugared impl methods.
    for decl in fn_decls {
        funcs.extend(lower_fn(decl, &types, syms)?);
    }
    for (type_name, m, mangled) in planned_methods {
        funcs.extend(lower_method(type_name, m, mangled, &types, syms)?);
    }
    Ok(Program { types: types.defs, funcs })
}

/// Lower a single function declaration into IR.
fn lower_fn(
    decl: &rv_syntax::ast::FnDecl,
    types: &Types,
    syms: &mut rv_core::Symbols,
) -> Result<Vec<Function<Parsed>>, String> {
    let type_params: Vec<Sym> = decl.generics.iter().map(|g| g.name).collect();
    lower_callable(
        decl.name,
        &decl.generics,
        &decl.params,
        &decl.requires,
        &decl.ensures,
        &decl.body,
        decl.ret.as_ref(),
        types,
        syms,
        type_params,
    )
}

/// Lower an `impl` method into a top-level [`Function`] named by its mangled
/// symbol. The receiver `self` (if present) becomes the FIRST ordinary parameter,
/// with the impl's `type_name` as its (best-effort tracked) ADT type so calls
/// like `self.other()` and field access on `self` resolve.
fn lower_method(
    type_name: Sym,
    decl: &MethodDecl,
    mangled: Sym,
    types: &Types,
    syms: &mut rv_core::Symbols,
) -> Result<Vec<Function<Parsed>>, String> {
    // The method's own generic parameters scope its signature/body types.
    let type_params: Vec<Sym> = decl.generics.iter().map(|g| g.name).collect();
    let scope: HashSet<Sym> = type_params.iter().copied().collect();

    let mut b = FnBuilder::new(types);
    let mut params = Vec::new();

    // A `self` receiver becomes the first parameter, typed as the impl's ADT.
    if decl.has_self {
        let self_sym = syms.intern("self");
        let id = b.new_local(Some(self_sym));
        b.set_local_adt(id, type_name);
        b.bind(self_sym, id);
        params.push(id);
    }
    // Remaining ordinary parameters.
    bind_params(&mut b, &decl.params, &scope, &mut params);

    // `self` and any struct-typed parameter can be projected in a spec.
    let mut var_struct = struct_typed_params(&decl.params, &scope, types);
    if decl.has_self && types.struct_info(type_name).is_some() {
        var_struct.insert(syms.intern("self"), type_name);
    }
    let (pre, post) = lower_clauses(&decl.requires, &decl.ensures, types, &var_struct, syms)?;
    b.lower_block(&decl.body, syms)?;
    b.finish_with_default_return();

    let lifted = b.take_lifted();
    let (locals, blocks) = b.into_parts();
    let mut out = vec![Function {
        name: mangled,
        type_params,
        params,
        // Declared return annotation (if any), for the body-vs-signature check in inference.
        ret: decl.ret.as_ref().map(|t| types::resolve_ty(t, &scope)),
        pre,
        post,
        locals,
        blocks,
        entry: BlockId_ENTRY,
    }];
    out.extend(lifted);
    Ok(out)
}

/// Shared lowering for an ordinary function (and the common path of methods):
/// bind parameters, lower spec clauses and body, and assemble the `Function`.
#[allow(clippy::too_many_arguments)]
fn lower_callable(
    name: Sym,
    generics: &[GenericParam],
    ast_params: &[Param],
    requires: &[AstExpr],
    ensures: &[AstExpr],
    body: &AstBlock,
    ret_ann: Option<&rv_syntax::ast::Ty>,
    types: &Types,
    syms: &mut rv_core::Symbols,
    type_params: Vec<Sym>,
) -> Result<Vec<Function<Parsed>>, String> {
    // In-scope type parameters: a parameter type naming one is a `Ty::Param`, not
    // an ADT — so we must NOT track it as a (resolvable) ADT local.
    let scope: HashSet<Sym> = generics.iter().map(|g| g.name).collect();

    let mut b = FnBuilder::new(types);
    let mut params = Vec::with_capacity(ast_params.len());
    bind_params(&mut b, ast_params, &scope, &mut params);

    let var_struct = struct_typed_params(ast_params, &scope, types);
    let (pre, post) = lower_clauses(requires, ensures, types, &var_struct, syms)?;

    // Lower the body into the CFG.
    b.lower_block(body, syms)?;
    // Ensure every path ends in a Return; append a unit return if it falls off.
    b.finish_with_default_return();

    let lifted = b.take_lifted();
    let (locals, blocks) = b.into_parts();
    let mut out = vec![Function {
        name,
        type_params,
        params,
        // Record the *declared* return annotation (if any) so inference can check the
        // body against it — most importantly to reject a primitive mismatch like a
        // `bool` body under an `-> i64` signature. `None` = unannotated (inferred).
        ret: ret_ann.map(|t| types::resolve_ty(t, &scope)),
        pre,
        post,
        locals,
        blocks,
        entry: BlockId_ENTRY,
    }];
    out.extend(lifted);
    Ok(out)
}

/// Allocate a local per parameter, register its name, and (when the parameter's
/// type is a concrete ADT — not a generic type parameter) track that ADT so field
/// access / `match` / method calls on it can resolve. Pushes the new locals onto
/// `out`.
fn bind_params(
    b: &mut FnBuilder,
    ast_params: &[Param],
    scope: &HashSet<Sym>,
    out: &mut Vec<rv_ir::LocalId>,
) {
    for p in ast_params {
        let id = b.new_local(Some(p.name));
        // Track an ADT parameter's type so field access / match / `?` / methods
        // resolve. A bare name that is actually a generic type parameter is NOT a
        // known ADT, so we skip it (its type erases to `Ty::Param`). A generic
        // application `Base<args..>` erases to its base ADT, which we also track
        // (so e.g. a `Result<i64, i64>` parameter is matchable / `?`-propagatable).
        match &p.ty {
            AstTy::Adt(adt) if !scope.contains(adt) => b.set_local_adt(id, *adt),
            AstTy::Generic { base, .. } if !scope.contains(base) => b.set_local_adt(id, *base),
            _ => {}
        }
        b.bind(p.name, id);
        out.push(id);
    }
}

/// Lower a callable's `requires` / `ensures` clauses into pre/post `Prop`s.
///
/// `var_struct` maps in-scope struct-typed variable names (parameters / `self`)
/// to their struct type, so a spec like `requires p.v != 0` can resolve `p.v`'s
/// field index and lower to an uninterpreted projection term.
fn lower_clauses(
    requires: &[AstExpr],
    ensures: &[AstExpr],
    types: &Types,
    var_struct: &HashMap<Sym, Sym>,
    syms: &mut rv_core::Symbols,
) -> Result<(rv_core::Prop, rv_core::Prop), String> {
    let ctx = spec::SpecCtx { types, var_struct };
    // Preconditions: conjoin all `requires` clauses (empty -> True).
    let mut pre = rv_core::Prop::True;
    for r in requires {
        pre = pre.and(spec::lower_prop(r, syms, &ctx)?);
    }
    // Postconditions: conjoin all `ensures` clauses (empty -> True). The `result`
    // identifier lowers to `Term::Var(intern("result"))` automatically because it
    // is interned by the parser as an ordinary symbol with that exact name.
    let mut post = rv_core::Prop::True;
    for e in ensures {
        post = post.and(spec::lower_prop(e, syms, &ctx)?);
    }
    Ok((pre, post))
}

/// Build the map from struct-typed parameter names to their struct type, used to
/// resolve `param.field` in specs. Only parameters whose type is a known struct
/// (not an enum, not a generic type parameter) are recorded.
fn struct_typed_params(
    ast_params: &[Param],
    scope: &HashSet<Sym>,
    types: &Types,
) -> HashMap<Sym, Sym> {
    let mut map = HashMap::new();
    for p in ast_params {
        if let AstTy::Adt(name) = &p.ty {
            if !scope.contains(name) && types.struct_info(*name).is_some() {
                map.insert(p.name, *name);
            }
        }
    }
    map
}

/// The entry block id every function starts from.
#[allow(non_upper_case_globals)]
const BlockId_ENTRY: rv_ir::BlockId = rv_ir::BlockId(0);

#[cfg(test)]
mod tests {
    use super::*;
    use rv_ir::Terminator;

    /// Parse + lower a source string, panicking with the error on failure.
    fn lower_src(src: &str) -> (Program<Parsed>, rv_core::Symbols) {
        let mut syms = rv_core::Symbols::new();
        let module = rv_syntax::parse(src, &mut syms).expect("parse failed");
        let prog = lower(&module, &mut syms).expect("lower failed");
        (prog, syms)
    }

    #[test]
    fn lowers_the_div_main_example() {
        let src = "\
fn div(x: i64, y: i64) -> i64
  requires y != 0;
{
  return x / y;
}
fn main() -> i64 {
  let a: i64 = 10;
  let b: i64 = 2;
  assert b != 0;
  return div(a, b);
}";
        let (prog, _syms) = lower_src(src);
        assert_eq!(prog.funcs.len(), 2);

        let div = &prog.funcs[0];
        assert_eq!(div.params.len(), 2);
        // Precondition `y != 0` must be present (not trivially True).
        assert_ne!(div.pre, rv_core::Prop::True);
        // A single straight-line block ending in Return.
        assert_eq!(div.blocks.len(), 1);
        assert!(matches!(div.blocks[0].term, Terminator::Return(_)));

        let main = &prog.funcs[1];
        // Two params? No — main has no params.
        assert_eq!(main.params.len(), 0);
        // Locals: a, b, plus temporaries for the call argument plumbing/result.
        assert!(main.locals.len() >= 2);
        // Must contain an Assert statement somewhere.
        let has_assert = main
            .blocks
            .iter()
            .flat_map(|bl| &bl.stmts)
            .any(|s| matches!(s, rv_ir::Stmt::Assert(_)));
        assert!(has_assert, "expected an assert in main");
    }

    #[test]
    fn if_else_produces_four_blocks() {
        // entry (branch) + then + else + join
        let src = "fn f(n: i64) -> i64 { if n > 0 { return 1; } else { return 0; } }";
        let (prog, _) = lower_src(src);
        let f = &prog.funcs[0];
        // entry, then, else, join = 4 blocks.
        assert_eq!(f.blocks.len(), 4, "blocks: {}", f.blocks.len());
        // The entry block must end in a Branch.
        let entry = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
        assert!(matches!(entry.term, Terminator::Branch { .. }));
    }

    #[test]
    fn while_has_a_back_edge() {
        let src = "fn f(n: i64) -> i64 { let i = 0; while i < n { i = i + 1; } return i; }";
        let (prog, _) = lower_src(src);
        let f = &prog.funcs[0];
        // Some block must Goto an earlier block id (the loop header back-edge).
        let has_back_edge = f.blocks.iter().any(|bl| match &bl.term {
            Terminator::Goto(target) => target.0 <= bl.id.0,
            _ => false,
        });
        assert!(has_back_edge, "expected a loop back-edge");
        // The header must end in a Branch (cond -> body / exit).
        let has_branch = f
            .blocks
            .iter()
            .any(|bl| matches!(bl.term, Terminator::Branch { .. }));
        assert!(has_branch);
    }

    #[test]
    fn lowers_struct_literal_and_field_access() {
        use rv_ir::{AggKind, Operand, Proj, RValue, Stmt, TypeDef};
        let src = "\
struct Point { x: i64, y: i64 }
fn f() -> i64 {
    let p = Point { x: 1, y: 2 };
    return p.x;
}";
        let (prog, _) = lower_src(src);
        // The struct decl is recorded in the program's type table.
        assert_eq!(prog.types.len(), 1);
        assert!(matches!(&prog.types[0], TypeDef::Struct { fields, .. } if fields.len() == 2));

        let f = &prog.funcs[0];
        // Somewhere there is an Aggregate(Struct) rvalue with two operands in
        // declaration order (x then y).
        let agg = f
            .blocks
            .iter()
            .flat_map(|b| &b.stmts)
            .find_map(|s| match s {
                Stmt::Assign(_, RValue::Aggregate(AggKind::Struct(_), ops)) => Some(ops.clone()),
                _ => None,
            })
            .expect("expected a struct Aggregate");
        assert_eq!(agg.len(), 2);

        // The returned operand reads `p.x` -> a place with a Field(0) projection.
        let ret_reads_field0 = f.blocks.iter().any(|b| match &b.term {
            Terminator::Return(Operand::Copy(place)) => {
                matches!(place.proj.as_slice(), [Proj::Field(0)])
            }
            _ => false,
        });
        assert!(ret_reads_field0, "expected a Return reading field 0 of the struct");
    }

    #[test]
    fn lowers_enum_and_match() {
        use rv_ir::{AggKind, Proj, RValue, Stmt, Terminator};
        let src = "\
enum Opt { None, Some(i64) }
fn f() -> i64 {
    let o = Opt::Some(5);
    match o {
        Opt::Some(v) => { return v; }
        _ => { return 0; }
    }
}";
        let (prog, _) = lower_src(src);
        assert_eq!(prog.types.len(), 1);

        let f = &prog.funcs[0];
        // The constructor lowers to Aggregate(Variant(_, 1)) (Some is variant 1).
        let has_variant_agg = f.blocks.iter().flat_map(|b| &b.stmts).any(|s| {
            matches!(s, Stmt::Assign(_, RValue::Aggregate(AggKind::Variant(_, 1), _)))
        });
        assert!(has_variant_agg, "expected an Aggregate(Variant(_, 1))");

        // There is a Match terminator with one arm (Some) and an `otherwise` (_).
        let match_term = f
            .blocks
            .iter()
            .find_map(|b| match &b.term {
                Terminator::Match { arms, otherwise, .. } => Some((arms.clone(), *otherwise)),
                _ => None,
            })
            .expect("expected a Match terminator");
        assert_eq!(match_term.0.len(), 1);
        assert_eq!(match_term.0[0].variant, 1);
        assert!(match_term.1.is_some(), "expected an `otherwise` arm");

        // The Some arm binds `v` via Downcast(1)+Field(0).
        let binds_v = f.blocks.iter().flat_map(|b| &b.stmts).any(|s| match s {
            Stmt::Assign(_, RValue::Use(rv_ir::Operand::Copy(place))) => {
                matches!(place.proj.as_slice(), [Proj::Downcast(1), Proj::Field(0)])
            }
            _ => false,
        });
        assert!(binds_v, "expected a Downcast(1)+Field(0) binder for `v`");
    }

    #[test]
    fn lowers_while_with_invariant() {
        use rv_ir::Stmt;
        let src = "\
fn f(n: i64) -> i64 {
    let i = 0;
    while i < n invariant i >= 0; {
        i = i + 1;
    }
    return i;
}";
        let (prog, _) = lower_src(src);
        let f = &prog.funcs[0];

        // The loop header block must begin with an Invariant statement, before
        // any condition-evaluation statements.
        let header_has_leading_invariant = f.blocks.iter().any(|b| {
            matches!(b.stmts.first(), Some(Stmt::Invariant(_)))
        });
        assert!(
            header_has_leading_invariant,
            "expected a loop header whose first statement is an Invariant"
        );
    }

    #[test]
    fn lowers_mut_borrow_and_store_through_it() {
        use rv_ir::{BorrowKind, Operand, Proj, RValue, Stmt};
        // `&mut x` produces `RValue::Ref(Mut, x)`; `*r = 5;` stores into the place
        // `r` + Deref.
        let src = "\
fn f() -> i64 {
    let x = 0;
    let r = &mut x;
    *r = 5;
    return x;
}";
        let (prog, _) = lower_src(src);
        let f = &prog.funcs[0];
        let stmts: Vec<&Stmt> = f.blocks.iter().flat_map(|b| &b.stmts).collect();

        // A `RValue::Ref(BorrowKind::Mut, _)` is emitted for `&mut x`.
        let mut_ref = stmts.iter().any(|s| {
            matches!(s, Stmt::Assign(_, RValue::Ref(BorrowKind::Mut, _)))
        });
        assert!(mut_ref, "expected a mutable Ref rvalue for `&mut x`");

        // `*r = 5;` assigns into a place whose final projection is `Deref`, with
        // the constant 5 on the right.
        let store = stmts.iter().any(|s| match s {
            Stmt::Assign(place, RValue::Use(Operand::Const(rv_ir::Const::Int(5)))) => {
                matches!(place.proj.last(), Some(Proj::Deref))
            }
            _ => false,
        });
        assert!(store, "expected a store of 5 through a Deref place");
    }

    #[test]
    fn lowers_shared_borrow_and_read_through_it() {
        use rv_ir::{BorrowKind, Operand, Proj, RValue, Stmt};
        // `&x` produces `RValue::Ref(Shared, x)`; `*r` reads through `r` + Deref.
        let src = "\
fn f() -> i64 {
    let x = 7;
    let r = &x;
    return *r;
}";
        let (prog, _) = lower_src(src);
        let f = &prog.funcs[0];
        let stmts: Vec<&Stmt> = f.blocks.iter().flat_map(|b| &b.stmts).collect();

        // A shared `RValue::Ref(BorrowKind::Shared, _)` for `&x`.
        let shared_ref = stmts.iter().any(|s| {
            matches!(s, Stmt::Assign(_, RValue::Ref(BorrowKind::Shared, _)))
        });
        assert!(shared_ref, "expected a shared Ref rvalue for `&x`");

        // `return *r;` returns a Copy of a place ending in `Deref`.
        let reads_deref = f.blocks.iter().any(|b| match &b.term {
            Terminator::Return(Operand::Copy(place)) => {
                matches!(place.proj.last(), Some(Proj::Deref))
            }
            _ => false,
        });
        assert!(reads_deref, "expected a Return reading through a Deref place");
    }

    #[test]
    fn lowers_reference_parameter_type() {
        // An `&T` parameter type must lower without error and the parameter local
        // be usable (read through with `*`).
        let src = "\
fn f(r: &i64) -> i64 {
    return *r;
}";
        let (prog, _) = lower_src(src);
        let f = &prog.funcs[0];
        assert_eq!(f.params.len(), 1);
        // The returned operand reads through a Deref of the parameter local.
        let ok = f.blocks.iter().any(|b| match &b.term {
            Terminator::Return(rv_ir::Operand::Copy(place)) => {
                place.local == f.params[0]
                    && matches!(place.proj.as_slice(), [rv_ir::Proj::Deref])
            }
            _ => false,
        });
        assert!(ok, "expected `return *r;` to read Deref of the &T parameter");
    }

    #[test]
    fn lowers_generic_fn_with_type_params() {
        // (a) `fn id<T>(x: T) -> T { return x; }` lowers; Function.type_params == [T].
        let src = "fn id<T>(x: T) -> T { return x; }";
        let (prog, mut syms) = lower_src(src);
        let f = &prog.funcs[0];
        assert_eq!(f.type_params, vec![syms.intern("T")]);
        // The parameter is usable: a single block returning the parameter local.
        assert_eq!(f.params.len(), 1);
        assert!(matches!(f.blocks[0].term, Terminator::Return(_)));
    }

    #[test]
    fn lowers_generic_struct_with_type_params() {
        // (b) `struct Pair<A, B> { .. }` lowers with type_params == [A, B], and a
        // field naming a type parameter lowers to `Ty::Param`.
        use rv_ir::TypeDef;
        let src = "struct Pair<A, B> { a: A, b: B }";
        let (prog, mut syms) = lower_src(src);
        let TypeDef::Struct { type_params, fields, .. } = &prog.types[0] else {
            panic!("expected a struct typedef");
        };
        assert_eq!(*type_params, vec![syms.intern("A"), syms.intern("B")]);
        // Field `a: A` -> `Ty::Param(A)`.
        assert_eq!(fields[0].ty, rv_core::Ty::Param(syms.intern("A")));
        assert_eq!(fields[1].ty, rv_core::Ty::Param(syms.intern("B")));
    }

    #[test]
    fn lowers_generic_enum_variant_field_as_param() {
        // (d) `enum Option<T> { None, Some(T) }` lowers; the `Some` payload type is
        // `Ty::Param(T)`.
        use rv_ir::TypeDef;
        let src = "enum Option<T> { None, Some(T) }";
        let (prog, mut syms) = lower_src(src);
        let TypeDef::Enum { type_params, variants, .. } = &prog.types[0] else {
            panic!("expected an enum typedef");
        };
        assert_eq!(*type_params, vec![syms.intern("T")]);
        // `Some(T)` is variant 1 with a single `Ty::Param(T)` field.
        assert_eq!(variants[1].fields, vec![rv_core::Ty::Param(syms.intern("T"))]);
    }

    #[test]
    fn generic_type_args_are_erased() {
        // A field `Option<i64>` erases to `Ty::Adt(Option)` (type args dropped).
        use rv_ir::TypeDef;
        let src = "\
enum Option<T> { None, Some(T) }
struct Holder { o: Option<i64> }";
        let (prog, mut syms) = lower_src(src);
        let holder = prog.types.iter().find_map(|d| match d {
            TypeDef::Struct { name, fields, .. } if *name == syms.intern("Holder") => Some(fields),
            _ => None,
        }).expect("expected the Holder struct");
        assert_eq!(holder[0].ty, rv_core::Ty::Adt(syms.intern("Option")));
    }

    #[test]
    fn desugars_inherent_method_call_to_mangled_call() {
        // (c) `impl Point { fn sum(self) -> i64 {..} }` + `p.sum()` desugars to a
        // Call of the mangled function `Point::sum` with the receiver as first arg.
        use rv_ir::{Operand, Place, RValue, Stmt};
        let src = "\
struct Point { x: i64, y: i64 }
impl Point { fn sum(self) -> i64 { return self.x + self.y; } }
fn f() -> i64 {
    let p = Point { x: 1, y: 2 };
    return p.sum();
}";
        let (prog, mut syms) = lower_src(src);

        // The desugared method exists as a top-level function named `Point::sum`.
        let mangled = syms.intern("Point::sum");
        let method_fn = prog.funcs.iter().find(|f| f.name == mangled)
            .expect("expected a top-level `Point::sum` function");
        // Its first parameter is the `self` receiver.
        assert_eq!(method_fn.params.len(), 1);

        // `f` contains a Call to `Point::sum` whose first operand reads a local
        // (the receiver `p`).
        let f = prog.funcs.iter().find(|f| f.name == syms.intern("f")).unwrap();
        let call_args = f.blocks.iter().flat_map(|b| &b.stmts).find_map(|s| match s {
            Stmt::Assign(_, RValue::Call(callee, args)) if *callee == mangled => Some(args.clone()),
            _ => None,
        }).expect("expected a Call to `Point::sum`");
        assert_eq!(call_args.len(), 1); // just the receiver
        assert!(matches!(&call_args[0], Operand::Copy(Place { proj, .. }) if proj.is_empty()));
    }

    #[test]
    fn distinct_types_get_distinct_mangled_methods() {
        // Two different types' `m` get distinct mangled names.
        let src = "\
struct A { v: i64 }
struct B { v: i64 }
impl A { fn m(self) -> i64 { return self.v; } }
impl B { fn m(self) -> i64 { return self.v; } }";
        let (prog, mut syms) = lower_src(src);
        assert!(prog.funcs.iter().any(|f| f.name == syms.intern("A::m")));
        assert!(prog.funcs.iter().any(|f| f.name == syms.intern("B::m")));
    }

    #[test]
    fn method_call_on_unknown_receiver_type_errors() {
        // A method call whose receiver type can't be resolved is a clear error.
        let mut syms = rv_core::Symbols::new();
        let src = "fn f(x: i64) -> i64 { return x.foo(); }";
        let module = rv_syntax::parse(src, &mut syms).unwrap();
        let err = match lower(&module, &mut syms) {
            Ok(_) => panic!("expected lowering to fail"),
            Err(e) => e,
        };
        assert!(err.contains("receiver"), "got: {err}");
    }

    #[test]
    fn panic_lowers_to_panic_terminator() {
        // (a) A `panic;` statement lowers to a `Terminator::Panic`.
        let src = "fn f() { panic; }";
        let (prog, _) = lower_src(src);
        let f = &prog.funcs[0];
        let has_panic = f.blocks.iter().any(|b| matches!(b.term, Terminator::Panic));
        assert!(has_panic, "expected a Terminator::Panic");
    }

    #[test]
    fn panic_with_arg_evaluates_then_aborts() {
        // `panic(g());` evaluates the argument (a call -> a Call rvalue) for its
        // side effects, then aborts; statements after it on the path are dead.
        use rv_ir::{RValue, Stmt};
        let src = "\
fn g() -> i64 { return 1; }
fn f() {
    panic(g());
    let dead = 99;
}";
        let (prog, mut syms) = lower_src(src);
        let f = prog.funcs.iter().find(|f| f.name == syms.intern("f")).unwrap();
        // The argument call is emitted as a Call rvalue before the abort.
        let g = syms.intern("g");
        let has_call = f.blocks.iter().flat_map(|b| &b.stmts).any(|s| {
            matches!(s, Stmt::Assign(_, RValue::Call(callee, _)) if *callee == g)
        });
        assert!(has_call, "expected the panic argument call to be evaluated");
        // The block ends in Panic.
        let has_panic = f.blocks.iter().any(|b| matches!(b.term, Terminator::Panic));
        assert!(has_panic, "expected a Terminator::Panic");
        // The trailing `let dead = 99;` is unreachable, so the constant 99 must not
        // be assigned anywhere.
        let has_dead = f.blocks.iter().flat_map(|b| &b.stmts).any(|s| {
            matches!(s, Stmt::Assign(_, RValue::Use(rv_ir::Operand::Const(rv_ir::Const::Int(99)))))
        });
        assert!(!has_dead, "statements after panic must be dead");
    }

    #[test]
    fn try_operator_lowers_to_match_with_bind_and_early_return() {
        // (b) `e?` on a `Result<i64, i64>` lowers to a `Match` with a success-bind
        // arm and an early-return-Err arm.
        use rv_ir::{AggKind, Operand, Proj, RValue, Stmt};
        let src = "\
enum Result<T, E> { Ok(T), Err(E) }
fn f(r: Result<i64, i64>) -> Result<i64, i64> {
    let v = r?;
    return Result::Ok(v);
}";
        let (prog, mut syms) = lower_src(src);
        let f = prog.funcs.iter().find(|f| f.name == syms.intern("f")).unwrap();

        // `Ok` is variant 0, `Err` is variant 1 (declaration order).
        // The `?` emits a Match with exactly two explicit arms (success + failure)
        // and no `otherwise`.
        let (arms, otherwise) = f
            .blocks
            .iter()
            .find_map(|b| match &b.term {
                Terminator::Match { arms, otherwise, .. } => Some((arms.clone(), *otherwise)),
                _ => None,
            })
            .expect("expected a Match terminator for `?`");
        assert_eq!(arms.len(), 2, "expected two explicit match arms");
        assert!(otherwise.is_none(), "expected no `otherwise` arm");
        assert!(arms.iter().any(|a| a.variant == 0), "expected a success (Ok=0) arm");
        assert!(arms.iter().any(|a| a.variant == 1), "expected a failure (Err=1) arm");

        // The success arm binds the payload via Downcast(0)+Field(0).
        let binds_success = f.blocks.iter().flat_map(|b| &b.stmts).any(|s| match s {
            Stmt::Assign(_, RValue::Use(Operand::Copy(place))) => {
                matches!(place.proj.as_slice(), [Proj::Downcast(0), Proj::Field(0)])
            }
            _ => false,
        });
        assert!(binds_success, "expected a Downcast(0)+Field(0) success binder");

        // The failure arm re-aggregates `Result::Err(_)` (variant 1) and returns it.
        // Find the block that constructs the Err aggregate and ends in a Return.
        let early_returns_err = f.blocks.iter().any(|b| {
            let builds_err = b.stmts.iter().any(|s| {
                matches!(
                    s,
                    Stmt::Assign(_, RValue::Aggregate(AggKind::Variant(_, 1), _))
                )
            });
            builds_err && matches!(b.term, Terminator::Return(_))
        });
        assert!(
            early_returns_err,
            "expected a failure arm that rebuilds Err and early-returns it"
        );

        // The failure re-aggregation reads the failure payload back from the
        // scrutinee via Downcast(1)+Field(0).
        let reads_err_payload = f.blocks.iter().flat_map(|b| &b.stmts).any(|s| match s {
            Stmt::Assign(_, RValue::Aggregate(AggKind::Variant(_, 1), ops)) => {
                matches!(ops.as_slice(), [Operand::Copy(p)]
                    if matches!(p.proj.as_slice(), [Proj::Downcast(1), Proj::Field(0)]))
            }
            _ => false,
        });
        assert!(reads_err_payload, "expected the failure payload to be read from the scrutinee");
    }

    #[test]
    fn try_operator_on_option_returns_none() {
        // `e?` on an `Option`-like enum: `None` is the (no-payload) failure variant,
        // re-aggregated with zero operands and early-returned.
        use rv_ir::{AggKind, RValue, Stmt};
        let src = "\
enum Option<T> { None, Some(T) }
fn f(o: Option<i64>) -> Option<i64> {
    let v = o?;
    return Option::Some(v);
}";
        let (prog, mut syms) = lower_src(src);
        let f = prog.funcs.iter().find(|f| f.name == syms.intern("f")).unwrap();

        // `None` is variant 0 (the failure), `Some` is variant 1 (the success).
        // The failure re-aggregation has zero operands (a unit variant) and returns.
        let none_return = f.blocks.iter().any(|b| {
            let builds_none = b.stmts.iter().any(|s| {
                matches!(
                    s,
                    Stmt::Assign(_, RValue::Aggregate(AggKind::Variant(_, 0), ops)) if ops.is_empty()
                )
            });
            builds_none && matches!(b.term, Terminator::Return(_))
        });
        assert!(none_return, "expected a `None` re-aggregation that is early-returned");
    }

    #[test]
    fn try_operator_on_unresolvable_enum_errors() {
        // A `?` whose operand enum can't be resolved is a clear error.
        let mut syms = rv_core::Symbols::new();
        let src = "fn f(x: i64) -> i64 { let v = x?; return v; }";
        let module = rv_syntax::parse(src, &mut syms).unwrap();
        let err = match lower(&module, &mut syms) {
            Ok(_) => panic!("expected lowering to fail"),
            Err(e) => e,
        };
        assert!(err.contains("`?`"), "got: {err}");
    }

    #[test]
    fn return_unit_is_appended_when_missing() {
        use rv_ir::{Const, Operand};
        let src = "fn f() { let a = 1; }";
        let (prog, _) = lower_src(src);
        let f = &prog.funcs[0];
        let last = f.blocks.last().unwrap();
        assert!(matches!(
            last.term,
            Terminator::Return(Operand::Const(Const::Unit))
        ));
    }
}
