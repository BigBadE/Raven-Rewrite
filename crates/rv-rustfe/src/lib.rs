//! Real-Rust front-end: parse genuine `.rs` source with **rust-analyzer's**
//! parser (`ra_ap_syntax`) and lower a well-scoped **subset** of Rust to raven's
//! IR (`rv_ir::Program<rv_ir::Parsed>`), so the verifier can consume real files.
//!
//! Lowering walks `ra_ap_syntax`'s typed AST (`ast::Item`/`ast::Expr`/...). The
//! parser is vendored as a normal dependency — owned, edition-aware, and
//! error-tolerant — and the IR it produces feeds the unchanged downstream phases
//! (infer / verify / codegen).
//!
//! # Supported subset
//! * **Items:** `fn`, `struct`, `enum`, `impl`/`trait` methods, inline `mod`,
//!   `use`; generics `<T>` (erased).
//! * **Types:** `bool`, `()`, named ADTs, tuples, fixed arrays, `Vec<T>`,
//!   `&T`/`&mut T`, type params; sized ints (`i8`..`u32` carry width), wider
//!   ints -> default `Int`.
//! * **Statements / control flow:** `let` (incl. tuple/struct destructuring),
//!   assignment + compound assignment, `if`/`else`, `while`/`loop`/`for a..b`
//!   with `break`/`continue`, `return`, `match`, and `?`.
//! * **Expressions:** literals, calls + method calls (desugared), field/tuple/
//!   index access, struct/enum/tuple/array literals, `&`/`&mut`/`*`, `Vec` ops,
//!   Option/Result combinators, `wrapping_*`, `panic!`/`assert!`/`assert_eq!`.
//! * **Specs:** `#[requires(..)]` / `#[ensures(..)]` -> `pre`/`post` `Prop`s.
//!
//! Anything outside the subset produces a clear `Err(String)`.

mod ra;

use rv_core::Symbols;
use rv_ir::{Parsed, Program};

/// Parse Rust `src` and lower the supported subset to `Program<Parsed>`.
///
/// Identifiers are interned into the caller's `Symbols`. On any parse error or
/// unsupported construct, returns `Err` with a located, human-readable message.
pub fn parse_rust(src: &str, syms: &mut Symbols) -> Result<Program<Parsed>, String> {
    parse_rust_modules(&[src], syms)
}

/// Parse and lower **multiple** Rust source files into one `Program`, sharing the
/// caller's `Symbols`. All type declarations across all files are collected before
/// any body is lowered, so references may cross file boundaries. Inline `mod m { .. }`
/// blocks are flattened and `use` is accepted; a path-qualified reference resolves by
/// its last segment (see `ra::parse_modules`).
pub fn parse_rust_modules(sources: &[&str], syms: &mut Symbols) -> Result<Program<Parsed>, String> {
    ra::parse_modules(sources, syms)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rv_ir::{AggKind, Operand, Proj, RValue, Stmt, Terminator, TypeDef};

    /// Parse a source string, panicking with the error on failure.
    fn parse(src: &str) -> (Program<Parsed>, Symbols) {
        let mut syms = Symbols::new();
        let prog = parse_rust(src, &mut syms).expect("parse_rust failed");
        (prog, syms)
    }

    /// Expect a parse error and return it (Program has no `Debug`, so we can't
    /// use `unwrap_err`).
    fn expect_err(r: Result<Program<Parsed>, String>) -> String {
        match r {
            Ok(_) => panic!("expected an error, but parsing succeeded"),
            Err(e) => e,
        }
    }

    #[test]
    fn parses_add_and_main() {
        // The headline example from the task: two real Rust functions, a call.
        let src = "\
fn add(x: i64, y: i64) -> i64 { return x + y; }
fn main() -> i64 { let a: i64 = 2; let b: i64 = 3; return add(a, b); }";
        let (prog, mut syms) = parse(src);
        assert_eq!(prog.funcs.len(), 2);
        // No user-declared types — only the injected `Option`/`Result` prelude.
        assert_eq!(prog.types.len(), 2);

        let add = &prog.funcs[0];
        assert_eq!(add.name, syms.intern("add"));
        assert_eq!(add.params.len(), 2);
        assert_eq!(add.blocks.len(), 1);
        assert!(matches!(add.blocks[0].term, Terminator::Return(_)));

        // `main` has a Call to `add` with two operands.
        let main = &prog.funcs[1];
        let call_args = main
            .blocks
            .iter()
            .flat_map(|b| &b.stmts)
            .find_map(|s| match s {
                Stmt::Assign(_, RValue::Call(callee, args)) if *callee == syms.intern("add") => Some(args.clone()),
                _ => None,
            })
            .expect("expected a Call to add");
        assert_eq!(call_args.len(), 2);
    }

    #[test]
    fn trailing_expression_is_a_return() {
        // `fn h() -> i64 { 5 }` — block-value expression with no `return`.
        let src = "fn h() -> i64 { 5 }";
        let (prog, _) = parse(src);
        let h = &prog.funcs[0];
        assert!(matches!(
            h.blocks.last().unwrap().term,
            Terminator::Return(Operand::Const(rv_ir::Const::Int(5)))
        ));
    }

    #[test]
    fn if_else_produces_four_blocks() {
        let src = "fn f(n: i64) -> i64 { if n > 0 { return 1; } else { return 0; } }";
        let (prog, _) = parse(src);
        let f = &prog.funcs[0];
        // entry(branch) + then + else + join = 4.
        assert_eq!(f.blocks.len(), 4, "blocks: {}", f.blocks.len());
        let entry = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
        assert!(matches!(entry.term, Terminator::Branch { .. }));
    }

    #[test]
    fn while_has_a_back_edge() {
        let src = "fn f(n: i64) -> i64 { let mut i = 0; while i < n { i = i + 1; } return i; }";
        let (prog, _) = parse(src);
        let f = &prog.funcs[0];
        let has_back_edge = f.blocks.iter().any(|bl| match &bl.term {
            Terminator::Goto(t) => t.0 <= bl.id.0,
            _ => false,
        });
        assert!(has_back_edge, "expected a loop back-edge");
        assert!(f.blocks.iter().any(|bl| matches!(bl.term, Terminator::Branch { .. })));
    }

    #[test]
    fn struct_literal_and_field_access() {
        let src = "\
struct Point { x: i64, y: i64 }
fn f() -> i64 {
    let p = Point { x: 1, y: 2 };
    return p.x;
}";
        let (prog, _) = parse(src);
        // The user `Point` struct (at index 0) plus the 2 prelude enums.
        assert_eq!(prog.types.len(), 3);
        assert!(matches!(&prog.types[0], TypeDef::Struct { fields, .. } if fields.len() == 2));

        let f = &prog.funcs[0];
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

        let reads_field0 = f.blocks.iter().any(|b| match &b.term {
            Terminator::Return(Operand::Copy(place)) => matches!(place.proj.as_slice(), [Proj::Field(0)]),
            _ => false,
        });
        assert!(reads_field0, "expected a Return reading field 0");
    }

    #[test]
    fn enum_struct_and_match() {
        // The required struct+enum+match example: assert func/type counts and the
        // match lowers to the expected terminator + binder.
        let src = "\
struct Wrap { v: i64 }
enum Opt { None, Some(i64) }
fn f() -> i64 {
    let o = Opt::Some(5);
    match o {
        Opt::Some(v) => { return v; }
        _ => { return 0; }
    }
}
fn g(w: Wrap) -> i64 { return w.v; }";
        let (prog, _) = parse(src);
        // Two user types (Wrap, Opt) + the 2 prelude enums; two funcs (f, g).
        assert_eq!(prog.types.len(), 4);
        assert_eq!(prog.funcs.len(), 2);

        let f = &prog.funcs[0];
        // `Opt::Some(5)` -> Aggregate(Variant(_, 1)).
        let has_variant_agg = f
            .blocks
            .iter()
            .flat_map(|b| &b.stmts)
            .any(|s| matches!(s, Stmt::Assign(_, RValue::Aggregate(AggKind::Variant(_, 1), _))));
        assert!(has_variant_agg, "expected Aggregate(Variant(_, 1))");

        // A Match terminator: one explicit arm (Some) + an `otherwise` (_).
        let (arms, otherwise) = f
            .blocks
            .iter()
            .find_map(|b| match &b.term {
                Terminator::Match { arms, otherwise, .. } => Some((arms.clone(), *otherwise)),
                _ => None,
            })
            .expect("expected a Match terminator");
        assert_eq!(arms.len(), 1);
        assert_eq!(arms[0].variant, 1);
        assert!(otherwise.is_some());

        // The Some arm binds `v` via Downcast(1)+Field(0).
        let binds_v = f.blocks.iter().flat_map(|b| &b.stmts).any(|s| match s {
            Stmt::Assign(_, RValue::Use(Operand::Copy(place))) => {
                matches!(place.proj.as_slice(), [Proj::Downcast(1), Proj::Field(0)])
            }
            _ => false,
        });
        assert!(binds_v, "expected a Downcast(1)+Field(0) binder for `v`");
    }

    #[test]
    fn references_and_deref_store() {
        let src = "\
fn f() -> i64 {
    let mut x = 0;
    let r = &mut x;
    *r = 5;
    return x;
}";
        let (prog, _) = parse(src);
        let f = &prog.funcs[0];
        let stmts: Vec<&Stmt> = f.blocks.iter().flat_map(|b| &b.stmts).collect();

        let mut_ref = stmts
            .iter()
            .any(|s| matches!(s, Stmt::Assign(_, RValue::Ref(rv_ir::BorrowKind::Mut, _))));
        assert!(mut_ref, "expected a mutable Ref rvalue for `&mut x`");

        let store = stmts.iter().any(|s| match s {
            Stmt::Assign(place, RValue::Use(Operand::Const(rv_ir::Const::Int(5)))) => {
                matches!(place.proj.last(), Some(Proj::Deref))
            }
            _ => false,
        });
        assert!(store, "expected a store of 5 through a Deref place");
    }

    #[test]
    fn reference_parameter_and_shared_read() {
        let src = "fn f(r: &i64) -> i64 { return *r; }";
        let (prog, _) = parse(src);
        let f = &prog.funcs[0];
        assert_eq!(f.params.len(), 1);
        let reads_deref = f.blocks.iter().any(|b| match &b.term {
            Terminator::Return(Operand::Copy(place)) => {
                place.local == f.params[0] && matches!(place.proj.as_slice(), [Proj::Deref])
            }
            _ => false,
        });
        assert!(reads_deref, "expected `return *r;` reading Deref of the &T param");
    }

    #[test]
    fn generic_fn_struct_and_enum() {
        let src = "\
fn id<T>(x: T) -> T { return x; }
struct Pair<A, B> { a: A, b: B }
enum Option<T> { None, Some(T) }";
        let (prog, mut syms) = parse(src);
        // The generic fn records its type params.
        let id = prog.funcs.iter().find(|f| f.name == syms.intern("id")).unwrap();
        assert_eq!(id.type_params, vec![syms.intern("T")]);

        // The generic struct: fields naming type params lower to `Ty::Param`.
        let TypeDef::Struct { type_params, fields, .. } =
            prog.types.iter().find(|t| t.name() == syms.intern("Pair")).unwrap()
        else {
            panic!("expected Pair struct");
        };
        assert_eq!(*type_params, vec![syms.intern("A"), syms.intern("B")]);
        assert_eq!(fields[0].ty, rv_core::Ty::Param(syms.intern("A")));

        // The generic enum: `Some(T)` payload is `Ty::Param(T)`.
        let TypeDef::Enum { variants, .. } =
            prog.types.iter().find(|t| t.name() == syms.intern("Option")).unwrap()
        else {
            panic!("expected Option enum");
        };
        assert_eq!(variants[1].fields, vec![rv_core::Ty::Param(syms.intern("T"))]);
    }

    #[test]
    fn requires_and_ensures_attributes() {
        // Real Rust carries specs as attributes; assert they populate pre/post.
        let src = "\
#[requires(y != 0)]
#[ensures(result == x)]
fn div(x: i64, y: i64) -> i64 { return x / y; }";
        let (prog, _) = parse(src);
        let div = &prog.funcs[0];
        // Both are non-trivial.
        assert_ne!(div.pre, rv_core::Prop::True, "requires should populate pre");
        assert_ne!(div.post, rv_core::Prop::True, "ensures should populate post");
    }

    #[test]
    fn no_attributes_means_true_specs() {
        let src = "fn f(x: i64) -> i64 { return x; }";
        let (prog, _) = parse(src);
        assert_eq!(prog.funcs[0].pre, rv_core::Prop::True);
        assert_eq!(prog.funcs[0].post, rv_core::Prop::True);
    }

    #[test]
    fn integer_width_collapses_to_int() {
        // Various integer widths all map to the IR's single Int type via params.
        let src = "fn f(a: u32, b: usize, c: i8) -> i64 { return 0; }";
        let (prog, _) = parse(src);
        assert_eq!(prog.funcs[0].params.len(), 3);
    }

    #[test]
    fn else_if_chain_lowers() {
        let src = "\
fn f(n: i64) -> i64 {
    if n > 10 { return 2; } else if n > 0 { return 1; } else { return 0; }
}";
        let (prog, _) = parse(src);
        let f = &prog.funcs[0];
        // At least two Branch terminators (outer if + the `else if`).
        let branches = f.blocks.iter().filter(|b| matches!(b.term, Terminator::Branch { .. })).count();
        assert!(branches >= 2, "expected >=2 branches, got {branches}");
    }

    #[test]
    fn return_unit_is_appended_when_missing() {
        let src = "fn f() { let a = 1; }";
        let (prog, _) = parse(src);
        let last = prog.funcs[0].blocks.last().unwrap();
        assert!(matches!(last.term, Terminator::Return(Operand::Const(rv_ir::Const::Unit))));
    }

    // ---- error reporting ----------------------------------------------------

    #[test]
    fn syntax_error_is_reported() {
        let mut syms = Symbols::new();
        let err = expect_err(parse_rust("fn f( -> i64 { 1 }", &mut syms));
        assert!(!err.is_empty());
    }

    #[test]
    fn impl_method_lowers_to_mangled_fn() {
        // An inherent method lowers to a top-level `S::m` function with `self`
        // as its first parameter, and a call site resolves to that symbol.
        let src = "\
struct S { v: i64 }
impl S { fn m(self) -> i64 { return self.v; } }
fn main() -> i64 { let s = S { v: 7 }; return s.m(); }";
        let (prog, mut syms) = parse(src);
        let mangled = syms.intern("S::m");
        let m = prog.funcs.iter().find(|f| f.name == mangled).expect("S::m lowered");
        assert_eq!(m.params.len(), 1, "self is the sole parameter");
        // `main` calls `S::m`.
        let main = prog.funcs.iter().find(|f| f.name == syms.intern("main")).unwrap();
        let calls_method = main.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(
            s, Stmt::Assign(_, RValue::Call(callee, _)) if *callee == mangled));
        assert!(calls_method, "main should call S::m");
    }

    #[test]
    fn impl_on_unknown_type_errors() {
        let mut syms = Symbols::new();
        let src = "impl Nope { fn m(self) -> i64 { return 0; } }";
        let err = expect_err(parse_rust(src, &mut syms));
        assert!(err.contains("Nope") || err.contains("unknown type"), "got: {err}");
    }

    #[test]
    fn trait_impl_methods_lower() {
        // `impl Trait for Type` methods lower the same way (trait decl ignored).
        let src = "\
struct S { v: i64 }
trait Get { fn get(self) -> i64; }
impl Get for S { fn get(self) -> i64 { return self.v; } }
fn main() -> i64 { let s = S { v: 3 }; return s.get(); }";
        let (prog, mut syms) = parse(src);
        let mangled = syms.intern("S::get");
        assert!(prog.funcs.iter().any(|f| f.name == mangled), "S::get should lower");
    }

    // ---- tuples & arrays ----------------------------------------------------

    #[test]
    fn tuple_expression_lowers_to_aggregate() {
        // `(a, b)` -> Aggregate(Tuple, [a, b]); `t.0` -> a Field(0) read.
        let src = "\
fn f() -> i64 {
    let t = (1, 2);
    return t.0;
}";
        let (prog, _) = parse(src);
        let f = &prog.funcs[0];
        let agg = f
            .blocks
            .iter()
            .flat_map(|b| &b.stmts)
            .find_map(|s| match s {
                Stmt::Assign(_, RValue::Aggregate(AggKind::Tuple, ops)) => Some(ops.clone()),
                _ => None,
            })
            .expect("expected a tuple Aggregate");
        assert_eq!(agg.len(), 2);

        let reads_field0 = f.blocks.iter().any(|b| match &b.term {
            Terminator::Return(Operand::Copy(place)) => matches!(place.proj.as_slice(), [Proj::Field(0)]),
            _ => false,
        });
        assert!(reads_field0, "expected `t.0` to read Field(0)");
    }

    #[test]
    fn array_expression_and_index() {
        // `[10, 20, 30]` -> Aggregate(Array, 3 ops); `a[i]` -> Index place read.
        let src = "\
fn f(i: i64) -> i64 {
    let a = [10, 20, 30];
    return a[i];
}";
        let (prog, _) = parse(src);
        let f = &prog.funcs[0];
        let agg = f
            .blocks
            .iter()
            .flat_map(|b| &b.stmts)
            .find_map(|s| match s {
                Stmt::Assign(_, RValue::Aggregate(AggKind::Array, ops)) => Some(ops.clone()),
                _ => None,
            })
            .expect("expected an array Aggregate");
        assert_eq!(agg.len(), 3);

        let reads_index = f.blocks.iter().any(|b| match &b.term {
            Terminator::Return(Operand::Copy(place)) => {
                matches!(place.proj.as_slice(), [Proj::Index(_)])
            }
            _ => false,
        });
        assert!(reads_index, "expected `a[i]` to read an Index place");
    }

    #[test]
    fn array_repeat_expression_replicates_element() {
        // `[0; 4]` -> Aggregate(Array, [0, 0, 0, 0]).
        let src = "fn f() -> i64 { let a = [0; 4]; return a[0]; }";
        let (prog, _) = parse(src);
        let f = &prog.funcs[0];
        let agg = f
            .blocks
            .iter()
            .flat_map(|b| &b.stmts)
            .find_map(|s| match s {
                Stmt::Assign(_, RValue::Aggregate(AggKind::Array, ops)) => Some(ops.clone()),
                _ => None,
            })
            .expect("expected an array Aggregate from `[0; 4]`");
        assert_eq!(agg.len(), 4, "`[0; 4]` should yield 4 elements");
        assert!(agg
            .iter()
            .all(|op| matches!(op, Operand::Const(rv_ir::Const::Int(0)))));
    }

    #[test]
    fn tuple_and_array_types_resolve() {
        // Param types `(i64, bool)` and `[i64; 3]` resolve to Tuple/Array `Ty`s.
        let src = "\
struct Holder { t: (i64, bool), a: [i64; 3] }";
        let (prog, mut syms) = parse(src);
        let TypeDef::Struct { fields, .. } =
            prog.types.iter().find(|t| t.name() == syms.intern("Holder")).unwrap()
        else {
            panic!("expected Holder struct");
        };
        assert_eq!(
            fields[0].ty,
            rv_core::Ty::Tuple(vec![rv_core::Ty::Int, rv_core::Ty::Bool])
        );
        assert_eq!(
            fields[1].ty,
            rv_core::Ty::Array(Box::new(rv_core::Ty::Int), 3)
        );
    }

    #[test]
    fn tuple_pattern_let_binds_elements() {
        // `let (a, b) = t;` binds `a`=Field(0), `b`=Field(1) off the tuple.
        let src = "\
fn f() -> i64 {
    let t = (4, 5);
    let (a, b) = t;
    return a + b;
}";
        let (prog, _) = parse(src);
        let f = &prog.funcs[0];
        let binds_f0 = f.blocks.iter().flat_map(|b| &b.stmts).any(|s| match s {
            Stmt::Assign(_, RValue::Use(Operand::Copy(p))) => matches!(p.proj.as_slice(), [Proj::Field(0)]),
            _ => false,
        });
        let binds_f1 = f.blocks.iter().flat_map(|b| &b.stmts).any(|s| match s {
            Stmt::Assign(_, RValue::Use(Operand::Copy(p))) => matches!(p.proj.as_slice(), [Proj::Field(1)]),
            _ => false,
        });
        assert!(binds_f0, "expected a Field(0) binder for `a`");
        assert!(binds_f1, "expected a Field(1) binder for `b`");
    }

    #[test]
    fn array_index_store() {
        // `a[i] = v;` stores through an Index place.
        let src = "\
fn f(i: i64) -> i64 {
    let mut a = [1, 2, 3];
    a[i] = 9;
    return a[0];
}";
        let (prog, _) = parse(src);
        let f = &prog.funcs[0];
        let stores_index = f.blocks.iter().flat_map(|b| &b.stmts).any(|s| match s {
            Stmt::Assign(place, RValue::Use(Operand::Const(rv_ir::Const::Int(9)))) => {
                matches!(place.proj.last(), Some(Proj::Index(_)))
            }
            _ => false,
        });
        assert!(stores_index, "expected a store of 9 through an Index place");
    }

    #[test]
    fn unknown_struct_in_literal_errors() {
        let mut syms = Symbols::new();
        let src = "fn f() -> i64 { let p = Nope { x: 1 }; return 0; }";
        let err = expect_err(parse_rust(src, &mut syms));
        assert!(err.contains("Nope") || err.contains("unknown struct"), "got: {err}");
    }
}
