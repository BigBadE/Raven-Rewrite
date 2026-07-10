//! Surface syntax: lexer + parser + AST.
//!
//! The single public entry point is [`parse`], which turns source text into an
//! [`ast::Module`]. Names are interned into the caller-supplied
//! [`rv_core::Symbols`] so the same symbol table threads through lowering.

pub mod ast;
pub mod fragment;
mod lexer;
mod parser;

pub use fragment::{classify, Fragment};
use parser::Parser;
use rv_core::Symbols;

/// Parse `src` into a [`ast::Module`].
///
/// Identifiers are interned into `syms`. On any lexing or parsing error, returns
/// `Err` with a message that includes the offending source line.
pub fn parse(src: &str, syms: &mut Symbols) -> Result<ast::Module, String> {
    let toks = lexer::lex(src)?;
    let mut p = Parser::new(&toks, syms);
    p.parse_module()
}

#[cfg(test)]
mod tests {
    use super::ast::*;
    use super::*;
    use rv_core::BinOp;

    #[test]
    fn parses_a_function_with_clauses() {
        let mut syms = Symbols::new();
        let m = parse(
            "fn div(x: i64, y: i64) -> i64 requires y != 0; { return x / y; }",
            &mut syms,
        )
        .unwrap();
        assert_eq!(m.items.len(), 1);
        let Item::Fn(f) = &m.items[0] else { panic!("expected a function item") };
        assert_eq!(f.params.len(), 2);
        assert_eq!(f.ret, Some(Ty::I64));
        assert_eq!(f.requires.len(), 1);
        assert_eq!(f.ensures.len(), 0);
        assert_eq!(f.body.stmts.len(), 1);
    }

    #[test]
    fn parses_runtime_float_and_string_types() {
        let mut syms = Symbols::new();
        let module = parse("fn f(x: f64, s: String) -> f64 { return x; }", &mut syms).unwrap();
        let Item::Fn(f) = &module.items[0] else { panic!("expected function") };
        assert_eq!(f.params[0].ty, Ty::F64);
        assert_eq!(f.params[1].ty, Ty::String);
        assert_eq!(f.ret, Some(Ty::F64));
    }

    #[test]
    fn parses_fixed_width_integer_types() {
        let mut syms = Symbols::new();
        let module = parse("fn f(x: u8) -> i32 { return 0; }", &mut syms).unwrap();
        let Item::Fn(f) = &module.items[0] else { panic!("expected function") };
        assert_eq!(f.params[0].ty, Ty::IntN(rv_core::IntTy { signed: false, bits: 8 }));
        assert_eq!(f.ret, Some(Ty::IntN(rv_core::IntTy { signed: true, bits: 32 })));
    }

    #[test]
    fn scalar_parameter_refinement_stays_executable() {
        let mut syms = Symbols::new();
        let module = parse("fn recip(x: i64 where x != 0) -> i64 { return 1 / x; }", &mut syms)
            .unwrap();
        assert_eq!(classify(&module), vec![Fragment::Exec]);
    }

    #[test]
    fn parses_refinement_type_alias() {
        let mut syms = Symbols::new();
        let module = parse("type NonZero = i64 where self != 0;", &mut syms).unwrap();
        let Item::TypeAlias(alias) = &module.items[0] else {
            panic!("expected type alias")
        };
        assert_eq!(syms.resolve(alias.name), "NonZero");
        assert_eq!(alias.base, Ty::I64);
        assert_eq!(classify(&module), vec![Fragment::Exec]);
    }

    #[test]
    fn respects_precedence() {
        let mut syms = Symbols::new();
        let m = parse("fn f() -> i64 { return 1 + 2 * 3; }", &mut syms).unwrap();
        let Item::Fn(f) = &m.items[0] else { panic!("expected a function item") };
        // Expect `1 + (2 * 3)`, i.e. an Add at the root whose RHS is a Mul.
        let Stmt::Return(Some(Expr::Bin(BinOp::Add, _, rhs))) = &f.body.stmts[0] else {
            panic!("expected a return of an addition");
        };
        assert!(matches!(**rhs, Expr::Bin(BinOp::Mul, _, _)));
    }

    #[test]
    fn parses_control_flow() {
        let mut syms = Symbols::new();
        let src = "fn f(n: i64) -> i64 {\
            let mut_x = 0;\
            if n > 0 { return 1; } else { return 0; }\
        }";
        // `mut_x` is just an identifier here.
        let m = parse(src, &mut syms).unwrap();
        let Item::Fn(f) = &m.items[0] else { panic!("expected a function item") };
        assert_eq!(f.body.stmts.len(), 2);
        assert!(matches!(f.body.stmts[1], Stmt::If { .. }));
    }

    #[test]
    fn assignment_vs_expr_disambiguation() {
        let mut syms = Symbols::new();
        let m = parse("fn f() { let a = 1; a = a + 1; g(); }", &mut syms).unwrap();
        let Item::Fn(f) = &m.items[0] else { panic!("expected a function item") };
        assert!(matches!(f.body.stmts[0], Stmt::Let { .. }));
        assert!(matches!(f.body.stmts[1], Stmt::Assign { .. }));
        assert!(matches!(f.body.stmts[2], Stmt::Expr(Expr::Call { .. })));
    }

    #[test]
    fn reports_line_on_error() {
        let mut syms = Symbols::new();
        let err = parse("fn f() {\n  let = 1;\n}", &mut syms).unwrap_err();
        assert!(err.contains("line 2"), "got: {err}");
    }

    #[test]
    fn parses_struct_decl_and_literal_and_field_access() {
        let mut syms = Symbols::new();
        let src = "\
struct Point { x: i64, y: i64 }
fn f() -> i64 {
    let p = Point { x: 1, y: 2 };
    return p.x;
}";
        let m = parse(src, &mut syms).unwrap();
        // First item is the struct decl with two fields.
        let Item::Struct(s) = &m.items[0] else {
            panic!("expected a struct item");
        };
        assert_eq!(s.fields.len(), 2);

        let Item::Fn(f) = &m.items[1] else { panic!("expected a function item") };
        // `let p = Point { x: 1, y: 2 };`
        let Stmt::Let { init: Expr::StructLit { fields, .. }, .. } = &f.body.stmts[0] else {
            panic!("expected a struct-literal let");
        };
        assert_eq!(fields.len(), 2);
        // `return p.x;`
        let Stmt::Return(Some(Expr::Field { .. })) = &f.body.stmts[1] else {
            panic!("expected a field-access return");
        };
    }

    #[test]
    fn parses_enum_match_and_ctor() {
        let mut syms = Symbols::new();
        let src = "\
enum Opt { None, Some(i64) }
fn f() -> i64 {
    let o = Opt::Some(5);
    match o {
        Opt::Some(v) => { return v; }
        _ => { return 0; }
    }
}";
        let m = parse(src, &mut syms).unwrap();
        let Item::Enum(e) = &m.items[0] else { panic!("expected an enum item") };
        assert_eq!(e.variants.len(), 2);
        assert_eq!(e.variants[0].fields.len(), 0); // unit variant `None`
        assert_eq!(e.variants[1].fields.len(), 1); // `Some(i64)`

        let Item::Fn(f) = &m.items[1] else { panic!("expected a function item") };
        let Stmt::Let { init: Expr::EnumCtor { args, .. }, .. } = &f.body.stmts[0] else {
            panic!("expected an enum-ctor let");
        };
        assert_eq!(args.len(), 1);
        let Stmt::Match { arms, .. } = &f.body.stmts[1] else {
            panic!("expected a match statement");
        };
        assert_eq!(arms.len(), 2);
        assert!(matches!(arms[0].pat, Pattern::Variant { .. }));
        assert!(matches!(arms[1].pat, Pattern::Wildcard));
    }

    #[test]
    fn parses_while_with_invariants() {
        let mut syms = Symbols::new();
        let src = "\
fn f(n: i64) -> i64 {
    let i = 0;
    while i < n invariant i >= 0; invariant i <= n; {
        i = i + 1;
    }
    return i;
}";
        let m = parse(src, &mut syms).unwrap();
        let Item::Fn(f) = &m.items[0] else { panic!("expected a function item") };
        let Stmt::While { invariants, .. } = &f.body.stmts[1] else {
            panic!("expected a while statement");
        };
        assert_eq!(invariants.len(), 2);
    }

    #[test]
    fn parses_reference_type_and_borrow_and_deref() {
        let mut syms = Symbols::new();
        let src = "\
fn f(r: &i64, m: &mut i64) -> i64 {
    let a = &r;
    let b = &mut a;
    *m = 5;
    return *r;
}";
        let m = parse(src, &mut syms).unwrap();
        let Item::Fn(f) = &m.items[0] else { panic!("expected a function item") };

        // Parameter types: `&i64` (shared) and `&mut i64` (mutable).
        assert_eq!(
            f.params[0].ty,
            Ty::Ref { mutable: false, inner: Box::new(Ty::I64) }
        );
        assert_eq!(
            f.params[1].ty,
            Ty::Ref { mutable: true, inner: Box::new(Ty::I64) }
        );

        // `let a = &r;` — shared borrow.
        let Stmt::Let { init: Expr::Ref { mutable: false, .. }, .. } = &f.body.stmts[0] else {
            panic!("expected a shared-borrow let");
        };
        // `let b = &mut a;` — mutable borrow.
        let Stmt::Let { init: Expr::Ref { mutable: true, .. }, .. } = &f.body.stmts[1] else {
            panic!("expected a mutable-borrow let");
        };
        // `*m = 5;` — store through a reference.
        let Stmt::DerefAssign { place: Expr::Deref(_), .. } = &f.body.stmts[2] else {
            panic!("expected a deref-assignment");
        };
        // `return *r;` — read through a reference.
        let Stmt::Return(Some(Expr::Deref(_))) = &f.body.stmts[3] else {
            panic!("expected a return of a dereference");
        };
    }

    #[test]
    fn parses_generic_fn_struct_enum() {
        let mut syms = Symbols::new();
        let src = "\
fn id<T>(x: T) -> T { return x; }
struct Pair<A, B> { a: A, b: B }
enum Option<T> { None, Some(T) }";
        let m = parse(src, &mut syms).unwrap();

        let Item::Fn(f) = &m.items[0] else { panic!("expected a function item") };
        assert_eq!(f.generics.len(), 1);
        // `x: T` parses as a bare ADT-named type (reinterpreted as a param later).
        assert_eq!(f.params[0].ty, Ty::Adt(syms.intern("T")));

        let Item::Struct(s) = &m.items[1] else { panic!("expected a struct item") };
        assert_eq!(s.generics.len(), 2);
        assert_eq!(s.fields.len(), 2);

        let Item::Enum(e) = &m.items[2] else { panic!("expected an enum item") };
        assert_eq!(e.generics.len(), 1);
        assert_eq!(e.variants[1].fields.len(), 1); // `Some(T)`
    }

    #[test]
    fn parses_generic_bounds_and_generic_type_use() {
        let mut syms = Symbols::new();
        // A bounded type parameter and a generic type application in a field.
        let src = "struct Box<T: Clone + Debug> { value: Option<T> }";
        let m = parse(src, &mut syms).unwrap();
        let Item::Struct(s) = &m.items[0] else { panic!("expected a struct item") };
        assert_eq!(s.generics[0].bounds.len(), 2);
        // `value: Option<T>` is a generic type application.
        assert!(matches!(s.fields[0].ty, Ty::Generic { .. }));
    }

    #[test]
    fn parses_trait_impl_and_method_call() {
        let mut syms = Symbols::new();
        let src = "\
trait Summable { fn sum(self) -> i64; }
struct Point { x: i64, y: i64 }
impl Point { fn sum(self) -> i64 { return self.x + self.y; } }
impl Summable for Point { fn total(self) -> i64 { return self.x; } }
fn f() -> i64 {
    let p = Point { x: 1, y: 2 };
    return p.sum();
}";
        let m = parse(src, &mut syms).unwrap();

        let Item::Trait(t) = &m.items[0] else { panic!("expected a trait item") };
        assert_eq!(t.methods.len(), 1);
        assert!(t.methods[0].has_self);

        let Item::Impl(inherent) = &m.items[2] else { panic!("expected an impl item") };
        assert_eq!(inherent.trait_name, None);
        assert_eq!(inherent.methods.len(), 1);
        assert!(inherent.methods[0].has_self);

        let Item::Impl(trait_impl) = &m.items[3] else { panic!("expected a trait-impl item") };
        assert!(trait_impl.trait_name.is_some());

        let Item::Fn(f) = &m.items[4] else { panic!("expected a function item") };
        // `p.sum()` parses as a method call.
        let Stmt::Return(Some(Expr::MethodCall { method, args, .. })) = &f.body.stmts[1] else {
            panic!("expected a method-call return");
        };
        assert_eq!(*method, syms.intern("sum"));
        assert_eq!(args.len(), 0);
    }

    #[test]
    fn method_with_self_and_extra_params() {
        let mut syms = Symbols::new();
        let src = "impl Point { fn add(self, dx: i64) -> i64 { return self.x + dx; } }";
        let m = parse(src, &mut syms).unwrap();
        let Item::Impl(im) = &m.items[0] else { panic!("expected an impl item") };
        assert!(im.methods[0].has_self);
        assert_eq!(im.methods[0].params.len(), 1); // just `dx` (self is separate)
    }

    #[test]
    fn parses_panic_with_and_without_arg() {
        let mut syms = Symbols::new();
        let src = "\
fn f(x: i64) {
    panic;
}
fn g(x: i64) {
    panic(x);
}";
        let m = parse(src, &mut syms).unwrap();
        // `panic;` — no argument.
        let Item::Fn(f) = &m.items[0] else { panic!("expected a function item") };
        assert!(matches!(f.body.stmts[0], Stmt::Panic(None)));
        // `panic(x);` — argument evaluated for side effects.
        let Item::Fn(g) = &m.items[1] else { panic!("expected a function item") };
        assert!(matches!(g.body.stmts[0], Stmt::Panic(Some(Expr::Var(_)))));
    }

    #[test]
    fn parses_try_postfix_operator() {
        let mut syms = Symbols::new();
        // `g()?` parses as `Try(Call ...)`; the `?` binds as a postfix operator.
        let src = "fn f() -> i64 { let v = g()?; return v; }";
        let m = parse(src, &mut syms).unwrap();
        let Item::Fn(f) = &m.items[0] else { panic!("expected a function item") };
        let Stmt::Let { init, .. } = &f.body.stmts[0] else {
            panic!("expected a let binding");
        };
        let Expr::Try(inner) = init else { panic!("expected a Try expression") };
        assert!(matches!(**inner, Expr::Call { .. }));
    }

    #[test]
    fn struct_literal_disabled_in_if_condition() {
        // `if x { ... }` must parse `x` as a bare var, not a struct literal.
        let mut syms = Symbols::new();
        let src = "fn f(x: bool) -> i64 { if x { return 1; } else { return 0; } }";
        let m = parse(src, &mut syms).unwrap();
        let Item::Fn(f) = &m.items[0] else { panic!("expected a function item") };
        let Stmt::If { cond, .. } = &f.body.stmts[0] else {
            panic!("expected an if statement");
        };
        assert!(matches!(cond, Expr::Var(_)));
    }
}
