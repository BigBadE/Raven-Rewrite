//! The surface abstract syntax tree.
//!
//! Names are stored as interned `rv_core::Sym`. Types are represented by a small
//! `Ty` enum mirroring the surface `i64` / `bool` / `()` set; the IR's richer
//! `rv_core::Ty` is only introduced later (during inference), so we keep a syntax-
//! local notion of type here.

use rv_core::{BinOp, Sym, UnOp};

/// A whole compilation unit: a sequence of top-level items.
#[derive(Clone, Debug, PartialEq)]
pub struct Module {
    pub items: Vec<Item>,
}

/// A top-level item: a function, a struct, an enum, a trait, or an impl block.
#[derive(Clone, Debug, PartialEq)]
pub enum Item {
    Fn(FnDecl),
    Struct(StructDecl),
    Enum(EnumDecl),
    /// A `trait Name { fn sig; ... }` declaration (surface-only sugar; produces no IR).
    Trait(TraitDecl),
    /// An `impl Type { methods }` or `impl Trait for Type { methods }` block.
    Impl(ImplDecl),
}

/// Surface type annotations: `i64`, `bool`, `()`, a named ADT, a reference, a
/// generic type application, or a bare generic type parameter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    I64,
    Bool,
    Unit,
    /// A user-defined struct or enum, referenced by its interned name. A bare
    /// `IDENT` whose name is one of the enclosing declaration's type parameters
    /// is reinterpreted as `Ty::Param` during lowering.
    Adt(Sym),
    /// A reference type: `&T` (`mutable == false`) or `&mut T` (`mutable == true`).
    Ref { mutable: bool, inner: Box<Ty> },
    /// A generic type application `Base<arg0, arg1, ...>` (e.g. `Option<i64>`).
    /// Lowering erases the type arguments to the base ADT (`Ty::Adt(base)`).
    Generic { base: Sym, args: Vec<Ty> },
    /// A bare type-parameter reference (`T` inside `fn f<T>(..)`). The parser
    /// never produces this directly (it can't tell a param from an ADT name);
    /// lowering rewrites a matching `Ty::Adt` into this form.
    Param(Sym),
}

/// A generic type parameter with optional trait bounds: `T` or `T: Trait0 + Trait1`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GenericParam {
    pub name: Sym,
    /// The named trait bounds (`T: A + B` -> `[A, B]`). Parsed and recorded; the
    /// current slice does not enforce them.
    pub bounds: Vec<Sym>,
}

/// A `struct Name<G...> { f0: T0, f1: T1, ... }` declaration.
#[derive(Clone, Debug, PartialEq)]
pub struct StructDecl {
    pub name: Sym,
    /// Generic type parameters (`struct Pair<A, B> {..}`); empty if non-generic.
    pub generics: Vec<GenericParam>,
    pub fields: Vec<FieldDecl>,
}

/// A single struct field `name: ty`.
#[derive(Clone, Debug, PartialEq)]
pub struct FieldDecl {
    pub name: Sym,
    pub ty: Ty,
}

/// An `enum Name<G...> { V0, V1(T), ... }` declaration.
#[derive(Clone, Debug, PartialEq)]
pub struct EnumDecl {
    pub name: Sym,
    /// Generic type parameters (`enum Option<T> {..}`); empty if non-generic.
    pub generics: Vec<GenericParam>,
    pub variants: Vec<VariantDecl>,
}

/// A single enum variant: a name plus zero or more tuple-style field types.
/// A unit variant has an empty `fields` vector.
#[derive(Clone, Debug, PartialEq)]
pub struct VariantDecl {
    pub name: Sym,
    pub fields: Vec<Ty>,
}

/// A `trait Name { fn sig; ... }` declaration. Traits are pure surface sugar:
/// they record their method *signatures* (for optional validation) and produce
/// no IR of their own.
#[derive(Clone, Debug, PartialEq)]
pub struct TraitDecl {
    pub name: Sym,
    pub methods: Vec<TraitMethodSig>,
}

/// One method signature inside a trait: `fn name(self?, params) (-> ty)? ;`.
#[derive(Clone, Debug, PartialEq)]
pub struct TraitMethodSig {
    pub name: Sym,
    /// Whether the first parameter is the receiver `self`.
    pub has_self: bool,
    pub params: Vec<Param>,
    pub ret: Option<Ty>,
}

/// An `impl Type { method* }` (inherent) or `impl Trait for Type { method* }`
/// (trait impl) block. Methods desugar to top-level functions during lowering.
#[derive(Clone, Debug, PartialEq)]
pub struct ImplDecl {
    /// For a trait impl `impl Trait for Type`, the trait name; `None` for an
    /// inherent `impl Type`. Used only for validation, never for name-mangling.
    pub trait_name: Option<Sym>,
    /// The type the methods are implemented for (the receiver's ADT name).
    pub type_name: Sym,
    pub methods: Vec<MethodDecl>,
}

/// A method inside an `impl` block: like a function, but its first parameter may
/// be the receiver `self` (whose type is the impl's `type_name`).
#[derive(Clone, Debug, PartialEq)]
pub struct MethodDecl {
    pub name: Sym,
    /// Generic type parameters on the method itself (`fn m<T>(..)`).
    pub generics: Vec<GenericParam>,
    /// Whether the method takes `self` as its first parameter.
    pub has_self: bool,
    /// The non-`self` parameters.
    pub params: Vec<Param>,
    pub ret: Option<Ty>,
    pub requires: Vec<Expr>,
    pub ensures: Vec<Expr>,
    pub body: Block,
}

/// A function declaration with its signature, spec clauses, and body.
#[derive(Clone, Debug, PartialEq)]
pub struct FnDecl {
    pub name: Sym,
    /// Generic type parameters (`fn f<T, U>(..)`); empty if non-generic.
    pub generics: Vec<GenericParam>,
    pub params: Vec<Param>,
    /// Declared return type, or `None` (defaults to unit at lowering).
    pub ret: Option<Ty>,
    /// `requires` clauses (preconditions over parameters).
    pub requires: Vec<Expr>,
    /// `ensures` clauses (postconditions; may mention `result`).
    pub ensures: Vec<Expr>,
    pub body: Block,
}

/// A single function parameter `name: ty`.
#[derive(Clone, Debug, PartialEq)]
pub struct Param {
    pub name: Sym,
    pub ty: Ty,
}

/// A braced sequence of statements.
#[derive(Clone, Debug, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
}

/// A statement.
#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
    /// `let name (: ty)? = init;`
    Let {
        name: Sym,
        ty: Option<Ty>,
        init: Expr,
    },
    /// `name = value;`
    Assign { name: Sym, value: Expr },
    /// A store through a reference: `*place = value;`. `place` is the expression
    /// being dereferenced (the reference), and `value` is the stored rvalue.
    DerefAssign { place: Expr, value: Expr },
    /// `if cond { then } (else { els })?`
    If {
        cond: Expr,
        then_blk: Block,
        else_blk: Option<Block>,
    },
    /// `while cond (invariant inv;)* { body }`
    While {
        cond: Expr,
        /// Zero or more loop-invariant clauses, in source order.
        invariants: Vec<Expr>,
        body: Block,
    },
    /// `match scrut { arm* }` as a statement (each arm body is a block).
    Match { scrut: Expr, arms: Vec<MatchArm> },
    /// `return value?;`
    Return(Option<Expr>),
    /// `assert cond;`
    Assert(Expr),
    /// `panic;` or `panic(expr);` — abort the program. An optional argument is
    /// evaluated for its side effects before the abort, then discarded.
    Panic(Option<Expr>),
    /// A bare expression evaluated for its effect: `expr;`
    Expr(Expr),
}

/// One arm of a `match`: `pattern => block`.
#[derive(Clone, Debug, PartialEq)]
pub struct MatchArm {
    pub pat: Pattern,
    pub body: Block,
}

/// A match pattern: either an enum-variant pattern with field binders, or `_`.
#[derive(Clone, Debug, PartialEq)]
pub enum Pattern {
    /// `Enum::Variant(b0, b1, ...)` (binders may be `_`); a unit/no-paren variant
    /// has an empty `binds` vector.
    Variant {
        enum_name: Sym,
        variant: Sym,
        binds: Vec<PatBind>,
    },
    /// The wildcard `_`, matching anything (the `otherwise` arm).
    Wildcard,
}

/// A single binder inside a variant pattern: a name to bind, or `_` to ignore.
#[derive(Clone, Debug, PartialEq)]
pub enum PatBind {
    Name(Sym),
    Wildcard,
}

/// An expression.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Int(i64),
    Bool(bool),
    Unit,
    /// A variable reference (includes `result` inside `ensures`).
    Var(Sym),
    /// `f(args)`
    Call { func: Sym, args: Vec<Expr> },
    /// A binary operation.
    Bin(BinOp, Box<Expr>, Box<Expr>),
    /// A unary operation.
    Un(UnOp, Box<Expr>),
    /// A struct literal `Name { f: e, ... }`. Field exprs are in source order;
    /// lowering reorders them to the struct's declared field order.
    StructLit { name: Sym, fields: Vec<(Sym, Expr)> },
    /// An enum constructor `Enum::Variant(args)` (or unit `Enum::Variant`).
    EnumCtor { enum_name: Sym, variant: Sym, args: Vec<Expr> },
    /// Field access `base.field`.
    Field { base: Box<Expr>, field: Sym },
    /// A method call `recv.method(args)`. Desugared in lowering to a resolved
    /// call on the mangled top-level function, with `recv` as the first argument.
    MethodCall { recv: Box<Expr>, method: Sym, args: Vec<Expr> },
    /// A borrow: `&expr` (`mutable == false`) or `&mut expr` (`mutable == true`).
    Ref { mutable: bool, expr: Box<Expr> },
    /// A dereference `*expr` (read through a reference).
    Deref(Box<Expr>),
    /// The error-propagation postfix operator `expr?`. On a `Result`/`Option`-like
    /// enum, it evaluates to the success payload, or early-returns the failure
    /// variant from the enclosing function.
    Try(Box<Expr>),
}
