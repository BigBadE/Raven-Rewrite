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

    // --- proof fragment (route to the kernel, not to rv-lower) ---
    /// `axiom name(params) : Type` — an assumed constant (no body). Used by the
    /// realization layer to name the model↔native trust assumptions.
    Axiom(AxiomDecl),
    /// `def name(params) : Type = body` — a checked definition (a `fn` whose body is
    /// a single expression; kept distinct so type-level `def`s read naturally).
    Def(DefDecl),
    /// `instance name(params) : Class args := body` — a `def` additionally registered for
    /// type-class instance resolution.
    Instance(DefDecl),
    /// `mutual { enum … enum … }` — a block of mutually-referential inductives.
    Mutual(Vec<EnumDecl>),
}

/// An `axiom name(params) : ty` declaration (proof fragment).
#[derive(Clone, Debug, PartialEq)]
pub struct AxiomDecl {
    pub name: Sym,
    pub generics: Vec<GenericParam>,
    pub params: Vec<Param>,
    pub ty: Ty,
}

/// A `def name(params) : ty = body` declaration (proof fragment).
#[derive(Clone, Debug, PartialEq)]
pub struct DefDecl {
    pub name: Sym,
    pub generics: Vec<GenericParam>,
    pub params: Vec<Param>,
    pub ty: Ty,
    pub body: Expr,
}

/// Surface type annotations: `i64`, `bool`, `()`, a named ADT, a reference, a
/// generic type application, or a bare generic type parameter.
// Not `Eq`: `Ty::Term` embeds an `Expr`, which carries `f64` (only `PartialEq`).
#[derive(Clone, Debug, PartialEq)]
pub enum Ty {
    I64,
    F64,
    Bool,
    String,
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
    /// A *dependent* type given by an arbitrary expression: a proposition
    /// (`a == b`), a type-level application (`Eval(env, e, v)`), a universe
    /// (`Type`/`Prop`), or a function type (`Nat -> Option<A>`). Produced only in
    /// the proof fragment of the unified grammar; the executable lowering never
    /// sees one (proof declarations route to the kernel, not to `rv-lower`).
    Term(Box<Expr>),
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

/// An `enum Name<G...> { V0, V1(T), ... }` declaration. In the proof fragment an
/// enum may additionally be an **indexed relation**:
/// `enum R<G…>(i0: T0, …) -> Prop { C(f: T, …) where i == e, …; … }`.
#[derive(Clone, Debug, PartialEq)]
pub struct EnumDecl {
    pub name: Sym,
    /// Generic type parameters (`enum Option<T> {..}`); empty if non-generic.
    pub generics: Vec<GenericParam>,
    /// Index binders `(i0: T0, …)` of a relation (GADT indices); empty for plain data.
    pub indices: Vec<Param>,
    /// The result sort `-> Prop` / `-> Type`; `None` defaults to `Type` (data) or, when
    /// there are indices, `Prop` (a relation).
    pub result_sort: Option<Ty>,
    pub variants: Vec<VariantDecl>,
}

/// A single enum variant: a name plus zero or more field types. A unit variant has an
/// empty `fields` vector. For relations, fields may be **named** (`field_names`, parallel
/// to `fields`) and the conclusion's indices pinned by `where` clauses (`pins`).
#[derive(Clone, Debug, PartialEq)]
pub struct VariantDecl {
    pub name: Sym,
    pub fields: Vec<Ty>,
    /// Parallel to `fields`: the field's name, or `None` for a positional field. Empty for
    /// plain data variants (all positional).
    pub field_names: Vec<Option<Sym>>,
    /// `where i == e, …` clauses pinning the conclusion's indices (relations only).
    pub pins: Vec<(Sym, Expr)>,
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

/// A single function parameter `name: ty`, optionally refined `name: ty where p`.
#[derive(Clone, Debug, PartialEq)]
pub struct Param {
    pub name: Sym,
    pub ty: Ty,
    /// A refinement predicate `where p` (a precondition that may mention the parameter).
    /// `None` for an ordinary parameter.
    pub refinement: Option<Expr>,
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
    Float(f64),
    Str(String),
    Bool(bool),
    Unit,
    /// A closure literal `|x, y| body`, lifted to a top-level function at lowering,
    /// capturing its free variables.
    Lambda { params: Vec<Sym>, body: Box<Expr> },
    /// A variable reference (includes `result` inside `ensures`).
    Var(Sym),
    /// `f(args)`
    Call { func: Sym, args: Vec<Expr> },
    /// General application `callee(args)` where the callee is an arbitrary
    /// expression (higher-order: `lookup(k)(rest)`, `diverge()(fuel)`). Produced in
    /// the proof fragment; the executable surface uses the first-order [`Expr::Call`].
    Apply { callee: Box<Expr>, args: Vec<Expr> },
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

    // --- proof fragment (the unified grammar; these reach the kernel, not the VM) ---
    /// `match scrut { | Pat => expr | … }` as an **expression** (value-producing,
    /// expression arms), distinct from the statement-level [`Stmt::Match`] whose
    /// arms are blocks. This is the form proofs and functional bodies use.
    MatchExpr { scrut: Box<Expr>, arms: Vec<(Pattern, Expr)> },
    /// A dependent lambda `fun x y => body` (kernel `fun`). Each parameter may carry
    /// an optional type annotation `fun (x: T) => …`. Distinct from the runtime
    /// closure [`Expr::Lambda`] (`|x| body`): `Fun` lowers to a kernel `Lam`.
    Fun { params: Vec<(Sym, Option<Box<Expr>>)>, body: Box<Expr> },
    /// `forall x : T, body` — a dependent function *type* (kernel `Pi`).
    Forall { params: Vec<(Sym, Box<Expr>)>, body: Box<Expr> },
    /// A let-*expression* `let x (: T)? := init in body` (kernel `Let`), distinct from the
    /// statement-level [`Stmt::Let`] — the form proof terms use (`:=` and `in`).
    LetIn { name: Sym, ty: Option<Box<Expr>>, init: Box<Expr>, body: Box<Expr> },
    /// A function/arrow type `A -> B` written in expression position.
    Arrow(Box<Expr>, Box<Expr>),
    /// The universe `Type` / `Type n`.
    TypeUniv(u32),
    /// The universe `Prop`.
    Prop,
    /// A hole `_`, solved by the kernel elaborator's inference.
    Hole,
    /// `rewrite h => body` — rewrite the goal by the equation `h`, then prove `body`.
    Rewrite { eqn: Box<Expr>, body: Box<Expr> },
    /// `decide` — discharge a decidable goal by reflection.
    Decide,
    /// `by_cases scrut => tbody | fbody` — split the goal on a `Bool` scrutinee.
    ByCases { scrut: Box<Expr>, tbody: Box<Expr>, fbody: Box<Expr> },
}
