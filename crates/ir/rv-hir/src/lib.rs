//! High-level Intermediate Representation (HIR)
//!
//! The HIR is a desugared, name-resolved representation of source code.
//! It's the first step after parsing and before type checking.

pub mod exhaustiveness;

use la_arena::{Arena, Idx};
use rv_intern::Symbol;
use rv_span::FileSpan;
use serde::{Deserialize, Serialize};

/// HIR node IDs
pub type ExprId = Idx<Expr>;
pub type StmtId = Idx<Stmt>;
pub type TypeId = Idx<Type>;
pub type PatternId = Idx<Pattern>;

/// Opaque reference to an inferred type from rv-ty (avoids circular dependency)
/// This is type-erased to break the circular dependency between rv-hir and rv-ty.
/// At runtime, rv-ty can safely transmute between Idx<Ty> and Idx<()>.
pub type InferredTyId = Idx<()>;

/// Unique ID for a macro
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct MacroId(pub u32);

/// Definition IDs for cross-referencing
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub enum DefId {
    /// Function definition
    Function(FunctionId),
    /// Type definition (struct, enum, etc.)
    Type(TypeDefId),
    /// Trait definition
    Trait(TraitId),
    /// Implementation block
    Impl(ImplId),
    /// Variable/local binding (function-scoped)
    Local {
        /// The function this local belongs to
        func: FunctionId,
        /// The local ID within that function
        local: LocalId,
    },
    /// Module definition
    Module(ModuleId),
    /// Const item definition
    Const(ConstId),
    /// Static item definition
    Static(StaticId),
}

/// Unique ID for a function
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct FunctionId(pub u32);

/// Unique ID for a type definition
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct TypeDefId(pub u32);

/// Unique ID for a trait
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct TraitId(pub u32);

/// Unique ID for an impl block
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct ImplId(pub u32);

/// Unique ID for a local variable
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct LocalId(pub u32);

/// Unique ID for a module
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct ModuleId(pub u32);

/// Attribute on an item (e.g., `#[inline]`, `#[repr(C)]`, `#[cfg(target_os = "linux")]`)
#[derive(Debug, Clone, PartialEq)]
pub struct Attribute {
    /// Attribute name (e.g., "inline", "repr", "cfg")
    pub name: Symbol,
    /// Attribute arguments
    pub args: AttributeArgs,
    /// Whether this is an inner attribute (#![...])
    pub is_inner: bool,
    /// Source location
    pub span: FileSpan,
}

/// Attribute arguments
#[derive(Debug, Clone, PartialEq)]
pub enum AttributeArgs {
    /// No arguments: `#[inline]`
    Empty,
    /// Parenthesized token list: `#[repr(C)]`, `#[cfg(target_os = "linux")]`
    Delimited(Vec<AttributeToken>),
    /// Name = value: `#[path = "foo.rs"]`
    NameValue(Symbol, String),
}

/// A token within attribute arguments
#[derive(Debug, Clone, PartialEq)]
pub enum AttributeToken {
    /// An identifier: `C`, `target_os`, `inline`
    Ident(Symbol),
    /// A string literal: `"linux"`, `"foo.rs"`
    StringLit(String),
    /// An integer literal
    IntLit(i64),
    /// Punctuation: `=`, `,`, `(`, `)`, etc.
    Punct(char),
    /// A nested group of tokens (for nested parens)
    Group(Vec<AttributeToken>),
}

/// Unique ID for a const item
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct ConstId(pub u32);

/// Unique ID for a static item
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct StaticId(pub u32);

/// Unique ID for a type alias
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct TypeAliasId(pub u32);

/// Const item definition (e.g., `const MAX: i64 = 100;`)
#[derive(Debug, Clone, PartialEq)]
pub struct ConstItem {
    /// Unique ID
    pub id: ConstId,
    /// Const name
    pub name: Symbol,
    /// Type annotation
    pub ty: TypeId,
    /// Value expression (the body containing the initializer)
    pub body: Body,
    /// Attributes
    pub attributes: Vec<Attribute>,
    /// Visibility
    pub visibility: Visibility,
    /// Source location
    pub span: FileSpan,
}

/// Static item definition (e.g., `static mut COUNTER: i64 = 0;`)
#[derive(Debug, Clone, PartialEq)]
pub struct StaticItem {
    /// Unique ID
    pub id: StaticId,
    /// Static name
    pub name: Symbol,
    /// Type annotation
    pub ty: TypeId,
    /// Value expression (the body containing the initializer)
    pub body: Body,
    /// Whether the static is mutable
    pub mutable: bool,
    /// Attributes
    pub attributes: Vec<Attribute>,
    /// Visibility
    pub visibility: Visibility,
    /// Source location
    pub span: FileSpan,
}

/// Type alias definition (e.g., `type Result<T> = core::result::Result<T, Error>;`)
#[derive(Debug, Clone, PartialEq)]
pub struct TypeAlias {
    /// Unique ID
    pub id: TypeAliasId,
    /// Alias name
    pub name: Symbol,
    /// Generic parameters
    pub generic_params: Vec<GenericParam>,
    /// The aliased type
    pub aliased_type: TypeId,
    /// Attributes
    pub attributes: Vec<Attribute>,
    /// Visibility
    pub visibility: Visibility,
    /// Source location
    pub span: FileSpan,
}

/// HIR representation of a file
#[derive(Debug, Clone, PartialEq)]
pub struct HirFile {
    /// Functions defined in this file
    pub functions: Vec<FunctionId>,
    /// Type definitions in this file
    pub types: Vec<TypeDefId>,
    /// Trait definitions in this file
    pub traits: Vec<TraitId>,
    /// Implementation blocks in this file
    pub impls: Vec<ImplId>,
    /// Root module for this file
    pub root_module: Option<ModuleId>,
}

/// Module definition
#[derive(Debug, Clone, PartialEq)]
pub struct ModuleDef {
    /// Unique ID
    pub id: ModuleId,
    /// Module name
    pub name: Symbol,
    /// Items in this module
    pub items: Vec<Item>,
    /// Submodules
    pub submodules: Vec<ModuleId>,
    /// Visibility
    pub visibility: Visibility,
    /// Source location
    pub span: FileSpan,
}

/// Item in a module (function, type, trait, impl, module, use, const, static, type alias)
#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    /// Function definition
    Function(FunctionId),
    /// Struct definition
    Struct(TypeDefId),
    /// Enum definition
    Enum(TypeDefId),
    /// Trait definition
    Trait(TraitId),
    /// Implementation block
    Impl(ImplId),
    /// Submodule
    Module(ModuleId),
    /// Use declaration (import)
    Use(UseItem),
    /// Const item
    Const(ConstId),
    /// Static item
    Static(StaticId),
    /// Type alias
    TypeAlias(TypeAliasId),
}

/// Use declaration (import)
#[derive(Debug, Clone, PartialEq)]
pub struct UseItem {
    /// Path segments (mod1::mod2::Item)
    pub path: Vec<Symbol>,
    /// Optional alias (as Name)
    pub alias: Option<Symbol>,
    /// Visibility
    pub visibility: Visibility,
    /// Source location
    pub span: FileSpan,
}

/// Path for module resolution
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModulePath {
    /// Path segments
    pub segments: Vec<Symbol>,
}

/// Module tree for a crate
#[derive(Debug, Clone, PartialEq)]
pub struct ModuleTree {
    /// All modules indexed by ID
    pub modules: std::collections::HashMap<ModuleId, ModuleDef>,
    /// Root module ID
    pub root: ModuleId,
    /// Path to module mapping
    pub path_to_module: std::collections::HashMap<ModulePath, ModuleId>,
}

/// The kind of struct definition
#[derive(Debug, Clone, PartialEq)]
pub enum StructKind {
    /// Named fields: `struct Foo { x: i64, y: i64 }`
    Named,
    /// Tuple fields: `struct Wrapper(i64)`
    Tuple,
    /// Unit struct: `struct Unit;`
    Unit,
}

/// Struct definition
#[derive(Debug, Clone, PartialEq)]
pub struct StructDef {
    /// Unique ID
    pub id: TypeDefId,
    /// Struct name
    pub name: Symbol,
    /// Visibility (pub, pub(crate), etc.)
    pub visibility: Visibility,
    /// Generic parameters
    pub generic_params: Vec<GenericParam>,
    /// Fields
    pub fields: Vec<FieldDef>,
    /// Struct kind (named, tuple, or unit)
    pub kind: StructKind,
    /// Attributes on this struct
    pub attributes: Vec<Attribute>,
    /// Source location
    pub span: FileSpan,
}

/// Field definition
#[derive(Debug, Clone, PartialEq)]
pub struct FieldDef {
    /// Field name
    pub name: Symbol,
    /// Field type
    pub ty: TypeId,
    /// Visibility
    pub visibility: Visibility,
    /// Source location
    pub span: FileSpan,
}

/// Visibility modifiers
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    /// Public (pub)
    Public,
    /// Private (default)
    Private,
}

/// Enum definition
#[derive(Debug, Clone, PartialEq)]
pub struct EnumDef {
    /// Unique ID
    pub id: TypeDefId,
    /// Enum name
    pub name: Symbol,
    /// Visibility (pub, pub(crate), etc.)
    pub visibility: Visibility,
    /// Generic parameters
    pub generic_params: Vec<GenericParam>,
    /// Variants
    pub variants: Vec<VariantDef>,
    /// Attributes on this enum
    pub attributes: Vec<Attribute>,
    /// Source location
    pub span: FileSpan,
}

/// Enum variant definition
#[derive(Debug, Clone, PartialEq)]
pub struct VariantDef {
    /// Variant name
    pub name: Symbol,
    /// Variant fields
    pub fields: VariantFields,
    /// Source location
    pub span: FileSpan,
}

/// Variant field types
#[derive(Debug, Clone, PartialEq)]
pub enum VariantFields {
    /// Unit variant (no fields)
    Unit,
    /// Tuple variant
    Tuple(Vec<TypeId>),
    /// Struct variant
    Struct(Vec<FieldDef>),
}

/// Function definition
#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    /// Unique ID
    pub id: FunctionId,
    /// Function name
    pub name: Symbol,
    /// Visibility (pub, pub(crate), etc.)
    pub visibility: Visibility,
    /// Source location
    pub span: FileSpan,
    /// Generic parameters
    pub generics: Vec<GenericParam>,
    /// Lifetime parameters (e.g., `'a`, `'b` in `fn foo<'a, 'b>`)
    pub lifetime_params: Vec<LifetimeParam>,
    /// Function parameters
    pub parameters: Vec<Parameter>,
    /// Return type
    pub return_type: Option<TypeId>,
    /// Function body
    pub body: Body,
    /// Whether this is an external function
    pub is_external: bool,
    /// Whether this function is unsafe
    pub is_unsafe: bool,
    /// Whether this function is const
    pub is_const: bool,
    /// Attributes on this function
    pub attributes: Vec<Attribute>,
    /// Self parameter (if this is a method)
    pub self_param: Option<SelfParam>,
}

/// External function declaration (from extern blocks)
#[derive(Debug, Clone, PartialEq)]
pub struct ExternalFunction {
    /// Unique ID
    pub id: FunctionId,
    /// Function name (unmangled)
    pub name: Symbol,
    /// Mangled name (for linking)
    pub mangled_name: Option<String>,
    /// Function parameters
    pub parameters: Vec<Parameter>,
    /// Return type
    pub return_type: Option<TypeId>,
    /// ABI (e.g., "C", "Rust")
    pub abi: Option<String>,
    /// Source location
    pub span: FileSpan,
}

/// Function parameter
#[derive(Debug, Clone, PartialEq)]
pub struct Parameter {
    /// Parameter name
    pub name: Symbol,
    /// Parameter type (HIR type annotation)
    pub ty: TypeId,
    /// Inferred type (populated by type inference)
    /// ARCHITECTURE: This is the single source of truth after type inference completes
    pub inferred_ty: Option<InferredTyId>,
    /// Source location
    pub span: FileSpan,
}

/// Lifetime parameter (e.g., `'a` in `fn foo<'a>(x: &'a i64)`)
#[derive(Debug, Clone, PartialEq)]
pub struct LifetimeParam {
    /// Unique ID for this lifetime
    pub id: rv_span::LifetimeId,
    /// Lifetime name (e.g., `'a`)
    pub name: Symbol,
    /// Outlives bounds (e.g., `'a: 'b` means 'a outlives 'b)
    pub bounds: Vec<rv_span::LifetimeId>,
    /// Source location
    pub span: FileSpan,
}

/// Kind of generic parameter (type or const)
#[derive(Debug, Clone, PartialEq)]
pub enum GenericParamKind {
    /// A type parameter (e.g., `T`)
    Type,
    /// A const parameter (e.g., `const N: usize`)
    Const {
        /// The type of the const parameter
        ty: TypeId,
    },
}

/// Representation of array size in type position
///
/// Used for `[T; N]` array types where N can be:
/// - A literal constant (e.g., `[i32; 10]`)
/// - A const generic parameter (e.g., `[T; N]` where `const N: usize`)
/// - An unevaluated expression (requires `generic_const_exprs` feature)
#[derive(Debug, Clone, PartialEq)]
pub enum ArraySize {
    /// A known constant size (e.g., `[T; 10]`)
    Const(usize),
    /// A reference to a const generic parameter by name (e.g., `N` in `[T; N]`)
    ConstParam(Symbol),
    /// An unevaluated const expression (for `generic_const_exprs` feature)
    /// Stores the expression text for later evaluation
    Expr(String),
    /// Size is unknown/inferred
    Infer,
}

/// Generic parameter
#[derive(Debug, Clone, PartialEq)]
pub struct GenericParam {
    /// Parameter name
    pub name: Symbol,
    /// Kind of parameter (type or const)
    pub kind: GenericParamKind,
    /// Trait bounds (only meaningful for type parameters)
    pub bounds: Vec<TraitBound>,
    /// True if `?Sized` bound is present (type parameter may be unsized)
    pub maybe_unsized: bool,
    /// Default type (e.g., `Rhs = Self` in `trait Add<Rhs = Self>`)
    pub default_type: Option<TypeId>,
    /// Source location
    pub span: FileSpan,
}

/// Trait bound
#[derive(Debug, Clone, PartialEq)]
pub struct TraitBound {
    /// Trait reference
    pub trait_ref: TraitId,
    /// Generic arguments
    pub args: Vec<TypeId>,
    /// Higher-ranked lifetime parameters (for<'a, 'b> ...)
    pub for_lifetimes: Vec<LifetimeParam>,
}

/// Trait definition
#[derive(Debug, Clone, PartialEq)]
pub struct TraitDef {
    /// Unique ID
    pub id: TraitId,
    /// Trait name
    pub name: Symbol,
    /// Visibility (pub, pub(crate), etc.)
    pub visibility: Visibility,
    /// Generic parameters
    pub generic_params: Vec<GenericParam>,
    /// Required methods (signatures only, no bodies)
    pub methods: Vec<TraitMethod>,
    /// Associated types with optional bounds
    pub associated_types: Vec<AssociatedType>,
    /// Supertraits (traits this trait extends)
    pub supertraits: Vec<TraitBound>,
    /// Whether this is an auto trait (auto trait Send {})
    pub is_auto: bool,
    /// Whether this is an unsafe trait (unsafe trait Foo {})
    pub is_unsafe: bool,
    /// Attributes on this trait
    pub attributes: Vec<Attribute>,
    /// Source location
    pub span: FileSpan,
}

/// Associated type definition in a trait
#[derive(Debug, Clone, PartialEq)]
pub struct AssociatedType {
    /// Associated type name
    pub name: Symbol,
    /// Optional type bounds
    pub bounds: Vec<TraitBound>,
    /// Default type (e.g., `type Item = i32;` in trait body)
    pub default: Option<TypeId>,
    /// Source location
    pub span: FileSpan,
}

/// Trait method signature
#[derive(Debug, Clone, PartialEq)]
pub struct TraitMethod {
    /// Method name
    pub name: Symbol,
    /// Generic parameters
    pub generics: Vec<GenericParam>,
    /// Parameters (excluding self)
    pub params: Vec<Parameter>,
    /// Return type
    pub return_type: Option<TypeId>,
    /// Whether method takes self, &self, or &mut self
    pub self_param: Option<SelfParam>,
    /// Default method body (if provided in trait definition)
    pub default_body: Option<FunctionId>,
    /// Source location
    pub span: FileSpan,
}

/// Self parameter type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelfParam {
    /// self (by value)
    Value,
    /// &self (by reference)
    Ref,
    /// &mut self (by mutable reference)
    MutRef,
}

/// Implementation block (impl Type { ... } or impl Trait for Type { ... })
#[derive(Debug, Clone, PartialEq)]
pub struct ImplBlock {
    /// Unique ID
    pub id: ImplId,
    /// Type being implemented for
    pub self_ty: TypeId,
    /// Trait being implemented (None for inherent impl)
    pub trait_ref: Option<TraitId>,
    /// Generic parameters
    pub generic_params: Vec<GenericParam>,
    /// Methods in this impl block
    pub methods: Vec<FunctionId>,
    /// Associated type implementations (type Foo = Bar;)
    pub associated_type_impls: Vec<AssociatedTypeImpl>,
    /// Where clauses for trait bounds
    pub where_clauses: Vec<WhereClause>,
    /// Whether this is an unsafe impl
    pub is_unsafe: bool,
    /// Whether this is a blanket impl (impl<T> Trait for T)
    pub is_blanket: bool,
    /// Whether this impl block was synthesized by the compiler (e.g., from
    /// blanket impl instantiation). Synthesized impls are skipped during
    /// coherence checking since they are derived from user-written impls.
    pub is_synthesized: bool,
    /// Whether this is a negative impl (impl !Trait for Type)
    pub is_negative: bool,
    /// Attributes on this impl block
    pub attributes: Vec<Attribute>,
    /// Source location
    pub span: FileSpan,
}

/// Associated type implementation in an impl block
#[derive(Debug, Clone, PartialEq)]
pub struct AssociatedTypeImpl {
    /// Associated type name
    pub name: Symbol,
    /// Concrete type
    pub ty: TypeId,
    /// Source location
    pub span: FileSpan,
}

/// Where clause for generic bounds
#[derive(Debug, Clone, PartialEq)]
pub struct WhereClause {
    /// Type being constrained
    pub ty: TypeId,
    /// Trait bounds that must be satisfied
    pub bounds: Vec<TraitBound>,
}

/// Function body
#[derive(Debug, Clone, PartialEq)]
pub struct Body {
    /// Expression arena
    pub exprs: Arena<Expr>,
    /// Statement arena
    pub stmts: Arena<Stmt>,
    /// Pattern arena
    pub patterns: Arena<Pattern>,
    /// Root expression
    pub root_expr: ExprId,
    /// Name resolution results (filled in by rv-resolve)
    pub resolution: Option<BodyResolution>,
}

/// Name resolution results for a function body
#[derive(Debug, Clone, PartialEq)]
pub struct BodyResolution {
    /// Mapping from variable expression IDs to their definitions
    pub expr_resolutions: rustc_hash::FxHashMap<ExprId, DefId>,
    /// Mapping from pattern bindings to local IDs
    pub pattern_locals: rustc_hash::FxHashMap<PatternId, LocalId>,
}

impl Body {
    /// Creates a new empty body
    #[must_use]
    pub fn new() -> Self {
        let mut exprs = Arena::new();
        // Allocate a placeholder expression for the root. This is overwritten
        // during HIR lowering when the actual function body is processed.
        let root_expr = exprs.alloc(Expr::Literal {
            kind: LiteralKind::Unit,
            span: FileSpan::synthetic(),
        });

        Self {
            exprs,
            stmts: Arena::new(),
            patterns: Arena::new(),
            root_expr,
            resolution: None,
        }
    }
}

impl Default for Body {
    fn default() -> Self {
        Self::new()
    }
}

/// HIR expressions
#[derive(Debug, Clone, PartialEq, rv_derive::Visitor)]
#[visitor(context = "Body", id_type = "ExprId")]
pub enum Expr {
    /// Literal value
    Literal {
        /// Literal kind
        kind: LiteralKind,
        /// Source location
        span: FileSpan,
    },
    /// Variable reference
    Variable {
        /// Variable name
        name: Symbol,
        /// Resolved definition (filled in by name resolution)
        def: Option<DefId>,
        /// Source location
        span: FileSpan,
    },
    /// Function call
    Call {
        /// Callee expression
        callee: ExprId,
        /// Arguments
        args: Vec<ExprId>,
        /// Explicit type arguments (turbofish: `::<T, U>`)
        type_args: Vec<TypeId>,
        /// Source location
        span: FileSpan,
    },
    /// Binary operation
    BinaryOp {
        /// Operator
        op: BinaryOp,
        /// Left operand
        left: ExprId,
        /// Right operand
        right: ExprId,
        /// Source location
        span: FileSpan,
    },
    /// Unary operation
    UnaryOp {
        /// Operator
        op: UnaryOp,
        /// Operand
        operand: ExprId,
        /// Source location
        span: FileSpan,
    },
    /// Block expression
    Block {
        /// Statements
        statements: Vec<StmtId>,
        /// Trailing expression
        expr: Option<ExprId>,
        /// Source location
        span: FileSpan,
    },
    /// If expression
    If {
        /// Condition
        condition: ExprId,
        /// Then branch
        then_branch: ExprId,
        /// Else branch
        else_branch: Option<ExprId>,
        /// Source location
        span: FileSpan,
    },
    /// Match expression
    Match {
        /// Scrutinee
        scrutinee: ExprId,
        /// Match arms
        arms: Vec<MatchArm>,
        /// Source location
        span: FileSpan,
    },
    /// Field access
    Field {
        /// Base expression
        base: ExprId,
        /// Field name
        field: Symbol,
        /// Source location
        span: FileSpan,
    },
    /// Method call
    MethodCall {
        /// Receiver
        receiver: ExprId,
        /// Method name
        method: Symbol,
        /// Arguments
        args: Vec<ExprId>,
        /// Source location
        span: FileSpan,
    },
    /// Struct construction
    StructConstruct {
        /// Struct name
        struct_name: Symbol,
        /// Resolved type definition
        def: Option<TypeDefId>,
        /// Field initializers
        fields: Vec<(Symbol, ExprId)>,
        /// Source location
        span: FileSpan,
    },
    /// Path-qualified function call (e.g., utils::get_value(42))
    PathCall {
        /// Module path segments (e.g., ["utils"] for utils::get_value)
        path: Vec<Symbol>,
        /// Function name
        function: Symbol,
        /// Arguments
        args: Vec<ExprId>,
        /// Source location
        span: FileSpan,
    },
    /// Enum variant construction
    EnumVariant {
        /// Enum name
        enum_name: Symbol,
        /// Variant name
        variant: Symbol,
        /// Resolved type definition
        def: Option<TypeDefId>,
        /// Field expressions
        fields: Vec<ExprId>,
        /// Source location
        span: FileSpan,
    },
    /// Closure expression
    Closure {
        /// Closure parameters
        params: Vec<Parameter>,
        /// Optional return type annotation
        return_type: Option<TypeId>,
        /// Body expression
        body: ExprId,
        /// Variables captured from environment (free variables in body)
        captures: Vec<Symbol>,
        /// Whether this is a `move` closure (capture by value)
        is_move: bool,
        /// Source location
        span: FileSpan,
    },
    /// Assignment expression (x = value)
    Assign {
        /// Target place expression
        target: ExprId,
        /// Value being assigned
        value: ExprId,
        /// Source location
        span: FileSpan,
    },
    /// Compound assignment expression (x += value, x -= value, etc.)
    CompoundAssign {
        /// Target place expression
        target: ExprId,
        /// Operator (Add, Sub, Mul, Div, etc.)
        op: BinaryOp,
        /// Value being assigned
        value: ExprId,
        /// Source location
        span: FileSpan,
    },
    /// While loop expression
    WhileLoop {
        /// Loop condition
        condition: ExprId,
        /// Loop body
        body: ExprId,
        /// Optional loop label
        label: Option<Symbol>,
        /// Source location
        span: FileSpan,
    },
    /// While let expression: `while let Some(x) = expr { ... }`
    WhileLet {
        /// Pattern to match
        pattern: PatternId,
        /// Expression to match against
        value: ExprId,
        /// Loop body
        body: ExprId,
        /// Optional loop label
        label: Option<Symbol>,
        /// Source location
        span: FileSpan,
    },
    /// If let expression: `if let Some(x) = expr { ... } else { ... }`
    IfLet {
        /// Pattern to match
        pattern: PatternId,
        /// Expression to match against
        value: ExprId,
        /// Then branch (executed on successful match)
        then_branch: ExprId,
        /// Else branch (executed on failed match)
        else_branch: Option<ExprId>,
        /// Source location
        span: FileSpan,
    },
    /// Infinite loop expression
    Loop {
        /// Loop body
        body: ExprId,
        /// Optional loop label
        label: Option<Symbol>,
        /// Source location
        span: FileSpan,
    },
    /// Break expression (exits a loop)
    Break {
        /// Optional value to break with
        value: Option<ExprId>,
        /// Optional label to break to
        label: Option<Symbol>,
        /// Source location
        span: FileSpan,
    },
    /// Continue expression (skips to next loop iteration)
    Continue {
        /// Optional label to continue to
        label: Option<Symbol>,
        /// Source location
        span: FileSpan,
    },
    /// Array literal expression ([1, 2, 3])
    Array {
        /// Element expressions
        elements: Vec<ExprId>,
        /// Source location
        span: FileSpan,
    },
    /// Tuple expression ((a, b, c))
    Tuple {
        /// Element expressions
        elements: Vec<ExprId>,
        /// Source location
        span: FileSpan,
    },
    /// Index expression (arr[idx])
    Index {
        /// Base expression
        base: ExprId,
        /// Index expression
        index: ExprId,
        /// Source location
        span: FileSpan,
    },
    /// Type cast expression (expr as Type)
    Cast {
        /// Expression being cast
        expr: ExprId,
        /// Target type
        ty: TypeId,
        /// Source location
        span: FileSpan,
    },
    /// Unsafe block expression
    UnsafeBlock {
        /// Inner block expression
        body: ExprId,
        /// Source location
        span: FileSpan,
    },
    /// Error expression — placeholder for expressions that failed to lower.
    ///
    /// Distinct from Unit to prevent error masking. Downstream passes must
    /// handle this variant (typically by skipping further analysis).
    Error {
        /// Source location of the failed expression
        span: FileSpan,
    },
    /// Range expression (1..10, 1..=10, ..10, 1.., ..)
    Range {
        /// Start of range (None for ..10 or ..)
        start: Option<ExprId>,
        /// End of range (None for 1.. or ..)
        end: Option<ExprId>,
        /// Whether the range is inclusive (..= vs ..)
        inclusive: bool,
        /// Source location
        span: FileSpan,
    },
    /// Try operator expression (expr?)
    Try {
        /// Expression being tried
        expr: ExprId,
        /// Source location
        span: FileSpan,
    },
    /// For loop expression (for pat in iter { body })
    ForLoop {
        /// Pattern to bind each element
        pattern: PatternId,
        /// Iterator expression
        iterator: ExprId,
        /// Loop body
        body: ExprId,
        /// Optional loop label
        label: Option<Symbol>,
        /// Source location
        span: FileSpan,
    },
    /// Box allocation expression: `Box::new(value)` or `box value`
    Box {
        /// Value to place in the box
        value: ExprId,
        /// Source location
        span: FileSpan,
    },
}

/// Match arm
#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    /// Pattern
    pub pattern: PatternId,
    /// Guard expression
    pub guard: Option<ExprId>,
    /// Body expression
    pub body: ExprId,
}

/// HIR statements
#[derive(Debug, Clone, PartialEq, rv_derive::Visitor)]
#[visitor(context = "Body", id_type = "StmtId")]
pub enum Stmt {
    /// Let binding
    Let {
        /// Pattern
        pattern: PatternId,
        /// Type annotation
        ty: Option<TypeId>,
        /// Initializer expression
        initializer: Option<ExprId>,
        /// Whether the binding is mutable
        mutable: bool,
        /// Else block for let...else pattern (diverging block executed on pattern match failure)
        else_branch: Option<ExprId>,
        /// Source location
        span: FileSpan,
    },
    /// Expression statement
    Expr {
        /// Expression
        expr: ExprId,
        /// Source location
        span: FileSpan,
    },
    /// Return statement
    Return {
        /// Return value
        value: Option<ExprId>,
        /// Source location
        span: FileSpan,
    },
    /// Box allocation: `Box::new(value)`
    Box {
        /// Value to place in the box
        value: ExprId,
        /// Source location
        span: FileSpan,
    },
}

/// Patterns
#[derive(Debug, Clone, PartialEq, rv_derive::Visitor)]
#[visitor(context = "Body", id_type = "PatternId")]
pub enum Pattern {
    /// Wildcard pattern (_)
    Wildcard {
        /// Source location
        span: FileSpan,
    },
    /// Binding pattern
    Binding {
        /// Variable name
        name: Symbol,
        /// Is mutable
        mutable: bool,
        /// Optional sub-pattern for @ patterns (x @ SomePattern)
        sub_pattern: Option<Box<PatternId>>,
        /// Source location
        span: FileSpan,
    },
    /// Literal pattern
    Literal {
        /// Literal value
        kind: LiteralKind,
        /// Source location
        span: FileSpan,
    },
    /// Tuple pattern
    Tuple {
        /// Sub-patterns
        patterns: Vec<PatternId>,
        /// Source location
        span: FileSpan,
    },
    /// Struct pattern
    Struct {
        /// Struct type
        ty: TypeId,
        /// Field patterns
        fields: Vec<(Symbol, PatternId)>,
        /// Source location
        span: FileSpan,
    },
    /// Enum pattern
    Enum {
        /// Enum name
        enum_name: Symbol,
        /// Variant name
        variant: Symbol,
        /// Resolved type definition
        def: Option<TypeDefId>,
        /// Sub-patterns
        sub_patterns: Vec<PatternId>,
        /// Source location
        span: FileSpan,
    },
    /// Or pattern (pat1 | pat2 | ...)
    Or {
        /// Alternative patterns
        patterns: Vec<PatternId>,
        /// Source location
        span: FileSpan,
    },
    /// Range pattern (start..=end or start..end)
    Range {
        /// Start of range
        start: LiteralKind,
        /// End of range
        end: LiteralKind,
        /// Whether the range is inclusive (..=) or exclusive (..)
        inclusive: bool,
        /// Source location
        span: FileSpan,
    },
    /// Slice pattern ([first, second, rest @ ..])
    Slice {
        /// Patterns at the start (before any rest pattern)
        prefix: Vec<PatternId>,
        /// Optional rest pattern (the `rest @ ..` part, binding to remaining elements)
        /// The PatternId is for the binding, if any (e.g., `rest` in `rest @ ..`)
        rest: Option<PatternId>,
        /// Patterns at the end (after the rest pattern)
        suffix: Vec<PatternId>,
        /// Source location
        span: FileSpan,
    },
}

/// HIR types
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    /// Named type
    Named {
        /// Type name
        name: Symbol,
        /// Resolved definition
        def: Option<TypeDefId>,
        /// Generic arguments
        args: Vec<TypeId>,
        /// Source location
        span: FileSpan,
    },
    /// Generic type parameter
    Generic {
        /// Parameter name
        name: Symbol,
        /// Source location
        span: FileSpan,
    },
    /// Function type
    Function {
        /// Parameter types
        params: Vec<TypeId>,
        /// Return type
        ret: Box<TypeId>,
        /// Source location
        span: FileSpan,
    },
    /// Tuple type
    Tuple {
        /// Element types
        elements: Vec<TypeId>,
        /// Source location
        span: FileSpan,
    },
    /// Reference type
    Reference {
        /// Is mutable
        mutable: bool,
        /// Inner type
        inner: Box<TypeId>,
        /// Lifetime (None = inferred)
        lifetime: Option<rv_span::LifetimeId>,
        /// Source location
        span: FileSpan,
    },
    /// Qualified path type (e.g., `Self::Item`, `<T as Trait>::Item`)
    QualifiedPath {
        /// Base type (e.g., `Self` or a concrete type)
        base: Box<TypeId>,
        /// Associated type name (e.g., `Item`)
        assoc_type: Symbol,
        /// Trait this associated type comes from (if known)
        trait_ref: Option<TraitId>,
        /// Source location
        span: FileSpan,
    },
    /// Raw pointer type (*const T or *mut T)
    Pointer {
        /// Is mutable (*mut vs *const)
        mutable: bool,
        /// Pointed-to type
        inner: Box<TypeId>,
        /// Source location
        span: FileSpan,
    },
    /// Array type ([T; N])
    Array {
        /// Element type
        element: Box<TypeId>,
        /// Array size
        size: ArraySize,
        /// Source location
        span: FileSpan,
    },
    /// Never type (!)
    Never {
        /// Source location
        span: FileSpan,
    },
    /// Dynamic trait object type (dyn Trait + Trait2)
    DynTrait {
        /// Trait bounds (stored as type-level trait refs, resolved later)
        bounds: Vec<TypeLevelTraitRef>,
        /// Source location
        span: FileSpan,
    },
    /// Impl trait type (impl Trait, used in return position or argument position)
    ImplTrait {
        /// Trait bounds
        bounds: Vec<TypeLevelTraitRef>,
        /// Source location
        span: FileSpan,
    },
    /// Unknown/error type
    Unknown {
        /// Source location
        span: FileSpan,
    },
}

/// A trait reference at the type level, before full resolution.
/// Used in `dyn Trait`, `impl Trait`, and trait bounds where we may not
/// yet have resolved the `TraitId`.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeLevelTraitRef {
    /// Trait name (may be a simple name or a path segment)
    pub name: Symbol,
    /// Generic type arguments
    pub args: Vec<TypeId>,
    /// Source location
    pub span: FileSpan,
}

/// Integer bit widths
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum IntWidth {
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
}

impl IntWidth {
    /// Size in bytes (isize uses pointer size = 8 on 64-bit)
    pub fn byte_size(self) -> usize {
        match self {
            IntWidth::I8 => 1,
            IntWidth::I16 => 2,
            IntWidth::I32 => 4,
            IntWidth::I64 => 8,
            IntWidth::I128 => 16,
            IntWidth::Isize => 8, // 64-bit target
        }
    }
}

/// Whether an integer type is signed or unsigned
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Signedness {
    Signed,
    Unsigned,
}

/// Float bit widths
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum FloatWidth {
    F32,
    F64,
}

impl FloatWidth {
    /// Size in bytes
    pub fn byte_size(self) -> usize {
        match self {
            FloatWidth::F32 => 4,
            FloatWidth::F64 => 8,
        }
    }
}

/// Literal kinds
#[derive(Debug, Clone, PartialEq)]
pub enum LiteralKind {
    /// Integer literal with optional type suffix
    Integer(i64, Option<(IntWidth, Signedness)>),
    /// Float literal with optional type suffix
    Float(f64, Option<FloatWidth>),
    /// Character literal
    Char(char),
    /// String literal
    String(String),
    /// Boolean literal
    Bool(bool),
    /// Unit literal
    Unit,
}

/// Binary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    /// Addition (+)
    Add,
    /// Subtraction (-)
    Sub,
    /// Multiplication (*)
    Mul,
    /// Division (/)
    Div,
    /// Modulo (%)
    Mod,
    /// Equality (==)
    Eq,
    /// Inequality (!=)
    Ne,
    /// Less than (<)
    Lt,
    /// Less than or equal (<=)
    Le,
    /// Greater than (>)
    Gt,
    /// Greater than or equal (>=)
    Ge,
    /// Logical AND (&&)
    And,
    /// Logical OR (||)
    Or,
    /// Bitwise AND (&)
    BitAnd,
    /// Bitwise OR (|)
    BitOr,
    /// Bitwise XOR (^)
    BitXor,
    /// Left shift (<<)
    Shl,
    /// Right shift (>>)
    Shr,
}

/// Unary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    /// Negation (-)
    Neg,
    /// Logical NOT (!)
    Not,
    /// Bitwise NOT (~)
    BitNot,
    /// Dereference (*)
    Deref,
    /// Reference (&)
    Ref,
    /// Mutable reference (&mut)
    RefMut,
}

// ── Feature Flags ───────────────────────────────────────────────────────────

/// Rust unstable features that can be enabled via `#![feature(...)]`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Feature {
    // Type system features
    /// `#![feature(adt_const_params)]` - const generics with arbitrary types
    AdtConstParams,
    /// `#![feature(associated_type_defaults)]`
    AssociatedTypeDefaults,
    /// `#![feature(const_trait_impl)]` - const trait implementations
    ConstTraitImpl,
    /// `#![feature(generic_const_exprs)]` - const generics with expressions
    GenericConstExprs,
    /// `#![feature(impl_trait_in_assoc_type)]`
    ImplTraitInAssocType,
    /// `#![feature(negative_impls)]` - `impl !Trait for Type`
    NegativeImpls,
    /// `#![feature(never_type)]` - `!` type
    NeverType,
    /// `#![feature(specialization)]` - impl specialization
    Specialization,
    /// `#![feature(trait_alias)]`
    TraitAlias,
    /// `#![feature(unsized_const_params)]`
    UnsizedConstParams,

    // Macro features
    /// `#![feature(decl_macro)]` - macro 2.0
    DeclMacro,
    /// `#![feature(macro_metavar_expr)]` - `${index()}`, `${count()}`, etc.
    MacroMetavarExpr,
    /// `#![feature(proc_macro_hygiene)]`
    ProcMacroHygiene,

    // Language features
    /// `#![feature(auto_traits)]` - `auto trait Send {}`
    AutoTraits,
    /// `#![feature(box_syntax)]` - `box` keyword
    BoxSyntax,
    /// `#![feature(generators)]` - generator functions
    Generators,
    /// `#![feature(if_let_guard)]` - `if let` in match guards
    IfLetGuard,
    /// `#![feature(inline_const)]` - inline const blocks
    InlineConst,
    /// `#![feature(let_chains)]` - `if let ... && let ...`
    LetChains,
    /// `#![feature(try_blocks)]` - `try { ... }`
    TryBlocks,

    // Intrinsic/runtime features
    /// `#![feature(core_intrinsics)]`
    CoreIntrinsics,
    /// `#![feature(lang_items)]`
    LangItems,
    /// `#![feature(no_core)]`
    NoCore,
    /// `#![feature(rustc_attrs)]` - internal rustc attributes
    RustcAttrs,

    // Stability features
    /// `#![feature(staged_api)]` - stability attributes
    StagedApi,
    /// `#![feature(structural_match)]`
    StructuralMatch,

    /// Unknown feature (for forward compatibility)
    Unknown(Symbol),
}

impl Feature {
    /// Parse a feature name string into a `Feature` variant
    #[must_use]
    pub fn from_name(name: &str, interner: &rv_intern::Interner) -> Self {
        match name {
            "adt_const_params" => Self::AdtConstParams,
            "associated_type_defaults" => Self::AssociatedTypeDefaults,
            "auto_traits" => Self::AutoTraits,
            "box_syntax" => Self::BoxSyntax,
            "const_trait_impl" => Self::ConstTraitImpl,
            "core_intrinsics" => Self::CoreIntrinsics,
            "decl_macro" => Self::DeclMacro,
            "generators" => Self::Generators,
            "generic_const_exprs" => Self::GenericConstExprs,
            "if_let_guard" => Self::IfLetGuard,
            "impl_trait_in_assoc_type" => Self::ImplTraitInAssocType,
            "inline_const" => Self::InlineConst,
            "lang_items" => Self::LangItems,
            "let_chains" => Self::LetChains,
            "macro_metavar_expr" => Self::MacroMetavarExpr,
            "negative_impls" => Self::NegativeImpls,
            "never_type" => Self::NeverType,
            "no_core" => Self::NoCore,
            "proc_macro_hygiene" => Self::ProcMacroHygiene,
            "rustc_attrs" => Self::RustcAttrs,
            "specialization" => Self::Specialization,
            "staged_api" => Self::StagedApi,
            "structural_match" => Self::StructuralMatch,
            "trait_alias" => Self::TraitAlias,
            "try_blocks" => Self::TryBlocks,
            "unsized_const_params" => Self::UnsizedConstParams,
            _ => Self::Unknown(interner.intern(name)),
        }
    }

    /// Get the feature name as a string
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            Self::AdtConstParams => "adt_const_params",
            Self::AssociatedTypeDefaults => "associated_type_defaults",
            Self::AutoTraits => "auto_traits",
            Self::BoxSyntax => "box_syntax",
            Self::ConstTraitImpl => "const_trait_impl",
            Self::CoreIntrinsics => "core_intrinsics",
            Self::DeclMacro => "decl_macro",
            Self::Generators => "generators",
            Self::GenericConstExprs => "generic_const_exprs",
            Self::IfLetGuard => "if_let_guard",
            Self::ImplTraitInAssocType => "impl_trait_in_assoc_type",
            Self::InlineConst => "inline_const",
            Self::LangItems => "lang_items",
            Self::LetChains => "let_chains",
            Self::MacroMetavarExpr => "macro_metavar_expr",
            Self::NegativeImpls => "negative_impls",
            Self::NeverType => "never_type",
            Self::NoCore => "no_core",
            Self::ProcMacroHygiene => "proc_macro_hygiene",
            Self::RustcAttrs => "rustc_attrs",
            Self::Specialization => "specialization",
            Self::StagedApi => "staged_api",
            Self::StructuralMatch => "structural_match",
            Self::TraitAlias => "trait_alias",
            Self::TryBlocks => "try_blocks",
            Self::UnsizedConstParams => "unsized_const_params",
            Self::Unknown(_) => "<unknown>",
        }
    }
}

/// Set of enabled features for a crate
#[derive(Debug, Clone, Default, PartialEq)]
pub struct FeatureSet {
    /// Enabled features
    features: std::collections::HashSet<Feature>,
}

impl FeatureSet {
    /// Create a new empty feature set
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Enable a feature
    pub fn enable(&mut self, feature: Feature) {
        self.features.insert(feature);
    }

    /// Check if a feature is enabled
    #[must_use]
    pub fn is_enabled(&self, feature: &Feature) -> bool {
        self.features.contains(feature)
    }

    /// Get all enabled features
    #[must_use]
    pub fn iter(&self) -> impl Iterator<Item = &Feature> {
        self.features.iter()
    }

    /// Number of enabled features
    #[must_use]
    pub fn len(&self) -> usize {
        self.features.len()
    }

    /// Check if no features are enabled
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.features.is_empty()
    }
}

// ── Lang Items ──────────────────────────────────────────────────────────────

/// Well-known lang items recognized via `#[lang = "..."]` attributes.
/// Each variant maps to a specific compiler behavior.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LangItem {
    // Operator traits
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Neg,
    Not,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    PartialEq,
    PartialOrd,
    Deref,
    DerefMut,
    Index,
    IndexMut,
    // Marker traits
    Sized,
    Copy,
    Send,
    Sync,
    Unpin,
    // Fn traits
    Fn,
    FnMut,
    FnOnce,
    // Memory
    Drop,
    ExchangeMalloc,
    Panic,
    PanicFmt,
    EhPersonality,
}

impl LangItem {
    /// Parse a lang item name from a `#[lang = "..."]` attribute value.
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "add" => Some(Self::Add),
            "sub" => Some(Self::Sub),
            "mul" => Some(Self::Mul),
            "div" => Some(Self::Div),
            "rem" => Some(Self::Rem),
            "neg" => Some(Self::Neg),
            "not" => Some(Self::Not),
            "bitand" => Some(Self::BitAnd),
            "bitor" => Some(Self::BitOr),
            "bitxor" => Some(Self::BitXor),
            "shl" => Some(Self::Shl),
            "shr" => Some(Self::Shr),
            "eq" => Some(Self::PartialEq),
            "partial_ord" => Some(Self::PartialOrd),
            "deref" => Some(Self::Deref),
            "deref_mut" => Some(Self::DerefMut),
            "index" => Some(Self::Index),
            "index_mut" => Some(Self::IndexMut),
            "sized" => Some(Self::Sized),
            "copy" => Some(Self::Copy),
            "send" => Some(Self::Send),
            "sync" => Some(Self::Sync),
            "unpin" => Some(Self::Unpin),
            "fn" => Some(Self::Fn),
            "fn_mut" => Some(Self::FnMut),
            "fn_once" => Some(Self::FnOnce),
            "drop_in_place" => Some(Self::Drop),
            "exchange_malloc" => Some(Self::ExchangeMalloc),
            "panic" | "panic_impl" => Some(Self::Panic),
            "panic_fmt" => Some(Self::PanicFmt),
            "eh_personality" => Some(Self::EhPersonality),
            _ => None,
        }
    }
}

/// Registry of lang items discovered from `#[lang = "..."]` attributes.
/// Built during HIR lowering and consumed by type inference and MIR lowering.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct LangItemRegistry {
    trait_items: std::collections::HashMap<LangItem, TraitId>,
    fn_items: std::collections::HashMap<LangItem, FunctionId>,
    type_items: std::collections::HashMap<LangItem, TypeDefId>,
}

impl LangItemRegistry {
    /// Register a trait as a lang item.
    pub fn register_trait(&mut self, item: LangItem, id: TraitId) {
        self.trait_items.insert(item, id);
    }

    /// Register a function as a lang item.
    pub fn register_fn(&mut self, item: LangItem, id: FunctionId) {
        self.fn_items.insert(item, id);
    }

    /// Register a type as a lang item.
    pub fn register_type(&mut self, item: LangItem, id: TypeDefId) {
        self.type_items.insert(item, id);
    }

    /// Look up the trait for a lang item.
    pub fn get_trait(&self, item: LangItem) -> Option<TraitId> {
        self.trait_items.get(&item).copied()
    }

    /// Look up the function for a lang item.
    pub fn get_fn(&self, item: LangItem) -> Option<FunctionId> {
        self.fn_items.get(&item).copied()
    }

    /// Look up the type for a lang item.
    pub fn get_type(&self, item: LangItem) -> Option<TypeDefId> {
        self.type_items.get(&item).copied()
    }

    /// Look up a trait for a lang item, returning a detailed error if not found.
    ///
    /// Use this method when the lang item is required for compilation to proceed.
    pub fn require_trait(
        &self,
        item: LangItem,
        use_site: rv_span::FileSpan,
    ) -> Result<TraitId, LangItemError> {
        self.get_trait(item).ok_or_else(|| LangItemError::Missing {
            item,
            kind: LangItemKind::Trait,
            use_site,
            suggestion: item.suggestion(),
        })
    }

    /// Look up a function for a lang item, returning a detailed error if not found.
    ///
    /// Use this method when the lang item is required for compilation to proceed.
    pub fn require_fn(
        &self,
        item: LangItem,
        use_site: rv_span::FileSpan,
    ) -> Result<FunctionId, LangItemError> {
        self.get_fn(item).ok_or_else(|| LangItemError::Missing {
            item,
            kind: LangItemKind::Function,
            use_site,
            suggestion: item.suggestion(),
        })
    }

    /// Look up a type for a lang item, returning a detailed error if not found.
    ///
    /// Use this method when the lang item is required for compilation to proceed.
    pub fn require_type(
        &self,
        item: LangItem,
        use_site: rv_span::FileSpan,
    ) -> Result<TypeDefId, LangItemError> {
        self.get_type(item).ok_or_else(|| LangItemError::Missing {
            item,
            kind: LangItemKind::Type,
            use_site,
            suggestion: item.suggestion(),
        })
    }

    /// Check if all required lang items for a feature are present.
    ///
    /// Returns a list of missing lang items.
    #[must_use]
    pub fn check_required(&self, required: &[LangItem]) -> Vec<LangItem> {
        required
            .iter()
            .filter(|&&item| {
                self.get_trait(item).is_none()
                    && self.get_fn(item).is_none()
                    && self.get_type(item).is_none()
            })
            .copied()
            .collect()
    }
}

// === Lang Item Errors ===

/// Kind of lang item (for error messages)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LangItemKind {
    /// A trait lang item (e.g., `Add`, `Copy`)
    Trait,
    /// A function lang item (e.g., `panic_impl`)
    Function,
    /// A type lang item
    Type,
}

impl std::fmt::Display for LangItemKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LangItemKind::Trait => write!(f, "trait"),
            LangItemKind::Function => write!(f, "function"),
            LangItemKind::Type => write!(f, "type"),
        }
    }
}

/// Error when a required lang item is missing or misconfigured
#[derive(Debug, Clone)]
pub enum LangItemError {
    /// Required lang item is not defined
    Missing {
        /// The lang item that was requested
        item: LangItem,
        /// What kind of definition was expected
        kind: LangItemKind,
        /// Where the lang item was needed
        use_site: rv_span::FileSpan,
        /// Suggestion for how to fix this (e.g., "add core library")
        suggestion: &'static str,
    },
    /// Lang item is defined multiple times
    Duplicate {
        /// The lang item that was duplicated
        item: LangItem,
        /// First definition location
        first: rv_span::FileSpan,
        /// Second definition location
        second: rv_span::FileSpan,
    },
    /// Lang item has wrong definition kind (e.g., expected trait, found function)
    WrongKind {
        /// The lang item
        item: LangItem,
        /// What kind was expected
        expected: LangItemKind,
        /// What kind was found
        found: LangItemKind,
        /// Definition location
        def_site: rv_span::FileSpan,
    },
}

impl std::fmt::Display for LangItemError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LangItemError::Missing {
                item,
                kind,
                suggestion,
                ..
            } => {
                write!(
                    f,
                    "missing lang item `{}` ({} required). {}",
                    item.name(),
                    kind,
                    suggestion
                )
            }
            LangItemError::Duplicate { item, .. } => {
                write!(
                    f,
                    "lang item `{}` defined multiple times",
                    item.name()
                )
            }
            LangItemError::WrongKind {
                item,
                expected,
                found,
                ..
            } => {
                write!(
                    f,
                    "lang item `{}` has wrong kind: expected {}, found {}",
                    item.name(),
                    expected,
                    found
                )
            }
        }
    }
}

impl std::error::Error for LangItemError {}

impl LangItem {
    /// Get the string name of this lang item (for error messages)
    #[must_use]
    pub const fn name(&self) -> &'static str {
        match self {
            LangItem::Add => "add",
            LangItem::Sub => "sub",
            LangItem::Mul => "mul",
            LangItem::Div => "div",
            LangItem::Rem => "rem",
            LangItem::Neg => "neg",
            LangItem::Not => "not",
            LangItem::BitAnd => "bitand",
            LangItem::BitOr => "bitor",
            LangItem::BitXor => "bitxor",
            LangItem::Shl => "shl",
            LangItem::Shr => "shr",
            LangItem::PartialEq => "eq",
            LangItem::PartialOrd => "partial_ord",
            LangItem::Deref => "deref",
            LangItem::DerefMut => "deref_mut",
            LangItem::Index => "index",
            LangItem::IndexMut => "index_mut",
            LangItem::Sized => "sized",
            LangItem::Copy => "copy",
            LangItem::Send => "send",
            LangItem::Sync => "sync",
            LangItem::Unpin => "unpin",
            LangItem::Fn => "fn",
            LangItem::FnMut => "fn_mut",
            LangItem::FnOnce => "fn_once",
            LangItem::Drop => "drop_in_place",
            LangItem::ExchangeMalloc => "exchange_malloc",
            LangItem::Panic => "panic",
            LangItem::PanicFmt => "panic_fmt",
            LangItem::EhPersonality => "eh_personality",
        }
    }

    /// Get a suggestion for how to define this lang item
    #[must_use]
    pub const fn suggestion(&self) -> &'static str {
        match self {
            // Operator traits
            LangItem::Add
            | LangItem::Sub
            | LangItem::Mul
            | LangItem::Div
            | LangItem::Rem
            | LangItem::Neg
            | LangItem::Not
            | LangItem::BitAnd
            | LangItem::BitOr
            | LangItem::BitXor
            | LangItem::Shl
            | LangItem::Shr => {
                "Consider linking the core library or defining operator traits with #[lang = \"...\"]"
            }
            // Comparison traits
            LangItem::PartialEq | LangItem::PartialOrd => {
                "Consider linking the core library for comparison traits"
            }
            // Deref/Index traits
            LangItem::Deref | LangItem::DerefMut | LangItem::Index | LangItem::IndexMut => {
                "Consider linking the core library for indexing and dereference traits"
            }
            // Marker traits
            LangItem::Sized | LangItem::Copy | LangItem::Send | LangItem::Sync | LangItem::Unpin => {
                "Consider linking the core library for marker traits"
            }
            // Fn traits
            LangItem::Fn | LangItem::FnMut | LangItem::FnOnce => {
                "Consider linking the core library for function traits (closures require Fn/FnMut/FnOnce)"
            }
            // Memory management
            LangItem::Drop => {
                "Consider linking the core library for drop semantics"
            }
            LangItem::ExchangeMalloc => {
                "Consider linking the alloc library for heap allocation (Box requires exchange_malloc)"
            }
            // Panic handling
            LangItem::Panic | LangItem::PanicFmt => {
                "Define a panic handler with #[panic_handler] or link std/core"
            }
            LangItem::EhPersonality => {
                "Define an exception personality function or use panic=abort"
            }
        }
    }

    /// Check if this lang item is required for basic compilation
    #[must_use]
    pub const fn is_required(&self) -> bool {
        matches!(
            self,
            LangItem::Sized | LangItem::Copy | LangItem::Drop
        )
    }

    /// Get related lang items that are typically defined together
    #[must_use]
    pub fn related_items(&self) -> &'static [LangItem] {
        match self {
            // Arithmetic operators typically come together
            LangItem::Add | LangItem::Sub | LangItem::Mul | LangItem::Div | LangItem::Rem => {
                &[LangItem::Add, LangItem::Sub, LangItem::Mul, LangItem::Div, LangItem::Rem]
            }
            // Bitwise operators
            LangItem::BitAnd | LangItem::BitOr | LangItem::BitXor | LangItem::Shl | LangItem::Shr => {
                &[LangItem::BitAnd, LangItem::BitOr, LangItem::BitXor, LangItem::Shl, LangItem::Shr]
            }
            // Fn traits
            LangItem::Fn | LangItem::FnMut | LangItem::FnOnce => {
                &[LangItem::Fn, LangItem::FnMut, LangItem::FnOnce]
            }
            // Deref
            LangItem::Deref | LangItem::DerefMut => {
                &[LangItem::Deref, LangItem::DerefMut]
            }
            // Index
            LangItem::Index | LangItem::IndexMut => {
                &[LangItem::Index, LangItem::IndexMut]
            }
            _ => &[],
        }
    }
}

// === Object Safety ===

/// Error explaining why a trait is not object-safe
#[derive(Debug, Clone, PartialEq)]
pub enum ObjectSafetyError {
    /// Method has no receiver (no self parameter)
    MethodWithoutReceiver(Symbol),
    /// Method has generic type parameters
    GenericMethod(Symbol),
    /// Non-object-safe supertrait
    NonObjectSafeSupertrait(Symbol),
}

/// Check if a trait definition is object-safe (can be used as `dyn Trait`).
///
/// A trait is object-safe if:
/// - All methods have a receiver (`&self`, `&mut self`, or `self`)
/// - No methods have generic type parameters
/// - All supertraits are also object-safe
pub fn is_object_safe(trait_def: &TraitDef) -> Result<(), ObjectSafetyError> {
    for method in &trait_def.methods {
        // All methods must have a receiver
        if method.self_param.is_none() {
            return Err(ObjectSafetyError::MethodWithoutReceiver(method.name));
        }
        // No generic methods
        if !method.generics.is_empty() {
            return Err(ObjectSafetyError::GenericMethod(method.name));
        }
    }
    Ok(())
}

// === Vtable Layout ===

/// Layout of a vtable for a trait object
#[derive(Debug, Clone)]
pub struct VtableLayout {
    /// Trait this vtable is for
    pub trait_id: TraitId,
    /// Method entries in vtable order
    pub entries: Vec<VtableEntry>,
}

/// A single entry in a vtable
#[derive(Debug, Clone)]
pub struct VtableEntry {
    /// Method name
    pub name: Symbol,
    /// Index in the vtable
    pub index: usize,
}

/// Build a vtable layout from a trait definition.
/// Methods are ordered by declaration order in the trait.
pub fn build_vtable_layout(trait_def: &TraitDef) -> VtableLayout {
    let entries = trait_def
        .methods
        .iter()
        .enumerate()
        .filter(|(_, m)| m.self_param.is_some()) // Only methods with receivers go in vtable
        .map(|(index, m)| VtableEntry {
            name: m.name,
            index,
        })
        .collect();

    VtableLayout {
        trait_id: trait_def.id,
        entries,
    }
}
