//! High-level Intermediate Representation (HIR)
//!
//! The HIR is a desugared, name-resolved representation of source code.
//! It's the first step after parsing and before type checking.

pub mod exhaustiveness;

use rv_arena::{Arena, Idx};
use rv_intern::Symbol;
use rv_span::{FileId, FileSpan, Span};
use serde::{Deserialize, Serialize};

/// HIR node IDs
pub type ExprId = Idx<Expr>;
pub type StmtId = Idx<Stmt>;
pub type TypeId = Idx<Type>;
pub type PatternId = Idx<Pattern>;

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
    /// Variable/local binding
    Local(LocalId),
    /// Module definition
    Module(ModuleId),
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

/// Item in a module (function, type, trait, impl, module, use)
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

/// Struct definition
#[derive(Debug, Clone, PartialEq)]
pub struct StructDef {
    /// Unique ID
    pub id: TypeDefId,
    /// Struct name
    pub name: Symbol,
    /// Generic parameters
    pub generic_params: Vec<Symbol>,
    /// Fields
    pub fields: Vec<FieldDef>,
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
    /// Generic parameters
    pub generic_params: Vec<Symbol>,
    /// Variants
    pub variants: Vec<VariantDef>,
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
    /// Source location
    pub span: FileSpan,
    /// Generic parameters
    pub generics: Vec<GenericParam>,
    /// Function parameters
    pub parameters: Vec<Parameter>,
    /// Return type
    pub return_type: Option<TypeId>,
    /// Function body
    pub body: Body,
    /// Whether this is an external function
    pub is_external: bool,
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
    /// Parameter type
    pub ty: TypeId,
    /// Source location
    pub span: FileSpan,
}

/// Generic parameter
#[derive(Debug, Clone, PartialEq)]
pub struct GenericParam {
    /// Parameter name
    pub name: Symbol,
    /// Trait bounds
    pub bounds: Vec<TraitBound>,
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
}

/// Trait definition
#[derive(Debug, Clone, PartialEq)]
pub struct TraitDef {
    /// Unique ID
    pub id: TraitId,
    /// Trait name
    pub name: Symbol,
    /// Generic parameters
    pub generic_params: Vec<Symbol>,
    /// Required methods (signatures only, no bodies)
    pub methods: Vec<TraitMethod>,
    /// Associated types with optional bounds
    pub associated_types: Vec<AssociatedType>,
    /// Supertraits (traits this trait extends)
    pub supertraits: Vec<TraitBound>,
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
    pub generic_params: Vec<Symbol>,
    /// Methods in this impl block
    pub methods: Vec<FunctionId>,
    /// Associated type implementations (type Foo = Bar;)
    pub associated_type_impls: Vec<AssociatedTypeImpl>,
    /// Where clauses for trait bounds
    pub where_clauses: Vec<WhereClause>,
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
        // Allocate a placeholder expression for the root
        let root_expr = exprs.alloc(Expr::Literal {
            kind: LiteralKind::Unit,
            span: FileSpan::new(FileId(0), Span::new(0, 0)),
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
        /// Source location
        span: FileSpan,
    },
    /// Unknown/error type
    Unknown {
        /// Source location
        span: FileSpan,
    },
}

/// Literal kinds
#[derive(Debug, Clone, PartialEq)]
pub enum LiteralKind {
    /// Integer literal
    Integer(i64),
    /// Float literal
    Float(f64),
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
