//! Low-level Intermediate Representation (LIR)
//!
//! LIR is a fully monomorphized, LLVM-ready representation.
//! Unlike MIR, LIR guarantees:
//! - No generic functions (all monomorphized)
//! - No generic types (all concrete)
//! - Simplified representation closer to LLVM IR
//!
//! The type system enforces that LLVM backend never receives generic code.

#![allow(
    missing_docs,
    reason = "LIR types mirror MIR types with identical semantics — struct field docs would be redundant"
)]

pub mod lower;

use indexmap::IndexMap;
use rv_hir::{FunctionId, LiteralKind};
use rv_intern::Symbol;
pub use rv_mir::{BinaryOp, UnaryOp};
use rv_span::FileSpan;
use serde::{Deserialize, Serialize};

/// A fully monomorphized LIR function
///
/// Type system guarantee: This struct cannot represent generic functions.
/// All type parameters have been resolved to concrete types.
#[derive(Debug, Clone, PartialEq)]
pub struct LirFunction {
    /// The function ID (may be original or monomorphized instance)
    pub id: FunctionId,
    /// Basic blocks
    pub basic_blocks: Vec<BasicBlock>,
    /// Local variables (all with concrete types)
    pub locals: Vec<Local>,
    /// Entry block ID
    pub entry_block: BasicBlockId,
    /// Number of parameters (first N locals are parameters)
    pub param_count: usize,
    /// Return type of the function (guaranteed concrete)
    pub return_type: LirType,
}

impl LirFunction {
    /// Get the LIR type of a local variable by its ID.
    #[must_use]
    pub fn get_local_type(&self, local: LocalId) -> Option<LirType> {
        self.locals
            .iter()
            .find(|l| l.id == local)
            .map(|l| l.ty.clone())
    }
}

/// Local variable with concrete type
#[derive(Debug, Clone, PartialEq)]
pub struct Local {
    pub id: LocalId,
    pub name: Option<Symbol>,
    /// Guaranteed concrete type (no type variables)
    pub ty: LirType,
    pub mutable: bool,
    /// Source span for error reporting
    pub span: rv_span::FileSpan,
}

/// Concrete type information for LIR
///
/// Type system guarantee: No generic types.
/// All variants represent concrete, monomorphized types.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum LirType {
    Int(rv_hir::IntWidth, rv_hir::Signedness),
    Float(rv_hir::FloatWidth),
    Char,
    Bool,
    Unit,
    String,
    /// Struct type with concrete field types
    Struct {
        name: Symbol,
        fields: Vec<LirType>,
    },
    /// Enum type with concrete variant types
    Enum {
        name: Symbol,
        variants: Vec<LirVariant>,
    },
    /// Array with concrete element type
    Array {
        element: Box<LirType>,
        size: usize,
    },
    /// Slice with concrete element type
    Slice {
        element: Box<LirType>,
    },
    /// Tuple with concrete element types
    Tuple(Vec<LirType>),
    /// Reference with concrete inner type
    Ref {
        mutable: bool,
        inner: Box<LirType>,
        lifetime: Option<rv_span::LifetimeId>,
    },
    /// Function pointer with concrete signature
    Function {
        params: Vec<LirType>,
        ret: Box<LirType>,
    },
    /// Raw pointer type (*const T or *mut T)
    Pointer {
        mutable: bool,
        inner: Box<LirType>,
    },
    /// Never type (!)
    Never,
    /// Dynamic trait object (dyn Trait)
    DynTrait {
        principal: Symbol,
    },
    /// Impl trait (opaque type)
    ImplTrait {
        principal: Symbol,
    },
    /// Function pointer type: fn(T, U) -> V
    FunctionPointer {
        params: Vec<LirType>,
        ret: Box<LirType>,
        abi: Option<String>,
    },
    /// Box<T> - heap-allocated smart pointer
    Box {
        inner: Box<LirType>,
    },
}

impl LirType {
    /// Returns true if this type is unsized (slices, dyn Trait).
    #[must_use]
    pub fn is_unsized(&self) -> bool {
        matches!(self, LirType::Slice { .. } | LirType::DynTrait { .. })
    }

    /// Returns true if a reference to this type is a fat pointer (16 bytes).
    #[must_use]
    pub fn ref_is_fat_ptr(&self) -> bool {
        self.is_unsized()
    }

    /// Check if this type needs to be dropped.
    ///
    /// A type needs drop if:
    /// - It's a Box (heap deallocation)
    /// - It's a struct/enum/tuple/array containing fields that need drop
    /// - It's a dyn Trait (drop called through vtable)
    ///
    /// A type does NOT need drop if:
    /// - It's a primitive (int, float, char, bool, unit)
    /// - It's a reference/pointer (doesn't own the data)
    /// - It's a function pointer
    #[must_use]
    pub fn needs_drop(&self) -> bool {
        match self {
            // Primitives never need drop
            LirType::Int(..)
            | LirType::Float(..)
            | LirType::Char
            | LirType::Bool
            | LirType::Unit
            | LirType::String
            | LirType::Never => false,

            // References and pointers don't own their data
            LirType::Ref { .. } | LirType::Pointer { .. } => false,

            // Function pointers and function types are just addresses
            LirType::Function { .. } | LirType::FunctionPointer { .. } => false,

            // Box types need drop (heap deallocation)
            LirType::Box { .. } => true,

            // dyn Trait calls drop through vtable
            LirType::DynTrait { .. } => true,

            // impl Trait might need drop (conservatively assume yes)
            LirType::ImplTrait { .. } => true,

            // Structs: check fields recursively
            LirType::Struct { fields, .. } => fields.iter().any(LirType::needs_drop),

            // Enums: check if any variant has fields that need drop
            LirType::Enum { variants, .. } => {
                variants.iter().any(|v| v.fields.iter().any(LirType::needs_drop))
            }

            // Tuples: check elements
            LirType::Tuple(elements) => elements.iter().any(LirType::needs_drop),

            // Arrays: check element type
            LirType::Array { element, .. } => element.needs_drop(),

            // Slices: we don't own the data
            LirType::Slice { .. } => false,
        }
    }
}

/// Enum variant with concrete types
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LirVariant {
    pub name: Symbol,
    pub fields: Vec<LirType>,
}

/// Basic block ID
pub type BasicBlockId = usize;

/// Local variable ID
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct LocalId(pub u32);

/// Place where a value can be stored
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Place {
    pub local: LocalId,
    pub projection: Vec<PlaceElem>,
}

impl Place {
    #[must_use]
    pub fn from_local(local: LocalId) -> Self {
        Self {
            local,
            projection: Vec::new(),
        }
    }
}

/// Place projection element
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PlaceElem {
    Deref,
    Field { field_idx: usize },
    Index(LocalId),
}

/// A basic block in the CFG
#[derive(Debug, Clone, PartialEq)]
pub struct BasicBlock {
    pub id: BasicBlockId,
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

/// Statements (non-control flow)
#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    /// Assign an rvalue to a place
    Assign {
        place: Place,
        rvalue: RValue,
        /// Source span for error reporting
        span: FileSpan,
    },
    /// No-op (used for storage liveness markers converted from MIR)
    Nop,
}

/// Terminator (control flow)
#[derive(Debug, Clone, PartialEq)]
pub enum Terminator {
    /// Return from function
    Return { value: Option<Operand> },
    /// Unconditional jump
    Goto { target: BasicBlockId },
    /// Switch on integer value
    SwitchInt {
        discriminant: Operand,
        targets: IndexMap<i64, BasicBlockId>,
        otherwise: BasicBlockId,
    },
    /// Function call
    Call {
        func: FunctionId,
        args: Vec<Operand>,
        destination: Place,
        target: Option<BasicBlockId>,
    },
    /// Drop the value at a place, then continue to target block
    Drop { place: Place, target: BasicBlockId },
    /// Unreachable code
    Unreachable,
    /// Assert a condition, panic if false
    Assert {
        /// Condition that must be true
        cond: Operand,
        /// Whether to panic when cond is true (false) or false (true)
        expected: bool,
        /// Message to display on failure
        msg: LirAssertMessage,
        /// Block to continue to if assertion passes
        target: BasicBlockId,
    },
}

/// Message to display when an LIR assertion fails
#[derive(Debug, Clone, PartialEq)]
pub enum LirAssertMessage {
    /// Index out of bounds: (index_value, length)
    BoundsCheck {
        /// The index that was out of bounds
        index: Operand,
        /// The length of the array/slice
        len: Operand,
    },
    /// Overflow in arithmetic operation
    Overflow(BinaryOp),
    /// Division by zero
    DivisionByZero,
    /// Remainder by zero
    RemainderByZero,
    /// Explicit panic message
    Panic(String),
}

/// R-values (things that can be assigned)
#[derive(Debug, Clone, PartialEq)]
pub enum RValue {
    /// Use an operand
    Use(Operand),
    /// Binary operation
    BinaryOp {
        op: BinaryOp,
        left: Operand,
        right: Operand,
    },
    /// Unary operation
    UnaryOp { op: UnaryOp, operand: Operand },
    /// Function call
    Call {
        func: FunctionId,
        args: Vec<Operand>,
    },
    /// Reference (address-of)
    Ref { mutable: bool, place: Place },
    /// Create aggregate (struct, tuple, array)
    Aggregate {
        kind: AggregateKind,
        operands: Vec<Operand>,
    },
    /// Extract the discriminant of an enum value as an integer
    Discriminant(Place),
    /// Type cast (as)
    Cast {
        /// Value to cast
        operand: Operand,
        /// Source type
        from: LirType,
        /// Target type
        to: LirType,
    },
    /// Dynamic dispatch via vtable
    VtableCall {
        receiver: Operand,
        vtable_index: usize,
        args: Vec<Operand>,
        trait_id: rv_hir::TraitId,
        method_name: Symbol,
    },
    /// Box allocation (heap allocate)
    BoxNew {
        operand: Operand,
        inner_ty: LirType,
    },
    /// Box deallocation (free heap memory)
    BoxFree {
        place: Place,
    },
    /// Compiler intrinsic call
    Intrinsic {
        intrinsic: rv_mir::Intrinsic,
        args: Vec<Operand>,
        type_args: Vec<LirType>,
    },
}

/// Aggregate construction
#[derive(Debug, Clone, PartialEq)]
pub enum AggregateKind {
    Tuple,
    Struct {
        /// Struct name
        name: Symbol,
    },
    Enum {
        /// Enum name
        name: Symbol,
        /// Variant index within the enum definition
        variant_idx: usize,
    },
    Array(LirType),
}

/// Operands (leaf values)
#[derive(Debug, Clone, PartialEq)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}

/// Constant value
#[derive(Debug, Clone, PartialEq)]
pub struct Constant {
    pub kind: LiteralKind,
    pub ty: LirType,
    pub span: FileSpan,
}

/// External function declaration with fully resolved LIR types.
///
/// This is the LIR equivalent of `rv_hir::ExternalFunction`, with all
/// HIR `TypeId` references resolved to concrete `LirType` values.
#[derive(Debug, Clone, PartialEq)]
pub struct LirExternalFunction {
    /// Unique ID
    pub id: FunctionId,
    /// Function name (unmangled)
    pub name: Symbol,
    /// Mangled name (for linking)
    pub mangled_name: Option<String>,
    /// Parameter types (resolved to LIR)
    pub param_types: Vec<LirType>,
    /// Return type (resolved to LIR), None = void
    pub return_type: Option<LirType>,
    /// ABI (e.g., "C", "Rust")
    pub abi: Option<String>,
}
