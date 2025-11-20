//! Low-level Intermediate Representation (LIR)
//!
//! LIR is a fully monomorphized, LLVM-ready representation.
//! Unlike MIR, LIR guarantees:
//! - No generic functions (all monomorphized)
//! - No generic types (all concrete)
//! - Simplified representation closer to LLVM IR
//!
//! The type system enforces that LLVM backend never receives generic code.

#![allow(missing_docs, reason = "LIR is in active development, documentation will be added")]

pub mod lower;

use indexmap::IndexMap;
use rv_hir::{FunctionId, LiteralKind};
pub use rv_mir::{BinaryOp, UnaryOp};
use rv_intern::Symbol;
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
}

/// Local variable with concrete type
#[derive(Debug, Clone, PartialEq)]
pub struct Local {
    pub id: LocalId,
    pub name: Option<Symbol>,
    /// Guaranteed concrete type (no type variables)
    pub ty: LirType,
    pub mutable: bool,
}

/// Concrete type information for LIR
///
/// Type system guarantee: No generic types.
/// All variants represent concrete, monomorphized types.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum LirType {
    Int,
    Float,
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
    },
    /// Function pointer with concrete signature
    Function {
        params: Vec<LirType>,
        ret: Box<LirType>,
    },
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
    },
    /// No-op placeholder
    Nop,
}

/// Terminator (control flow)
#[derive(Debug, Clone, PartialEq)]
pub enum Terminator {
    /// Return from function
    Return {
        value: Option<Operand>,
    },
    /// Unconditional jump
    Goto {
        target: BasicBlockId,
    },
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
    /// Unreachable code
    Unreachable,
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
    UnaryOp {
        op: UnaryOp,
        operand: Operand,
    },
    /// Function call
    Call {
        func: FunctionId,
        args: Vec<Operand>,
    },
    /// Reference (address-of)
    Ref {
        mutable: bool,
        place: Place,
    },
    /// Create aggregate (struct, tuple, array)
    Aggregate {
        kind: AggregateKind,
        operands: Vec<Operand>,
    },
}

/// Aggregate construction
#[derive(Debug, Clone, PartialEq)]
pub enum AggregateKind {
    Tuple,
    Struct,
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
