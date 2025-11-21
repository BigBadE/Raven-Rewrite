//! Mid-level Intermediate Representation (MIR)
//!
//! MIR is a control-flow graph based representation used for optimization
//! and code generation. It's lower-level than HIR but still mostly independent
//! of the target architecture.

pub mod lower;

use indexmap::IndexMap;
use rv_hir::{BinaryOp as HirBinaryOp, FunctionId, LiteralKind, UnaryOp as HirUnaryOp};
use rv_intern::Symbol;
use rv_span::FileSpan;
use serde::{Deserialize, Serialize};

/// A MIR function representation
#[derive(Debug, Clone, PartialEq)]
pub struct MirFunction {
    /// The original HIR function ID
    pub id: FunctionId,
    /// Basic blocks
    pub basic_blocks: Vec<BasicBlock>,
    /// Local variables
    pub locals: Vec<Local>,
    /// Entry block ID
    pub entry_block: BasicBlockId,
    /// Number of parameters (first N locals are parameters)
    pub param_count: usize,
}

/// Local variable declaration
#[derive(Debug, Clone, PartialEq)]
pub struct Local {
    /// Local ID
    pub id: LocalId,
    /// Variable name (for debugging)
    pub name: Option<Symbol>,
    /// Type information (simplified)
    pub ty: MirType,
    /// Is this a mutable binding
    pub mutable: bool,
}

/// Simplified type information for MIR
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum MirType {
    /// Integer type
    Int,
    /// Float type
    Float,
    /// Boolean type
    Bool,
    /// Unit type
    Unit,
    /// String type
    String,
    /// Named type (for user-defined types without field info)
    Named(Symbol),
    /// Struct type with field information
    Struct {
        /// Struct name
        name: Symbol,
        /// Field types
        fields: Vec<MirType>,
    },
    /// Enum type with variant information
    Enum {
        /// Enum name
        name: Symbol,
        /// Variant types
        variants: Vec<MirVariant>,
    },
    /// Array type
    Array {
        /// Element type
        element: Box<MirType>,
        /// Size
        size: usize,
    },
    /// Slice type
    Slice {
        /// Element type
        element: Box<MirType>,
    },
    /// Tuple type
    Tuple(Vec<MirType>),
    /// Reference type
    Ref {
        /// Is mutable
        mutable: bool,
        /// Inner type
        inner: Box<MirType>,
    },
    /// Function type
    Function {
        /// Parameter types
        params: Vec<MirType>,
        /// Return type
        ret: Box<MirType>,
    },
}

/// MIR representation of enum variant
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MirVariant {
    /// Variant name
    pub name: Symbol,
    /// Variant payload types
    pub fields: Vec<MirType>,
}

/// Basic block ID
pub type BasicBlockId = usize;

/// Local variable ID
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct LocalId(pub u32);

/// Place where a value can be stored
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Place {
    /// Base local variable
    pub local: LocalId,
    /// Projection (field access, array indexing, etc.)
    pub projection: Vec<PlaceElem>,
}

impl Place {
    /// Creates a simple place from a local
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
    /// Dereference (*place)
    Deref,
    /// Field access (place.field) - uses field index, not name
    Field { field_idx: usize },
    /// Array/slice indexing (place[index])
    Index(LocalId),
}

/// Alias for backwards compatibility
pub type Projection = PlaceElem;

/// Basic block in control flow graph
#[derive(Debug, Clone, PartialEq)]
pub struct BasicBlock {
    /// Block ID
    pub id: BasicBlockId,
    /// Statements in this block
    pub statements: Vec<Statement>,
    /// Block terminator (how control flow exits this block)
    pub terminator: Terminator,
}

/// MIR statement
#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    /// Assign an rvalue to a place
    Assign {
        /// Destination
        place: Place,
        /// Value being assigned
        rvalue: RValue,
        /// Source location
        span: FileSpan,
    },
    /// Mark storage as live
    StorageLive(LocalId),
    /// Mark storage as dead
    StorageDead(LocalId),
    /// No-op (used for debugging/optimization markers)
    Nop,
}

/// Right-hand side value
#[derive(Debug, Clone, PartialEq)]
pub enum RValue {
    /// Use a value (copy or move)
    Use(Operand),
    /// Binary operation
    BinaryOp {
        /// Operator
        op: BinaryOp,
        /// Left operand
        left: Operand,
        /// Right operand
        right: Operand,
    },
    /// Unary operation
    UnaryOp {
        /// Operator
        op: UnaryOp,
        /// Operand
        operand: Operand,
    },
    /// Function call
    Call {
        /// Function being called
        func: FunctionId,
        /// Arguments
        args: Vec<Operand>,
    },
    /// Create a reference
    Ref {
        /// Is mutable
        mutable: bool,
        /// Place being referenced
        place: Place,
    },
    /// Aggregate construction (tuple, struct, array)
    Aggregate {
        /// Kind of aggregate
        kind: AggregateKind,
        /// Fields/elements
        operands: Vec<Operand>,
    },
}

/// Aggregate kind
#[derive(Debug, Clone, PartialEq)]
pub enum AggregateKind {
    /// Tuple
    Tuple,
    /// Struct
    Struct,
    /// Enum variant
    Enum {
        /// Variant index
        variant_idx: usize,
    },
    /// Array
    Array(MirType),
}

/// Operand (value being used)
#[derive(Debug, Clone, PartialEq)]
pub enum Operand {
    /// Copy a place's value
    Copy(Place),
    /// Move a place's value
    Move(Place),
    /// Constant value
    Constant(Constant),
}

/// Constant value
#[derive(Debug, Clone, PartialEq)]
pub struct Constant {
    /// Literal value
    pub kind: LiteralKind,
    /// Type
    pub ty: MirType,
}

/// Block terminator (control flow)
#[derive(Debug, Clone, PartialEq)]
pub enum Terminator {
    /// Unconditional jump to another block
    Goto(BasicBlockId),
    /// Conditional branch based on integer discriminant
    SwitchInt {
        /// Value being switched on
        discriminant: Operand,
        /// Map from values to target blocks
        targets: IndexMap<u128, BasicBlockId>,
        /// Default/otherwise target
        otherwise: BasicBlockId,
    },
    /// Return from function
    Return {
        /// Return value
        value: Option<Operand>,
    },
    /// Call a function and potentially unwind
    Call {
        /// Function being called
        func: FunctionId,
        /// Arguments
        args: Vec<Operand>,
        /// Destination for return value
        destination: Place,
        /// Target block after successful call
        target: BasicBlockId,
    },
    /// Code that will never be reached
    Unreachable,
}

/// Binary operators (MIR version)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinaryOp {
    /// Addition
    Add,
    /// Subtraction
    Sub,
    /// Multiplication
    Mul,
    /// Division
    Div,
    /// Modulo
    Mod,
    /// Equality
    Eq,
    /// Inequality
    Ne,
    /// Less than
    Lt,
    /// Less than or equal
    Le,
    /// Greater than
    Gt,
    /// Greater than or equal
    Ge,
    /// Bitwise AND
    BitAnd,
    /// Bitwise OR
    BitOr,
    /// Bitwise XOR
    BitXor,
    /// Left shift
    Shl,
    /// Right shift
    Shr,
}

impl From<HirBinaryOp> for BinaryOp {
    fn from(op: HirBinaryOp) -> Self {
        match op {
            HirBinaryOp::Add => Self::Add,
            HirBinaryOp::Sub => Self::Sub,
            HirBinaryOp::Mul => Self::Mul,
            HirBinaryOp::Div => Self::Div,
            HirBinaryOp::Mod => Self::Mod,
            HirBinaryOp::Eq => Self::Eq,
            HirBinaryOp::Ne => Self::Ne,
            HirBinaryOp::Lt => Self::Lt,
            HirBinaryOp::Le => Self::Le,
            HirBinaryOp::Gt => Self::Gt,
            HirBinaryOp::Ge => Self::Ge,
            HirBinaryOp::And | HirBinaryOp::BitAnd => Self::BitAnd,
            HirBinaryOp::Or | HirBinaryOp::BitOr => Self::BitOr,
            HirBinaryOp::BitXor => Self::BitXor,
            HirBinaryOp::Shl => Self::Shl,
            HirBinaryOp::Shr => Self::Shr,
        }
    }
}

/// Unary operators (MIR version)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnaryOp {
    /// Negation
    Neg,
    /// Logical NOT
    Not,
}

impl From<HirUnaryOp> for UnaryOp {
    fn from(op: HirUnaryOp) -> Self {
        match op {
            HirUnaryOp::Neg => Self::Neg,
            HirUnaryOp::Not | HirUnaryOp::BitNot => Self::Not,
            HirUnaryOp::Deref => Self::Not, // Deref is handled via Place
            HirUnaryOp::Ref | HirUnaryOp::RefMut => Self::Not, // Ref is RValue::Ref
        }
    }
}

/// Builder for constructing MIR functions
pub struct MirBuilder {
    function: MirFunction,
    current_block: Option<BasicBlockId>,
    next_local: u32,
}

impl MirBuilder {
    /// Creates a new MIR builder
    #[must_use]
    pub fn new(func_id: FunctionId) -> Self {
        let entry_block = BasicBlock {
            id: 0,
            statements: Vec::new(),
            terminator: Terminator::Return { value: None },
        };

        Self {
            function: MirFunction {
                id: func_id,
                basic_blocks: vec![entry_block],
                locals: Vec::new(),
                entry_block: 0,
                param_count: 0,
            },
            current_block: Some(0),
            next_local: 0,
        }
    }

    /// Sets the number of parameters for this function
    pub fn set_param_count(&mut self, count: usize) {
        self.function.param_count = count;
    }

    /// Creates a new basic block and returns its ID
    pub fn new_block(&mut self) -> BasicBlockId {
        let id = self.function.basic_blocks.len();
        self.function.basic_blocks.push(BasicBlock {
            id,
            statements: Vec::new(),
            terminator: Terminator::Unreachable,
        });
        id
    }

    /// Sets the current block for adding statements
    pub fn set_current_block(&mut self, block_id: BasicBlockId) {
        self.current_block = Some(block_id);
    }

    /// Allocates a new local variable
    pub fn new_local(&mut self, name: Option<Symbol>, ty: MirType, mutable: bool) -> LocalId {
        let id = LocalId(self.next_local);
        self.next_local += 1;
        self.function.locals.push(Local {
            id,
            name,
            ty,
            mutable,
        });
        id
    }

    /// Adds a statement to the current block
    pub fn add_statement(&mut self, stmt: Statement) {
        if let Some(block_id) = self.current_block {
            self.function.basic_blocks[block_id].statements.push(stmt);
        }
    }

    /// Sets the terminator for the current block
    pub fn set_terminator(&mut self, terminator: Terminator) {
        if let Some(block_id) = self.current_block {
            self.function.basic_blocks[block_id].terminator = terminator;
        }
    }

    /// Finishes building and returns the MIR function
    #[must_use]
    pub fn finish(self) -> MirFunction {
        self.function
    }
}
