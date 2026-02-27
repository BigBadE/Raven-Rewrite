//! Mid-level Intermediate Representation (MIR)
//!
//! MIR is a control-flow graph based representation used for optimization
//! and code generation. It's lower-level than HIR but still mostly independent
//! of the target architecture.
//!
//! This crate contains only MIR data structures. For HIR → MIR lowering,
//! see the rv-mir-lower crate.

use indexmap::IndexMap;
use rv_hir::{BinaryOp as HirBinaryOp, FunctionId, LiteralKind, UnaryOp as HirUnaryOp};
use rv_intern::Symbol;
use rv_span::FileSpan;
use serde::{Deserialize, Serialize};

/// Compiler intrinsic identifier.
///
/// This is a simplified version that stores the intrinsic name as a Symbol.
/// The full intrinsic implementation is in rv-intrinsics (currently inaccessible
/// due to permission issues).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Intrinsic {
    /// The name of the intrinsic (e.g., "size_of", "transmute")
    pub name: Symbol,
}

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
    /// Return type of the function
    pub return_type: MirType,
}

impl MirFunction {
    /// Get the MIR type of a local variable by its ID.
    #[must_use]
    pub fn get_local_type(&self, local: LocalId) -> Option<MirType> {
        self.locals
            .iter()
            .find(|l| l.id == local)
            .map(|l| l.ty.clone())
    }
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
    /// Source span for error reporting (e.g., borrow checker diagnostics)
    pub span: FileSpan,
}

/// Simplified type information for MIR
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum MirType {
    /// Integer type with width and signedness
    Int(rv_hir::IntWidth, rv_hir::Signedness),
    /// Float type with width
    Float(rv_hir::FloatWidth),
    /// Character type
    Char,
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
        /// Lifetime (None = inferred)
        lifetime: Option<rv_span::LifetimeId>,
    },
    /// Function type (for closures and trait objects)
    Function {
        /// Parameter types
        params: Vec<MirType>,
        /// Return type
        ret: Box<MirType>,
    },
    /// Function pointer type: fn(T, U) -> V
    FunctionPointer {
        /// Parameter types
        params: Vec<MirType>,
        /// Return type
        ret: Box<MirType>,
        /// ABI (None = Rust, Some("C") = extern "C", etc.)
        abi: Option<String>,
    },
    /// Raw pointer type (*const T or *mut T)
    Pointer {
        /// Is mutable (*mut vs *const)
        mutable: bool,
        /// Pointed-to type
        inner: Box<MirType>,
    },
    /// Never type (!)
    Never,
    /// Box<T> - heap-allocated smart pointer
    Box {
        /// Inner type
        inner: Box<MirType>,
    },
    /// Dynamic trait object (dyn Trait)
    DynTrait {
        /// Principal trait name
        principal: Symbol,
        /// Resolved trait ID (for vtable lookup)
        trait_id: Option<rv_hir::TraitId>,
    },
    /// Impl trait (opaque type)
    ImplTrait {
        /// Principal trait name
        principal: Symbol,
    },
}

impl MirType {
    /// Returns true if a reference/pointer to this type requires a fat pointer
    /// (pointer + metadata). Fat pointer targets are unsized types: slices,
    /// string slices, dynamic trait objects, and structs with unsized last fields.
    #[must_use]
    pub fn is_unsized(&self) -> bool {
        match self {
            MirType::Slice { .. } | MirType::DynTrait { .. } => true,
            MirType::Struct { fields, .. } => {
                // Struct is unsized if its last field is unsized
                fields.last().map_or(false, |f| f.is_unsized())
            }
            _ => false,
        }
    }

    /// Returns true if a reference to this type is a fat pointer (16 bytes).
    /// Thin pointers are 8 bytes, fat pointers are 16 bytes (pointer + metadata).
    #[must_use]
    pub fn ref_is_fat_ptr(&self) -> bool {
        self.is_unsized()
    }

    /// Returns true if this Box contains an unsized type.
    /// Box<dyn Trait> requires special handling for vtable pointers.
    #[must_use]
    pub fn is_box_of_unsized(&self) -> bool {
        match self {
            MirType::Box { inner } => inner.is_unsized(),
            _ => false,
        }
    }
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
    /// Extract the discriminant of an enum value as an integer
    Discriminant(Place),
    /// Type cast (as)
    Cast {
        /// Value to cast
        operand: Operand,
        /// Source type
        from: MirType,
        /// Target type
        to: MirType,
    },
    /// Virtual method call through trait object vtable
    VtableCall {
        /// Receiver (the dyn Trait reference)
        receiver: Operand,
        /// Index into the vtable
        vtable_index: usize,
        /// Arguments (excluding receiver)
        args: Vec<Operand>,
        /// Trait ID for looking up concrete impl
        trait_id: rv_hir::TraitId,
        /// Method name (for interpreter dispatch)
        method_name: Symbol,
    },
    /// Box allocation (heap allocation via exchange_malloc)
    BoxNew {
        /// Value to place in the box
        operand: Operand,
        /// Type of the boxed value
        inner_ty: MirType,
    },
    /// Box deallocation (implicit when Box goes out of scope)
    /// This is lowered from Drop terminator for Box types
    BoxFree {
        /// The box to deallocate
        place: Place,
    },
    /// Compiler intrinsic call
    Intrinsic {
        /// The intrinsic being called
        intrinsic: Intrinsic,
        /// Arguments to the intrinsic
        args: Vec<Operand>,
        /// Type arguments (for generic intrinsics like size_of<T>)
        type_args: Vec<MirType>,
    },
}

/// Aggregate kind
#[derive(Debug, Clone, PartialEq)]
pub enum AggregateKind {
    /// Tuple
    Tuple,
    /// Struct with its name
    Struct {
        /// Struct name
        name: Symbol,
    },
    /// Enum variant
    Enum {
        /// Enum name
        name: Symbol,
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
        /// Source location
        span: rv_span::FileSpan,
    },
    /// Return from function
    Return {
        /// Return value
        value: Option<Operand>,
        /// Source location
        span: rv_span::FileSpan,
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
        /// Source location
        span: rv_span::FileSpan,
    },
    /// Drop the value at a place, then continue to target block
    Drop {
        /// Place whose value should be dropped
        place: Place,
        /// Optional drop flag to check before dropping (for conditional drops)
        /// If Some(flag_place), only drop if the flag is true
        drop_flag: Option<Place>,
        /// Block to jump to after drop completes
        target: BasicBlockId,
        /// Source location
        span: rv_span::FileSpan,
    },
    /// Code that will never be reached
    Unreachable,
    /// Assert a condition, panic if false
    /// Used for bounds checks, overflow checks, etc.
    Assert {
        /// Condition that must be true
        cond: Operand,
        /// Whether to panic when cond is true (for `assert!(!cond)`) or false (normal assert)
        expected: bool,
        /// Message to display on failure
        msg: AssertMessage,
        /// Block to continue to if assertion passes
        target: BasicBlockId,
        /// Source location
        span: rv_span::FileSpan,
    },
}

/// Message to display when an assertion fails
#[derive(Debug, Clone, PartialEq)]
pub enum AssertMessage {
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
    /// Logical AND (&&) - short-circuit semantics
    And,
    /// Logical OR (||) - short-circuit semantics
    Or,
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
            HirBinaryOp::And => Self::And,
            HirBinaryOp::Or => Self::Or,
            HirBinaryOp::BitAnd => Self::BitAnd,
            HirBinaryOp::BitOr => Self::BitOr,
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
            HirUnaryOp::Deref | HirUnaryOp::Ref | HirUnaryOp::RefMut => {
                panic!(
                    "ICE: Deref/Ref/RefMut are handled via Place projections and RValue::Ref, not UnaryOp"
                )
            }
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
            terminator: Terminator::Return {
                value: None,
                span: rv_span::FileSpan::new(rv_span::FileId(0), rv_span::Span::new(0, 0)),
            },
        };

        Self {
            function: MirFunction {
                id: func_id,
                basic_blocks: vec![entry_block],
                locals: Vec::new(),
                entry_block: 0,
                param_count: 0,
                return_type: MirType::Unit,
            },
            current_block: Some(0),
            next_local: 0,
        }
    }

    /// Sets the number of parameters for this function
    pub fn set_param_count(&mut self, count: usize) {
        self.function.param_count = count;
    }

    /// Sets the return type for this function
    pub fn set_return_type(&mut self, ty: MirType) {
        self.function.return_type = ty;
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
    pub fn new_local(
        &mut self,
        name: Option<Symbol>,
        ty: MirType,
        mutable: bool,
        span: FileSpan,
    ) -> LocalId {
        let id = LocalId(self.next_local);
        self.next_local += 1;
        self.function.locals.push(Local {
            id,
            name,
            ty,
            mutable,
            span,
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

    /// Get a reference to the locals (for reading during lowering)
    #[must_use]
    pub fn locals(&self) -> &[Local] {
        &self.function.locals
    }

    /// Get the MIR type of a local variable by its ID.
    #[must_use]
    pub fn get_local_type(&self, local: LocalId) -> Option<MirType> {
        self.function
            .locals
            .iter()
            .find(|l| l.id == local)
            .map(|l| l.ty.clone())
    }
}
