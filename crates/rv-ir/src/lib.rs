//! Phase-indexed IR ("Trees That Grow"): a field that is "not yet inferred" does
//! not exist in early phases, so you cannot lower an un-elaborated program.
//!
//! The IR core is *behavior-only*: no `mut`, no lifetimes, no memory strategy as a
//! field. Those are inferred facts living in side-tables, or filled in by phase.
use rv_core::Ty as CoreTy;
use rv_core::{BinOp, Prop, Sym, UnOp};

pub use rv_arena::NodeId;
pub use rv_core::{BinOp as IrBinOp, UnOp as IrUnOp};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct LocalId(pub u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BlockId(pub u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct DisciplineId(pub u32);

/// A compilation phase chooses the representation of each "grows over time" field.
/// `()` = "not yet inferred / absent in this phase"; a real id/type = "resolved".
pub trait Phase {
    type Ty: Clone + std::fmt::Debug;
    type Strategy: Clone + std::fmt::Debug;
}

#[derive(Clone, Copy, Debug)]
pub struct Parsed;
#[derive(Clone, Copy, Debug)]
pub struct Typed;
#[derive(Clone, Copy, Debug)]
pub struct Lowerable;

impl Phase for Parsed {
    /// An *optional declared* type: `Some(ty)` records a front-end annotation
    /// (e.g. a parameter's `: u8`) so inference can recover types it cannot infer
    /// from use (most importantly fixed-width integers); `None` = unannotated.
    type Ty = Option<CoreTy>;
    type Strategy = ();
}
impl Phase for Typed {
    type Ty = CoreTy;
    type Strategy = ();
}
impl Phase for Lowerable {
    type Ty = CoreTy;
    type Strategy = DisciplineId;
}

/// A whole program: user-defined types plus functions in some phase `P`.
pub struct Program<P: Phase> {
    /// Struct/enum definitions. Phase-independent (declared types are always concrete).
    pub types: Vec<TypeDef>,
    /// Implemented trait/type pairs known to this compilation unit. Kept at
    /// module scope because a generic call must validate a type argument against
    /// the implementation registry, independently of any method body.
    pub trait_impls: Vec<TraitImpl>,
    pub funcs: Vec<Function<P>>,
}

/// Evidence that `type_name` implements `trait_name` in the current module.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TraitImpl {
    pub trait_name: Sym,
    pub type_name: Sym,
}

/// A user-defined algebraic data type.
#[derive(Clone, Debug)]
pub enum TypeDef {
    Struct { name: Sym, type_params: Vec<Sym>, fields: Vec<FieldDef> },
    Enum { name: Sym, type_params: Vec<Sym>, variants: Vec<VariantDef> },
}
impl TypeDef {
    pub fn name(&self) -> Sym {
        match self {
            TypeDef::Struct { name, .. } | TypeDef::Enum { name, .. } => *name,
        }
    }
}

#[derive(Clone, Debug)]
pub struct FieldDef {
    pub name: Sym,
    pub ty: CoreTy,
}

/// A tuple-style enum variant (`Variant(T0, T1, ...)`); a unit variant has no fields.
#[derive(Clone, Debug)]
pub struct VariantDef {
    pub name: Sym,
    pub fields: Vec<CoreTy>,
}

/// How an [`RValue::Aggregate`] builds a value.
#[derive(Clone, Debug)]
pub enum AggKind {
    /// Construct struct `name`; operands are the fields in declaration order.
    Struct(Sym),
    /// Construct enum `name`'s variant `index`; operands are that variant's fields.
    Variant(Sym, u32),
    /// Construct a tuple `(a, b, ..)`; operands are the elements in order. Tuple
    /// elements are read back with ordinary `Proj::Field(i)` projections, so a
    /// tuple is an anonymous, positionally-typed struct.
    Tuple,
    /// Construct a fixed-size array `[a, b, ..]`; operands are the elements in
    /// order. Elements are read with `Proj::Index` (dynamic) — a bounds
    /// obligation guards each indexed read.
    Array,
    /// Construct a `Vec<T>` from zero or more initial elements (`Vec::new()` is
    /// the empty case). Like an array it stores its operands positionally, but it
    /// is growable (`RValue::VecPush`) and its length is dynamic.
    Vec,
}

/// The reserved name `result`, bound in a function's postcondition.
pub const RESULT_NAME: &str = "result";

pub struct Function<P: Phase> {
    pub name: Sym,
    /// Generic type parameters (`fn f<T, U>(..)`). Erased at runtime; opaque to checking.
    pub type_params: Vec<Sym>,
    /// Bounds on each declared generic parameter. These are retained through
    /// lowering so call-site elaboration can validate inferred substitutions.
    pub generic_bounds: Vec<(Sym, Vec<Sym>)>,
    pub params: Vec<LocalId>,
    /// Return type. Grows `()` -> `Ty`.
    pub ret: P::Ty,
    /// Precondition (over parameters).
    pub pre: Prop,
    /// Postcondition (over parameters and the reserved `result` symbol).
    pub post: Prop,
    pub locals: Vec<LocalDecl<P>>,
    pub blocks: Vec<Block<P>>,
    pub entry: BlockId,
}

pub struct LocalDecl<P: Phase> {
    pub name: Option<Sym>,
    /// Local's type. Grows `()` -> `Ty`.
    pub ty: P::Ty,
}

pub struct Block<P: Phase> {
    pub id: BlockId,
    pub stmts: Vec<Stmt>,
    pub term: Terminator<P>,
}

#[derive(Clone, Debug)]
pub struct Place {
    pub local: LocalId,
    pub proj: Vec<Proj>,
}
impl Place {
    pub fn local(local: LocalId) -> Self {
        Self { local, proj: Vec::new() }
    }
}

#[derive(Clone, Debug)]
pub enum Proj {
    /// Access field `n` of a struct, or field `n` of the variant a `Downcast` selected.
    Field(u32),
    /// View an enum place as its variant `index` (so subsequent `Field`s read that
    /// variant's payload). Lowering inserts these to bind `match`-arm fields.
    Downcast(u32),
    /// Dereference a reference place (follow a `&T`/`&mut T` to its pointee).
    Deref,
    /// Index into an array place: `a[i]`, where the index is an arbitrary
    /// operand. The verifier emits a bounds obligation (`0 <= i < len`) for each
    /// indexed access; the result type is the array's element type.
    Index(Operand),
}

/// Whether a borrow is shared (`&`) or mutable (`&mut`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BorrowKind {
    Shared,
    Mut,
}

#[derive(Clone, Debug)]
pub enum Operand {
    Copy(Place),
    Const(Const),
}

#[derive(Clone, Debug)]
pub enum Const {
    /// Full 128-bit magnitude; see `rv_syntax::Tok::Int`'s doc comment for the
    /// bit-pattern convention used for unsigned literals above `i128::MAX`.
    Int(i128),
    Float(f64),
    Str(String),
    Bool(bool),
    Unit,
}

/// Statements are phase-independent here (no phase-varying fields). `Assert`/`Assume`
/// are ghost (erased before codegen).
#[derive(Clone, Debug)]
pub enum Stmt {
    Assign(Place, RValue),
    Assert(Prop),
    Assume(Prop),
    /// A loop invariant, placed at a loop header. Verification assumes it on entry
    /// and must prove it preserved; codegen erases it (ghost).
    Invariant(Prop),
}

#[derive(Clone, Debug)]
pub enum RValue {
    Use(Operand),
    Bin(BinOp, Operand, Operand),
    /// A *wrapping* binary op (`a.wrapping_add(b)`, etc.): identical machine
    /// arithmetic to [`RValue::Bin`], but the verifier emits **no overflow
    /// obligation** for it — the explicit opt-out from the checked-overflow
    /// discipline. (Division-by-zero is still checked.)
    WrappingBin(BinOp, Operand, Operand),
    Un(UnOp, Operand),
    /// `v.len()` — the current length of the vector operand. Verified as an opaque
    /// length term; at runtime reads the vector's element count.
    VecLen(Operand),
    /// `push(v, x)` — the vector `v` grown by appending `x`. Modeled as a fresh
    /// (havoc'd) vector value in verification (its length changes); at runtime
    /// appends in place. Lowered from `v.push(x)` as `v = VecPush(v, x)`.
    VecPush(Operand, Operand),
    Call(Sym, Vec<Operand>),
    /// Build a closure value: the lifted top-level function `func` paired with the
    /// `captures` it closes over (captured *by value*). This is closure conversion:
    /// the front-end lifts a `|args| body` lambda to a top-level `func` whose first
    /// parameters are the captured variables, and emits this node at the lambda
    /// site. Opaque to the kernel `Term` (modeled as a fresh variable), like an
    /// aggregate.
    Closure(Sym, Vec<Operand>),
    /// Indirect call: invoke the closure value `callee` with `args`. At runtime the
    /// closure's captured environment is prepended to `args` before dispatch. In
    /// verification the target is not statically known, so the result is a fresh
    /// unconstrained term — sound (nothing false is assumed), like a call to a
    /// function with no known signature.
    CallClosure(Operand, Vec<Operand>),
    /// Construct an algebraic data value (struct or enum variant).
    Aggregate(AggKind, Vec<Operand>),
    /// Take a reference to a place: `&place` or `&mut place`.
    Ref(BorrowKind, Place),
}

/// One arm of a [`Terminator::Match`]: if the scrutinee's discriminant is `variant`,
/// jump to `target`. Field bindings are ordinary `Assign`s (via `Downcast`+`Field`)
/// at the start of the target block.
#[derive(Clone, Debug)]
pub struct MatchArm {
    pub variant: u32,
    pub target: BlockId,
}

pub enum Terminator<P: Phase> {
    Goto(BlockId),
    Branch { cond: Operand, then_blk: BlockId, else_blk: BlockId },
    /// Switch on an enum scrutinee's discriminant.
    Match { scrutinee: Operand, arms: Vec<MatchArm>, otherwise: Option<BlockId> },
    Return(Operand),
    /// Abort the program (an unrecoverable `panic`). Has no successors.
    Panic,
    /// Drop carries a *derived* memory-management strategy, present only in `Lowerable`.
    Drop { place: Place, strategy: P::Strategy, next: BlockId },
}
