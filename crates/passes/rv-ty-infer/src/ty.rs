//! Type representation
#![allow(
    clippy::min_ident_chars,
    unused_variables,
    unused_assignments,
    reason = "Ty and TyId are conventional names, fields used by generated visitor"
)]

use crate::context::TyContext;
use la_arena::{Arena, Idx};
use rv_hir::TypeDefId;
use rv_intern::Symbol;
use std::fmt;

/// Type ID for arena allocation
pub type TyId = Idx<Ty>;

/// A type in the type system
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ty {
    /// Type kind
    pub kind: TyKind,
}

/// Kind of type
#[derive(Debug, Clone, PartialEq, Eq, Hash, rv_derive::Visitor)]
#[visitor(context = "TyContext", id_type = "TyId")]
#[allow(
    unused,
    reason = "Variants and fields are used by rv_derive::Visitor proc macro code generation"
)]
pub enum TyKind {
    /// Integer type with width and signedness
    Int(rv_hir::IntWidth, rv_hir::Signedness),
    /// Float type with width
    Float(rv_hir::FloatWidth),
    /// Character type
    Char,
    /// Boolean type
    Bool,
    /// String type
    String,
    /// Unit type (empty tuple)
    Unit,
    /// Never type (bottom type)
    Never,

    /// Function type
    Function {
        /// Parameter types
        params: Vec<TyId>,
        /// Return type
        ret: Box<TyId>,
    },

    /// Tuple type
    Tuple {
        /// Element types
        elements: Vec<TyId>,
    },

    /// Named type (struct, enum, etc.)
    Named {
        /// Type name
        name: Symbol,
        /// Resolved type definition
        def: TypeDefId,
        /// Generic arguments
        args: Vec<TyId>,
    },

    /// Generic type parameter
    Param {
        /// Parameter index
        index: u32,
        /// Parameter name
        name: Symbol,
    },

    /// Integer inference variable (unsuffixed integer literal).
    /// Can unify with any `Int(...)` type. Defaults to `i32` when unconstrained.
    IntVar {
        /// Variable ID for tracking
        id: TyVarId,
    },

    /// Float inference variable (unsuffixed float literal).
    /// Can unify with any `Float(...)` type. Defaults to `f64` when unconstrained.
    FloatVar {
        /// Variable ID for tracking
        id: TyVarId,
    },

    /// Type variable (unknown type to be inferred)
    Var {
        /// Variable ID
        id: TyVarId,
    },

    /// Reference type
    Ref {
        /// Is mutable
        mutable: bool,
        /// Inner type
        inner: Box<TyId>,
        /// Lifetime (None = inferred)
        lifetime: Option<rv_span::LifetimeId>,
    },

    /// Struct type
    Struct {
        /// Type definition ID
        def_id: TypeDefId,
        /// Field types (name, type)
        fields: Vec<(Symbol, TyId)>,
    },

    /// Enum type
    Enum {
        /// Type definition ID
        def_id: TypeDefId,
        /// Variant types (name, variant_ty)
        variants: Vec<(Symbol, VariantTy)>,
    },

    /// Array type
    Array {
        /// Element type
        element: Box<TyId>,
        /// Array size
        size: usize,
    },

    /// Slice type
    Slice {
        /// Element type
        element: Box<TyId>,
    },

    /// Raw pointer type (*const T or *mut T)
    Pointer {
        /// Is mutable (*mut vs *const)
        mutable: bool,
        /// Pointed-to type
        inner: Box<TyId>,
    },

    /// Dynamic trait object type (dyn Trait)
    DynTrait {
        /// Primary trait ID (resolved)
        principal: rv_hir::TraitId,
        /// Primary trait name (for display)
        principal_name: Symbol,
    },

    /// Impl trait type (impl Trait) — opaque type
    ImplTrait {
        /// Primary trait name
        principal: Symbol,
    },

    /// Associated type projection (e.g., `T::Item`, `<T as Trait>::Output`)
    ///
    /// This represents a type that depends on trait resolution. It must be
    /// normalized to a concrete type before code generation.
    Projection {
        /// The base type (e.g., `T` in `T::Item`)
        base: Box<TyId>,
        /// The associated type name (e.g., `Item`)
        assoc_type: Symbol,
        /// The trait that defines this associated type (if known)
        trait_ref: Option<rv_hir::TraitId>,
    },

    /// Function pointer type: fn(T, U) -> V
    FunctionPointer {
        /// Parameter types
        params: Vec<TyId>,
        /// Return type
        ret: Box<TyId>,
        /// ABI (None = Rust, Some("C") = extern "C", etc.)
        abi: Option<String>,
    },

    /// Box<T> - heap-allocated smart pointer
    Box {
        /// Inner type
        inner: Box<TyId>,
    },
}

/// Enum variant type
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VariantTy {
    /// Unit variant (no fields)
    Unit,
    /// Tuple variant
    Tuple(Vec<TyId>),
    /// Struct variant
    Struct(Vec<(Symbol, TyId)>),
}

/// Type variable ID
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyVarId(pub u32);

impl fmt::Display for TyVarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "?{}", self.0)
    }
}

/// Type arena for allocating types
#[derive(Debug, Default, Clone, PartialEq)]
pub struct TyArena {
    arena: Arena<Ty>,
}

impl TyArena {
    /// Create a new type arena
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocate a type
    pub fn alloc(&mut self, kind: TyKind) -> TyId {
        self.arena.alloc(Ty { kind })
    }

    /// Get a type by ID
    pub fn get(&self, id: TyId) -> &Ty {
        &self.arena[id]
    }

    /// Allocate an integer type with specific width and signedness
    pub fn int_typed(&mut self, width: rv_hir::IntWidth, sign: rv_hir::Signedness) -> TyId {
        self.alloc(TyKind::Int(width, sign))
    }

    /// Allocate the default integer type (i32, matching Rust's default for unsuffixed literals)
    pub fn int(&mut self) -> TyId {
        self.alloc(TyKind::Int(
            rv_hir::IntWidth::I32,
            rv_hir::Signedness::Signed,
        ))
    }

    /// Allocate a float type with specific width
    pub fn float_typed(&mut self, width: rv_hir::FloatWidth) -> TyId {
        self.alloc(TyKind::Float(width))
    }

    /// Allocate the default float type (f64, matching Rust's default for unsuffixed literals)
    pub fn float(&mut self) -> TyId {
        self.alloc(TyKind::Float(rv_hir::FloatWidth::F64))
    }

    /// Allocate char type
    pub fn char(&mut self) -> TyId {
        self.alloc(TyKind::Char)
    }

    /// Allocate bool type
    pub fn bool(&mut self) -> TyId {
        self.alloc(TyKind::Bool)
    }

    /// Allocate string type
    pub fn string(&mut self) -> TyId {
        self.alloc(TyKind::String)
    }

    /// Allocate unit type
    pub fn unit(&mut self) -> TyId {
        self.alloc(TyKind::Unit)
    }

    /// Allocate never type
    pub fn never(&mut self) -> TyId {
        self.alloc(TyKind::Never)
    }

    /// Allocate type variable
    pub fn var(&mut self, id: TyVarId) -> TyId {
        self.alloc(TyKind::Var { id })
    }

    /// Allocate Box<T> type
    pub fn boxed(&mut self, inner: TyId) -> TyId {
        self.alloc(TyKind::Box {
            inner: Box::new(inner),
        })
    }
}

/// Struct layout information
#[derive(Debug, Clone)]
pub struct StructLayout {
    /// Total size in bytes
    pub size: usize,
    /// Alignment in bytes
    pub align: usize,
    /// Field offsets
    pub field_offsets: Vec<usize>,
}

impl StructLayout {
    /// Compute layout for a struct with given field types
    pub fn compute(fields: &[(Symbol, TyId)], ty_arena: &TyArena) -> Self {
        let mut size = 0;
        let mut align = 1;
        let mut offsets = Vec::new();

        for (_, ty_id) in fields {
            let field_align = Self::alignment(*ty_id, ty_arena);
            let field_size = Self::size(*ty_id, ty_arena);

            // Align current offset to field alignment
            size = align_to(size, field_align);
            offsets.push(size);

            size += field_size;
            align = align.max(field_align);
        }

        // Final struct size must be multiple of alignment
        size = align_to(size, align);

        Self {
            size,
            align,
            field_offsets: offsets,
        }
    }

    /// Get size of a type in bytes
    fn size(ty_id: TyId, ty_arena: &TyArena) -> usize {
        match &ty_arena.get(ty_id).kind {
            TyKind::Int(w, _) => w.byte_size(),
            TyKind::Float(w) => w.byte_size(),
            TyKind::Char => 4,
            TyKind::Bool => 1,
            TyKind::String => 8, // Pointer
            TyKind::Unit => 0,
            TyKind::Ref { .. } => 8, // Pointer
            TyKind::Struct { fields, .. } => Self::compute(fields, ty_arena).size,
            TyKind::Enum { variants, .. } => {
                // Discriminant (u32) + max variant size
                let max_variant_size = variants
                    .iter()
                    .map(|(_, variant_ty)| Self::variant_size(variant_ty, ty_arena))
                    .max()
                    .unwrap_or(0);
                4 + max_variant_size
            }
            TyKind::Array { element, size } => Self::size(**element, ty_arena) * size,
            TyKind::Slice { .. } => 16, // fat pointer (ptr + len)
            TyKind::Tuple { elements } => {
                // For tuples, just sum up the sizes with alignment
                elements.iter().map(|ty| Self::size(*ty, ty_arena)).sum()
            }
            _ => 8, // Default to pointer size
        }
    }

    /// Get alignment of a type in bytes
    fn alignment(ty_id: TyId, ty_arena: &TyArena) -> usize {
        match &ty_arena.get(ty_id).kind {
            TyKind::Int(w, _) => w.byte_size(),
            TyKind::Float(w) => w.byte_size(),
            TyKind::Bool => 1,
            TyKind::String => 8,
            TyKind::Unit => 1,
            TyKind::Ref { .. } => 8,
            TyKind::Struct { fields, .. } => fields
                .iter()
                .map(|(_, ty)| Self::alignment(*ty, ty_arena))
                .max()
                .unwrap_or(1),
            TyKind::Enum { .. } => 4, // Discriminant alignment
            TyKind::Array { element, .. } => Self::alignment(**element, ty_arena),
            TyKind::Slice { .. } => 8,
            TyKind::Tuple { elements } => elements
                .iter()
                .map(|ty| Self::alignment(*ty, ty_arena))
                .max()
                .unwrap_or(1),
            _ => 8,
        }
    }

    /// Get size of an enum variant
    fn variant_size(variant_ty: &VariantTy, ty_arena: &TyArena) -> usize {
        match variant_ty {
            VariantTy::Unit => 0,
            VariantTy::Tuple(types) => {
                // Sum up the sizes of all tuple elements
                types.iter().map(|ty| Self::size(*ty, ty_arena)).sum()
            }
            VariantTy::Struct(fields) => Self::compute(fields, ty_arena).size,
        }
    }
}

/// Align offset to the given alignment
fn align_to(offset: usize, align: usize) -> usize {
    (offset + align - 1) & !(align - 1)
}
