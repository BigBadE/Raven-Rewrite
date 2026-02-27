//! Drop analysis for determining when and how types need to be dropped
//!
//! This module provides infrastructure for:
//! - Determining if a type needs drop (implements Drop trait or has fields that do)
//! - Generating the proper drop sequence (fields in reverse declaration order)
//! - Tracking drop glue requirements for code generation

use rv_hir::{ImplBlock, ImplId, TraitDef, TraitId, TypeDefId};
use std::collections::{HashMap, HashSet};

use crate::context::TyContext;
use crate::ty::{TyId, TyKind};

/// Result of drop analysis for a type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DropRequirement {
    /// Type does not need drop (primitive, Copy, or all fields are trivially droppable)
    None,
    /// Type implements Drop trait directly
    CustomDrop {
        /// The function to call for drop
        drop_fn: rv_hir::FunctionId,
    },
    /// Type has fields that need drop but no custom Drop impl
    FieldDrop {
        /// Fields that need drop, in drop order (reverse declaration)
        fields_to_drop: Vec<DropField>,
    },
    /// Type is a Box<T> requiring heap deallocation
    BoxDrop {
        /// Inner type that may also need drop
        inner_needs_drop: bool,
    },
}

/// A field that needs to be dropped
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DropField {
    /// Field index (0-based)
    pub index: usize,
    /// Field name (for diagnostics)
    pub name: rv_intern::Symbol,
    /// Type of the field
    pub ty: TyId,
    /// Drop requirement for this field
    pub requirement: Box<DropRequirement>,
}

/// Drop analyzer for determining drop requirements
///
/// Analyzes types to determine what drop glue needs to be generated.
/// Handles recursive type definitions and caches results.
pub struct DropAnalyzer<'a> {
    /// Trait definitions (for finding Drop trait by name)
    /// Note: Used only during construction to find the Drop trait
    _traits: &'a HashMap<TraitId, TraitDef>,
    /// Impl blocks (for finding Drop implementations)
    impl_blocks: &'a HashMap<ImplId, ImplBlock>,
    /// Struct definitions (for field analysis)
    structs: &'a HashMap<TypeDefId, rv_hir::StructDef>,
    /// Enum definitions (for variant analysis)
    enums: &'a HashMap<TypeDefId, rv_hir::EnumDef>,
    /// Functions (for finding drop methods)
    functions: &'a HashMap<rv_hir::FunctionId, rv_hir::Function>,
    /// HIR types arena for resolving TypeIds
    hir_types: &'a la_arena::Arena<rv_hir::Type>,
    /// Interner for symbol resolution
    interner: &'a rv_intern::Interner,
    /// Drop trait ID if found
    drop_trait: Option<TraitId>,
    /// Cache of analyzed types (avoids recomputation and handles cycles)
    cache: HashMap<TypeDefId, DropRequirement>,
    /// Types currently being analyzed (for cycle detection)
    in_progress: HashSet<TypeDefId>,
}

impl<'a> DropAnalyzer<'a> {
    /// Create a new drop analyzer
    #[must_use]
    pub fn new(
        traits: &'a HashMap<TraitId, TraitDef>,
        impl_blocks: &'a HashMap<ImplId, ImplBlock>,
        structs: &'a HashMap<TypeDefId, rv_hir::StructDef>,
        enums: &'a HashMap<TypeDefId, rv_hir::EnumDef>,
        functions: &'a HashMap<rv_hir::FunctionId, rv_hir::Function>,
        hir_types: &'a la_arena::Arena<rv_hir::Type>,
        interner: &'a rv_intern::Interner,
    ) -> Self {
        // Find the Drop trait by name
        // Note: In a full implementation, this would use lang_item lookup
        let drop_trait = traits
            .iter()
            .find(|(_, t)| interner.resolve(&t.name) == "Drop")
            .map(|(id, _)| *id);

        Self {
            _traits: traits,
            impl_blocks,
            structs,
            enums,
            functions,
            hir_types,
            interner,
            drop_trait,
            cache: HashMap::new(),
            in_progress: HashSet::new(),
        }
    }

    /// Analyze a type to determine its drop requirements
    ///
    /// Returns `true` if the type needs drop, `false` if it's trivially droppable.
    #[must_use]
    pub fn needs_drop(&mut self, ty: TyId, ctx: &TyContext) -> bool {
        !matches!(self.analyze_type(ty, ctx), DropRequirement::None)
    }

    /// Get the full drop requirements for a type
    pub fn analyze_type(&mut self, ty: TyId, ctx: &TyContext) -> DropRequirement {
        let ty = ctx.follow_var(ty);
        let ty_data = ctx.types.get(ty);

        match &ty_data.kind {
            // Primitives never need drop
            TyKind::Int(..)
            | TyKind::Float(..)
            | TyKind::Char
            | TyKind::Bool
            | TyKind::Unit
            | TyKind::Never
            | TyKind::String
            | TyKind::Param { .. }
            | TyKind::Var { .. }
            | TyKind::IntVar { .. }
            | TyKind::FloatVar { .. } => DropRequirement::None,

            // References and pointers never need drop (they don't own their data)
            TyKind::Ref { .. } | TyKind::Pointer { .. } => DropRequirement::None,

            // Function types never need drop
            TyKind::Function { .. } | TyKind::FunctionPointer { .. } => DropRequirement::None,

            // Box needs special handling
            TyKind::Box { inner } => {
                let inner_needs_drop = self.needs_drop(**inner, ctx);
                DropRequirement::BoxDrop { inner_needs_drop }
            }

            // Named/struct/enum types need analysis
            TyKind::Named { def, .. } => self.analyze_type_def(*def, ctx),

            TyKind::Struct { def_id, fields, .. } => {
                // First check if there's a custom Drop impl
                if let Some(drop_fn) = self.find_drop_impl(*def_id) {
                    return DropRequirement::CustomDrop { drop_fn };
                }

                // Check if cached
                if let Some(cached) = self.cache.get(def_id) {
                    return cached.clone();
                }

                // Prevent infinite recursion
                if self.in_progress.contains(def_id) {
                    return DropRequirement::None;
                }
                self.in_progress.insert(*def_id);

                // Analyze fields
                let mut fields_to_drop = Vec::new();
                for (i, (name, field_ty)) in fields.iter().enumerate() {
                    let field_req = self.analyze_type(*field_ty, ctx);
                    if field_req != DropRequirement::None {
                        fields_to_drop.push(DropField {
                            index: i,
                            name: *name,
                            ty: *field_ty,
                            requirement: Box::new(field_req),
                        });
                    }
                }

                self.in_progress.remove(def_id);

                let result = if fields_to_drop.is_empty() {
                    DropRequirement::None
                } else {
                    // Reverse for drop order (last declared drops first)
                    fields_to_drop.reverse();
                    DropRequirement::FieldDrop { fields_to_drop }
                };

                self.cache.insert(*def_id, result.clone());
                result
            }

            TyKind::Enum { def_id, variants } => {
                // First check if there's a custom Drop impl
                if let Some(drop_fn) = self.find_drop_impl(*def_id) {
                    return DropRequirement::CustomDrop { drop_fn };
                }

                // Check if cached
                if let Some(cached) = self.cache.get(def_id) {
                    return cached.clone();
                }

                // Prevent infinite recursion
                if self.in_progress.contains(def_id) {
                    return DropRequirement::None;
                }
                self.in_progress.insert(*def_id);

                // Check if any variant has fields that need drop
                let mut any_needs_drop = false;
                for (_name, variant_ty) in variants {
                    match variant_ty {
                        crate::ty::VariantTy::Unit => {}
                        crate::ty::VariantTy::Tuple(tys) => {
                            for ty in tys {
                                if self.needs_drop(*ty, ctx) {
                                    any_needs_drop = true;
                                    break;
                                }
                            }
                        }
                        crate::ty::VariantTy::Struct(fields) => {
                            for (_name, ty) in fields {
                                if self.needs_drop(*ty, ctx) {
                                    any_needs_drop = true;
                                    break;
                                }
                            }
                        }
                    }
                    if any_needs_drop {
                        break;
                    }
                }

                self.in_progress.remove(def_id);

                let result = if any_needs_drop {
                    // For enums, we can't pre-compute the drop sequence because
                    // it depends on which variant is active at runtime.
                    // Return a marker that says "needs drop" and the backend
                    // will need to generate a match expression to drop the
                    // active variant.
                    DropRequirement::FieldDrop {
                        fields_to_drop: Vec::new(),
                    }
                } else {
                    DropRequirement::None
                };

                self.cache.insert(*def_id, result.clone());
                result
            }

            // Tuples: drop elements in reverse order
            TyKind::Tuple { elements } => {
                let mut fields_to_drop = Vec::new();
                for (i, elem_ty) in elements.iter().enumerate() {
                    let req = self.analyze_type(*elem_ty, ctx);
                    if req != DropRequirement::None {
                        fields_to_drop.push(DropField {
                            index: i,
                            name: rv_intern::Symbol::default(),
                            ty: *elem_ty,
                            requirement: Box::new(req),
                        });
                    }
                }

                if fields_to_drop.is_empty() {
                    DropRequirement::None
                } else {
                    fields_to_drop.reverse();
                    DropRequirement::FieldDrop { fields_to_drop }
                }
            }

            // Arrays: drop all elements in reverse order
            TyKind::Array { element, size } => {
                let elem_req = self.analyze_type(**element, ctx);
                if elem_req == DropRequirement::None {
                    DropRequirement::None
                } else {
                    // For arrays, the backend generates a loop to drop each element
                    // We just need to signal that drop is needed
                    DropRequirement::FieldDrop {
                        fields_to_drop: (0..*size)
                            .rev()
                            .map(|i| DropField {
                                index: i,
                                name: rv_intern::Symbol::default(),
                                ty: **element,
                                requirement: Box::new(elem_req.clone()),
                            })
                            .collect(),
                    }
                }
            }

            // Slices: we don't own the data, so no drop
            TyKind::Slice { .. } => DropRequirement::None,

            // Dynamic trait objects: check if the trait has Drop
            TyKind::DynTrait { .. } => {
                // dyn Trait types call drop through vtable
                // This is handled specially by the backend
                DropRequirement::FieldDrop {
                    fields_to_drop: Vec::new(),
                }
            }

            // impl Trait: analyze the concrete type (if known)
            TyKind::ImplTrait { .. } => {
                // impl Trait at monomorphization will have concrete type
                // For now, conservatively assume it might need drop
                DropRequirement::FieldDrop {
                    fields_to_drop: Vec::new(),
                }
            }

            // Projections: analyze after normalization
            TyKind::Projection { .. } => {
                // Associated types should be normalized before drop analysis
                DropRequirement::None
            }
        }
    }

    /// Analyze a type definition (struct or enum)
    fn analyze_type_def(&mut self, def_id: TypeDefId, ctx: &TyContext) -> DropRequirement {
        // First check if there's a custom Drop impl
        if let Some(drop_fn) = self.find_drop_impl(def_id) {
            return DropRequirement::CustomDrop { drop_fn };
        }

        // Check if cached
        if let Some(cached) = self.cache.get(&def_id) {
            return cached.clone();
        }

        // Prevent infinite recursion
        if self.in_progress.contains(&def_id) {
            return DropRequirement::None;
        }
        self.in_progress.insert(def_id);

        // Try to find the definition and analyze it
        let result = if let Some(struct_def) = self.structs.get(&def_id) {
            self.analyze_struct_def(struct_def, ctx)
        } else if let Some(enum_def) = self.enums.get(&def_id) {
            self.analyze_enum_def(enum_def, ctx)
        } else {
            DropRequirement::None
        };

        self.in_progress.remove(&def_id);
        self.cache.insert(def_id, result.clone());
        result
    }

    /// Analyze a struct definition
    fn analyze_struct_def(
        &mut self,
        _struct_def: &rv_hir::StructDef,
        _ctx: &TyContext,
    ) -> DropRequirement {
        // For struct definitions, we need to convert HIR types to TyKind types
        // This is a placeholder - in practice, the types should already be
        // in the TyContext from type inference
        DropRequirement::None
    }

    /// Analyze an enum definition
    fn analyze_enum_def(
        &mut self,
        _enum_def: &rv_hir::EnumDef,
        _ctx: &TyContext,
    ) -> DropRequirement {
        // For enum definitions, we need to convert HIR types to TyKind types
        DropRequirement::None
    }

    /// Find a Drop impl for a type definition
    fn find_drop_impl(&self, def_id: TypeDefId) -> Option<rv_hir::FunctionId> {
        let drop_trait = self.drop_trait?;

        for impl_block in self.impl_blocks.values() {
            // Check if this is a Drop impl
            if impl_block.trait_ref != Some(drop_trait) {
                continue;
            }

            // Check if it's for our type by looking up the HIR type
            let hir_ty = &self.hir_types[impl_block.self_ty];
            let impl_def_id = match hir_ty {
                rv_hir::Type::Named { def, .. } => *def,
                _ => None,
            };

            if impl_def_id == Some(def_id) {
                // Find the drop method
                for method_id in &impl_block.methods {
                    if let Some(func) = self.functions.get(method_id) {
                        // The Drop trait has a single method called "drop"
                        if self.interner.resolve(&func.name) == "drop" {
                            return Some(*method_id);
                        }
                    }
                }
            }
        }

        None
    }
}

/// Generate drop glue for a type
///
/// Returns a sequence of drop operations to perform for a value of this type.
/// Operations are in the order they should be executed (reverse declaration order).
#[derive(Debug, Clone)]
pub enum DropOp {
    /// Call the custom drop function
    CallDrop {
        /// Function to call
        drop_fn: rv_hir::FunctionId,
    },
    /// Drop a field at the given index
    DropField {
        /// Field index
        index: usize,
        /// Nested operations for this field
        nested: Vec<DropOp>,
    },
    /// Drop all elements of an array in reverse order
    DropArray {
        /// Number of elements
        count: usize,
        /// Operations for each element
        element_ops: Vec<DropOp>,
    },
    /// Free heap memory (for Box)
    FreeHeap,
}

impl DropRequirement {
    /// Convert drop requirements to a sequence of operations
    #[must_use]
    pub fn to_drop_ops(&self) -> Vec<DropOp> {
        match self {
            DropRequirement::None => Vec::new(),
            DropRequirement::CustomDrop { drop_fn } => {
                vec![DropOp::CallDrop { drop_fn: *drop_fn }]
            }
            DropRequirement::FieldDrop { fields_to_drop } => fields_to_drop
                .iter()
                .map(|f| DropOp::DropField {
                    index: f.index,
                    nested: f.requirement.to_drop_ops(),
                })
                .collect(),
            DropRequirement::BoxDrop { inner_needs_drop } => {
                let mut ops = Vec::new();
                if *inner_needs_drop {
                    // Drop the inner value first
                    ops.push(DropOp::DropField {
                        index: 0,
                        nested: Vec::new(),
                    });
                }
                // Then free the heap memory
                ops.push(DropOp::FreeHeap);
                ops
            }
        }
    }
}
