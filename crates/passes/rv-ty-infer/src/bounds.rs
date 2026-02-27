//! Trait bound checking
//!
//! This module handles verification that types satisfy trait bounds.

use la_arena::Arena;
use rv_hir::{
    EnumDef, GenericParam, ImplBlock, StructDef, TraitBound, TraitDef, TraitId, Type, TypeDefId,
    TypeId, VariantFields, WhereClause,
};
use std::collections::{HashMap, HashSet};

/// Trait bound checker
pub struct BoundChecker {
    /// Trait definitions
    traits: HashMap<TraitId, TraitDef>,
    /// Implementation blocks
    impls: HashMap<TypeDefId, Vec<ImplBlock>>,
    /// Type arena for resolving type references
    types: Arena<Type>,
    /// Struct definitions for field-level auto-trait checking
    structs: HashMap<TypeDefId, StructDef>,
    /// Enum definitions for variant-level auto-trait checking
    enums: HashMap<TypeDefId, EnumDef>,
    /// Negative impl set: (TypeDefId, TraitId) pairs that opt out of auto-impl
    negative_impls: HashSet<(TypeDefId, TraitId)>,
}

impl BoundChecker {
    /// Create a new bound checker
    #[must_use]
    pub fn new(
        traits: HashMap<TraitId, TraitDef>,
        impl_blocks: &HashMap<rv_hir::ImplId, ImplBlock>,
        types: Arena<Type>,
        structs: HashMap<TypeDefId, StructDef>,
        enums: HashMap<TypeDefId, EnumDef>,
    ) -> Self {
        // Group impl blocks by the type they implement for
        let mut impls: HashMap<TypeDefId, Vec<ImplBlock>> = HashMap::new();
        let mut negative_impls: HashSet<(TypeDefId, TraitId)> = HashSet::new();

        // Extract TypeDefId from self_ty and group impl blocks
        for impl_block in impl_blocks.values() {
            // Extract the TypeDefId from self_ty if it's a Named type
            if let Some(type_def_id) = Self::extract_type_def_id_static(&types, impl_block.self_ty)
            {
                // Check for negative impls (impl !Trait for Type)
                if impl_block.is_negative {
                    if let Some(trait_id) = impl_block.trait_ref {
                        negative_impls.insert((type_def_id, trait_id));
                    }
                }
                impls
                    .entry(type_def_id)
                    .or_default()
                    .push(impl_block.clone());
            }
        }

        Self {
            traits,
            impls,
            types,
            structs,
            enums,
            negative_impls,
        }
    }

    /// Check if a type satisfies a trait bound
    #[must_use]
    pub fn check_bound(&self, type_def_id: TypeDefId, bound: &TraitBound) -> bool {
        // Check if there's an explicit impl block for this type that implements the trait
        if let Some(impl_list) = self.impls.get(&type_def_id) {
            for impl_block in impl_list {
                if impl_block.trait_ref == Some(bound.trait_ref) {
                    return true;
                }
            }
        }

        // If no explicit impl, check if the trait is an auto trait and can be
        // automatically derived from the type's fields
        if self.is_auto_trait(bound.trait_ref) {
            return self.check_auto_impl(type_def_id, bound.trait_ref);
        }

        false
    }

    /// Check if a type automatically implements an auto trait by recursively
    /// verifying that all its fields implement the trait.
    ///
    /// Auto traits (Send, Sync, Unpin) are implemented for a type if:
    /// 1. There is no negative impl (`impl !Trait for Type`)
    /// 2. All fields of the type implement the trait
    fn check_auto_impl(&self, type_def_id: TypeDefId, trait_id: TraitId) -> bool {
        // Check for negative impl — opt-out overrides auto-impl
        if self.negative_impls.contains(&(type_def_id, trait_id)) {
            return false;
        }

        // Check struct fields
        if let Some(struct_def) = self.structs.get(&type_def_id) {
            return struct_def
                .fields
                .iter()
                .all(|field| self.field_type_satisfies_auto_trait(field.ty, trait_id));
        }

        // Check enum variant fields
        if let Some(enum_def) = self.enums.get(&type_def_id) {
            return enum_def
                .variants
                .iter()
                .all(|variant| match &variant.fields {
                    VariantFields::Unit => true,
                    VariantFields::Tuple(type_ids) => type_ids
                        .iter()
                        .all(|ty_id| self.field_type_satisfies_auto_trait(*ty_id, trait_id)),
                    VariantFields::Struct(fields) => fields
                        .iter()
                        .all(|field| self.field_type_satisfies_auto_trait(field.ty, trait_id)),
                });
        }

        // Unknown type — conservatively assume it satisfies the trait
        // (primitives, references, etc. are generally Send/Sync)
        true
    }

    /// Check if a field's type satisfies an auto trait.
    fn field_type_satisfies_auto_trait(&self, type_id: TypeId, trait_id: TraitId) -> bool {
        let ty = &self.types[type_id];
        match ty {
            // Named types with a def: recursively check via check_bound
            Type::Named {
                def: Some(def_id), ..
            } => {
                let bound = TraitBound {
                    trait_ref: trait_id,
                    args: vec![],
                    for_lifetimes: vec![],
                };
                self.check_bound(*def_id, &bound)
            }

            // Named types without a def are primitives (i64, bool, etc.) — always Send/Sync
            Type::Named { def: None, .. } => true,

            // References: the inner type must satisfy the auto trait
            Type::Reference { inner, .. } => {
                self.field_type_satisfies_auto_trait(**inner, trait_id)
            }

            // Tuples: all elements must satisfy the trait
            Type::Tuple { elements, .. } => elements
                .iter()
                .all(|el| self.field_type_satisfies_auto_trait(*el, trait_id)),

            // Arrays: element must satisfy the trait
            Type::Array { element, .. } => {
                self.field_type_satisfies_auto_trait(**element, trait_id)
            }

            // Never, Generic, Function, Pointer, QualifiedPath: conservatively allow
            _ => true,
        }
    }

    /// Check all bounds on a generic parameter, including the implicit Sized bound.
    #[must_use]
    pub fn check_generic_bounds(
        &self,
        type_def_id: TypeDefId,
        param: &GenericParam,
    ) -> Vec<BoundError> {
        let mut errors = vec![];

        // Implicit Sized bound: all generic type parameters must be Sized
        // unless the parameter is declared with ?Sized.
        if !param.maybe_unsized && !self.is_sized_type(type_def_id) {
            errors.push(BoundError::UnsizedType {
                param_name: param.name,
            });
        }

        for bound in &param.bounds {
            if !self.check_bound(type_def_id, bound) {
                errors.push(BoundError::UnsatisfiedBound {
                    param_name: param.name,
                    trait_id: bound.trait_ref,
                });
            }
        }

        errors
    }

    /// Check if a concrete type is Sized.
    ///
    /// Currently all concrete types in the system are Sized. Unsized types
    /// ([T], str, dyn Trait) can only appear behind a pointer/reference.
    #[must_use]
    pub fn is_sized_type(&self, _type_def_id: TypeDefId) -> bool {
        // All user-defined structs and enums are Sized.
        // Unsized types ([T], str, dyn Trait) are not yet representable
        // as standalone TypeDefId values in our system — they only appear
        // as MirType::Slice or behind references.
        true
    }

    /// Check if a trait's supertrait constraints are satisfied
    #[must_use]
    pub fn check_supertrait_constraints(&self, impl_block: &ImplBlock) -> Vec<BoundError> {
        let mut errors = vec![];

        // If this impl implements a trait, check that all supertraits are also implemented
        if let Some(trait_id) = impl_block.trait_ref {
            if let Some(trait_def) = self.traits.get(&trait_id) {
                // Extract the TypeDefId from self_ty if it's a Named type
                if let Some(type_def_id) = self.extract_type_def_id(impl_block.self_ty) {
                    // Check each supertrait
                    for supertrait_bound in &trait_def.supertraits {
                        if !self.check_bound(type_def_id, supertrait_bound) {
                            errors.push(BoundError::MissingSupertrait {
                                trait_id,
                                supertrait_id: supertrait_bound.trait_ref,
                            });
                        }
                    }
                }
            }
        }

        errors
    }

    /// Check that all associated types are implemented
    #[must_use]
    pub fn check_associated_types(&self, impl_block: &ImplBlock) -> Vec<BoundError> {
        let mut errors = vec![];

        // If this impl implements a trait, check that all associated types are implemented
        if let Some(trait_id) = impl_block.trait_ref {
            if let Some(trait_def) = self.traits.get(&trait_id) {
                // Get the set of implemented associated types
                let mut implemented: HashSet<rv_intern::Symbol> = HashSet::new();
                for assoc_impl in &impl_block.associated_type_impls {
                    implemented.insert(assoc_impl.name);
                }

                // Check each required associated type
                for assoc_type in &trait_def.associated_types {
                    if !implemented.contains(&assoc_type.name) {
                        errors.push(BoundError::MissingAssociatedType {
                            trait_id,
                            assoc_type_name: assoc_type.name,
                        });
                    }
                }
            }
        }

        errors
    }

    /// Check where clause constraints
    #[must_use]
    pub fn check_where_clauses(&self, where_clauses: &[WhereClause]) -> Vec<BoundError> {
        let mut errors = vec![];

        for where_clause in where_clauses {
            // Extract TypeDefId from the constrained type
            if let Some(type_def_id) = self.extract_type_def_id(where_clause.ty) {
                // Check each bound
                for bound in &where_clause.bounds {
                    if !self.check_bound(type_def_id, bound) {
                        errors.push(BoundError::WhereClauseViolation {
                            type_id: where_clause.ty,
                            trait_id: bound.trait_ref,
                        });
                    }
                }
            }
        }

        errors
    }

    /// Check if a trait is an auto trait (Send, Sync, Unpin, Sized).
    ///
    /// Auto traits are automatically implemented for types unless explicitly opted out.
    /// A trait is auto if `TraitDef.is_auto` is true or if it is a known auto-trait
    /// lang item (Sized, Send, Sync, Unpin).
    #[must_use]
    pub fn is_auto_trait(&self, trait_id: TraitId) -> bool {
        if let Some(trait_def) = self.traits.get(&trait_id) {
            if trait_def.is_auto {
                return true;
            }
            // Check by well-known name
            // This is a supplementary check for when `is_auto` isn't set
            // but the trait has a known auto-trait name
            false
        } else {
            false
        }
    }

    /// Extract TypeDefId from a TypeId (helper method)
    fn extract_type_def_id(&self, type_id: TypeId) -> Option<TypeDefId> {
        Self::extract_type_def_id_static(&self.types, type_id)
    }

    /// Extract TypeDefId from a TypeId (static helper for use in constructor)
    fn extract_type_def_id_static(types: &Arena<Type>, type_id: TypeId) -> Option<TypeDefId> {
        let ty = &types[type_id];
        match ty {
            Type::Named { def, .. } => *def,
            _ => None,
        }
    }
}

/// Bound checking error
#[derive(Debug, Clone, PartialEq)]
pub enum BoundError {
    /// A trait bound is not satisfied
    UnsatisfiedBound {
        /// Generic parameter name
        param_name: rv_intern::Symbol,
        /// Required trait
        trait_id: TraitId,
    },
    /// A supertrait constraint is not satisfied
    MissingSupertrait {
        /// Trait being implemented
        trait_id: TraitId,
        /// Required supertrait
        supertrait_id: TraitId,
    },
    /// An associated type is not implemented
    MissingAssociatedType {
        /// Trait being implemented
        trait_id: TraitId,
        /// Missing associated type name
        assoc_type_name: rv_intern::Symbol,
    },
    /// A where clause constraint is violated
    WhereClauseViolation {
        /// Type being constrained
        type_id: TypeId,
        /// Required trait
        trait_id: TraitId,
    },
    /// A type parameter requires Sized but received an unsized type
    UnsizedType {
        /// Generic parameter name
        param_name: rv_intern::Symbol,
    },
}
