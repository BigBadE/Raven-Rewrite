//! Trait bound checking
//!
//! This module handles verification that types satisfy trait bounds.

use rv_arena::Arena;
use rv_hir::{GenericParam, ImplBlock, TraitBound, TraitDef, TraitId, Type, TypeDefId, TypeId, WhereClause};
use std::collections::{HashMap, HashSet};

/// Trait bound checker
pub struct BoundChecker {
    /// Trait definitions
    traits: HashMap<TraitId, TraitDef>,
    /// Implementation blocks
    impls: HashMap<TypeDefId, Vec<ImplBlock>>,
    /// Type arena for resolving type references
    types: Arena<Type>,
}

impl BoundChecker {
    /// Create a new bound checker
    #[must_use]
    pub fn new(
        traits: HashMap<TraitId, TraitDef>,
        impl_blocks: &HashMap<rv_hir::ImplId, ImplBlock>,
        types: Arena<Type>,
    ) -> Self {
        // Group impl blocks by the type they implement for
        let mut impls: HashMap<TypeDefId, Vec<ImplBlock>> = HashMap::new();

        // Extract TypeDefId from self_ty and group impl blocks
        for impl_block in impl_blocks.values() {
            // Extract the TypeDefId from self_ty if it's a Named type
            if let Some(type_def_id) = Self::extract_type_def_id_static(&types, impl_block.self_ty) {
                impls.entry(type_def_id).or_default().push(impl_block.clone());
            }
        }

        Self {
            traits,
            impls,
            types,
        }
    }

    /// Check if a type satisfies a trait bound
    #[must_use]
    pub fn check_bound(&self, type_def_id: TypeDefId, bound: &TraitBound) -> bool {
        // Check if there's an impl block for this type that implements the trait
        if let Some(impl_list) = self.impls.get(&type_def_id) {
            for impl_block in impl_list {
                if impl_block.trait_ref == Some(bound.trait_ref) {
                    return true;
                }
            }
        }
        false
    }

    /// Check all bounds on a generic parameter
    #[must_use]
    pub fn check_generic_bounds(&self, type_def_id: TypeDefId, param: &GenericParam) -> Vec<BoundError> {
        let mut errors = vec![];

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
#[derive(Debug, Clone)]
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
}
