//! Trait coherence checking
//!
//! Detects overlapping and conflicting trait implementations.
//! Two impl blocks conflict when they could apply to the same type for the
//! same trait, making method resolution ambiguous.
//!
//! Checked cases:
//! - Two concrete impls of the same trait for the same type
//! - Two blanket impls of the same trait with overlapping bounds
//! - A blanket impl that overlaps with a concrete impl (without specialization)

use la_arena::Arena;
use rv_hir::{ImplBlock, ImplId, TraitDef, TraitId, Type, TypeDefId};
use rv_span::FileSpan;
use std::collections::HashMap;

/// Coherence checking errors
#[derive(Debug, Clone, PartialEq)]
pub enum CoherenceError {
    /// Two concrete impl blocks implement the same trait for the same type
    OverlappingImpls {
        /// The trait being implemented
        trait_id: TraitId,
        /// First impl block
        impl1: ImplId,
        /// Location of first impl
        span1: FileSpan,
        /// Second impl block
        impl2: ImplId,
        /// Location of second impl
        span2: FileSpan,
    },
    /// Two blanket impls of the same trait could apply to the same type
    OverlappingBlanketImpls {
        /// The trait being implemented
        trait_id: TraitId,
        /// First blanket impl
        impl1: ImplId,
        /// Location of first impl
        span1: FileSpan,
        /// Second blanket impl
        impl2: ImplId,
        /// Location of second impl
        span2: FileSpan,
    },
    /// A blanket impl conflicts with a concrete impl (no specialization support)
    BlanketConcreteConflict {
        /// The trait being implemented
        trait_id: TraitId,
        /// The blanket impl
        blanket_impl: ImplId,
        /// Location of blanket impl
        blanket_span: FileSpan,
        /// The concrete impl
        concrete_impl: ImplId,
        /// Location of concrete impl
        concrete_span: FileSpan,
    },
    /// Duplicate inherent impl (two inherent impls for the same type with
    /// a method of the same name)
    DuplicateInherentMethod {
        /// The type that has duplicate methods
        type_def_id: TypeDefId,
        /// Method name
        method_name: rv_intern::Symbol,
        /// First impl block
        impl1: ImplId,
        /// Location of first impl
        span1: FileSpan,
        /// Second impl block
        impl2: ImplId,
        /// Location of second impl
        span2: FileSpan,
    },
}

impl std::fmt::Display for CoherenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CoherenceError::OverlappingImpls { trait_id, .. } => {
                write!(
                    f,
                    "conflicting implementations of trait {:?}: \
                     only one impl per type is allowed",
                    trait_id
                )
            }
            CoherenceError::OverlappingBlanketImpls { trait_id, .. } => {
                write!(
                    f,
                    "conflicting blanket implementations of trait {:?}: \
                     bounds overlap and could apply to the same type",
                    trait_id
                )
            }
            CoherenceError::BlanketConcreteConflict { trait_id, .. } => {
                write!(
                    f,
                    "conflicting implementations of trait {:?}: \
                     blanket impl conflicts with a concrete impl",
                    trait_id
                )
            }
            CoherenceError::DuplicateInherentMethod { method_name, .. } => {
                write!(
                    f,
                    "duplicate definitions with name `{:?}`: \
                     multiple inherent impls define the same method",
                    method_name
                )
            }
        }
    }
}

/// Trait coherence checker
///
/// Verifies that no two impl blocks in the program conflict. Two trait impls
/// conflict when they implement the same trait for types that could overlap.
pub struct CoherenceChecker<'a> {
    /// All impl blocks in the program
    impl_blocks: &'a HashMap<ImplId, ImplBlock>,
    /// Type arena for resolving self_ty
    types: &'a Arena<Type>,
    /// Functions (for looking up method names in inherent impls)
    functions: &'a HashMap<rv_hir::FunctionId, rv_hir::Function>,
}

impl<'a> CoherenceChecker<'a> {
    /// Create a new coherence checker
    #[must_use]
    pub fn new(
        impl_blocks: &'a HashMap<ImplId, ImplBlock>,
        types: &'a Arena<Type>,
        functions: &'a HashMap<rv_hir::FunctionId, rv_hir::Function>,
    ) -> Self {
        Self {
            impl_blocks,
            types,
            functions,
        }
    }

    /// Run all coherence checks and return any errors found
    #[must_use]
    pub fn check_all(&self) -> Vec<CoherenceError> {
        let mut errors = Vec::new();
        errors.extend(self.check_trait_impl_overlaps());
        errors.extend(self.check_inherent_impl_overlaps());
        errors
    }

    /// Check for overlapping trait implementations.
    ///
    /// Groups trait impls by trait ID and checks each group for conflicts:
    /// - concrete vs concrete (same TypeDefId)
    /// - blanket vs blanket (unconstrained overlap)
    /// - blanket vs concrete (always conflicts without specialization)
    fn check_trait_impl_overlaps(&self) -> Vec<CoherenceError> {
        let mut errors = Vec::new();

        // Group trait impls by trait ID, skipping synthesized impls
        let mut trait_impls: HashMap<TraitId, Vec<&ImplBlock>> = HashMap::new();
        for impl_block in self.impl_blocks.values() {
            if impl_block.is_synthesized {
                continue;
            }
            if let Some(trait_id) = impl_block.trait_ref {
                trait_impls.entry(trait_id).or_default().push(impl_block);
            }
        }

        // Check each trait's impls for overlaps
        for (trait_id, impls) in &trait_impls {
            // Separate into concrete and blanket impls
            let mut concrete: Vec<&ImplBlock> = Vec::new();
            let mut blanket: Vec<&ImplBlock> = Vec::new();

            for imp in impls {
                if imp.is_blanket {
                    blanket.push(imp);
                } else {
                    concrete.push(imp);
                }
            }

            // Check concrete vs concrete: same trait + same type = conflict
            for i in 0..concrete.len() {
                for j in (i + 1)..concrete.len() {
                    if self.concrete_types_overlap(concrete[i], concrete[j]) {
                        errors.push(CoherenceError::OverlappingImpls {
                            trait_id: *trait_id,
                            impl1: concrete[i].id,
                            span1: concrete[i].span,
                            impl2: concrete[j].id,
                            span2: concrete[j].span,
                        });
                    }
                }
            }

            // Check blanket vs blanket: two blanket impls of the same trait
            // conflict if their bounds don't exclude each other.
            // Conservative: if neither has bounds that provably exclude the
            // other, report overlap.
            for i in 0..blanket.len() {
                for j in (i + 1)..blanket.len() {
                    if self.blanket_impls_overlap(blanket[i], blanket[j]) {
                        errors.push(CoherenceError::OverlappingBlanketImpls {
                            trait_id: *trait_id,
                            impl1: blanket[i].id,
                            span1: blanket[i].span,
                            impl2: blanket[j].id,
                            span2: blanket[j].span,
                        });
                    }
                }
            }

            // Check blanket vs concrete: without specialization, a blanket
            // impl always conflicts with a concrete impl for the same trait
            // (because the blanket impl covers the concrete type too).
            // Skip this check if the blanket impl has bounds that the
            // concrete type might not satisfy — but conservatively, we flag
            // it if the blanket impl's bounds are a subset of what the
            // concrete type provides.
            for b in &blanket {
                for c in &concrete {
                    if self.blanket_covers_concrete(b, c) {
                        errors.push(CoherenceError::BlanketConcreteConflict {
                            trait_id: *trait_id,
                            blanket_impl: b.id,
                            blanket_span: b.span,
                            concrete_impl: c.id,
                            concrete_span: c.span,
                        });
                    }
                }
            }
        }

        errors
    }

    /// Check for overlapping inherent implementations.
    ///
    /// Two inherent impl blocks for the same type must not define a method
    /// with the same name, as that makes method resolution ambiguous.
    fn check_inherent_impl_overlaps(&self) -> Vec<CoherenceError> {
        let mut errors = Vec::new();

        // Group inherent impls (no trait_ref) by TypeDefId, skipping synthesized impls
        let mut inherent_impls: HashMap<TypeDefId, Vec<&ImplBlock>> = HashMap::new();
        for impl_block in self.impl_blocks.values() {
            if impl_block.trait_ref.is_some() || impl_block.is_synthesized {
                continue; // Skip trait impls and synthesized impls
            }
            if let Some(type_def_id) = self.extract_type_def_id(impl_block.self_ty) {
                inherent_impls
                    .entry(type_def_id)
                    .or_default()
                    .push(impl_block);
            }
        }

        // For each type, check all pairs of inherent impls for duplicate methods
        for (type_def_id, impls) in &inherent_impls {
            for i in 0..impls.len() {
                for j in (i + 1)..impls.len() {
                    self.check_duplicate_methods(*type_def_id, impls[i], impls[j], &mut errors);
                }
            }
        }

        errors
    }

    /// Check if two concrete impls have the same self type
    fn concrete_types_overlap(&self, a: &ImplBlock, b: &ImplBlock) -> bool {
        let a_def = self.extract_type_def_id(a.self_ty);
        let b_def = self.extract_type_def_id(b.self_ty);
        match (a_def, b_def) {
            (Some(a_id), Some(b_id)) => a_id == b_id,
            _ => false,
        }
    }

    /// Check if two blanket impls could overlap.
    ///
    /// Two blanket impls overlap when a type could satisfy both sets of bounds
    /// simultaneously. Without full bound negation, we use a conservative
    /// approach: they overlap unless their bounds are provably disjoint
    /// (i.e., they require different, non-overlapping traits that no single
    /// type could implement).
    fn blanket_impls_overlap(&self, a: &ImplBlock, b: &ImplBlock) -> bool {
        // If both are fully unconstrained (impl<T> Trait for T), they
        // definitely overlap.
        if a.generic_params.iter().all(|p| p.bounds.is_empty())
            && b.generic_params.iter().all(|p| p.bounds.is_empty())
        {
            return true;
        }

        // If one is unconstrained and the other has bounds, the unconstrained
        // one covers everything including all types the bounded one covers.
        if a.generic_params.iter().all(|p| p.bounds.is_empty())
            || b.generic_params.iter().all(|p| p.bounds.is_empty())
        {
            return true;
        }

        // Both have bounds. Check if their bound sets share any common trait.
        // If they do, a type implementing that trait could satisfy both.
        // This is conservative — real Rust uses more sophisticated analysis.
        let a_traits: std::collections::HashSet<TraitId> = a
            .generic_params
            .iter()
            .flat_map(|p| p.bounds.iter().map(|b| b.trait_ref))
            .collect();

        let b_traits: std::collections::HashSet<TraitId> = b
            .generic_params
            .iter()
            .flat_map(|p| p.bounds.iter().map(|b| b.trait_ref))
            .collect();

        // If they share any required trait, types implementing that trait
        // could satisfy both impls.
        if !a_traits.is_disjoint(&b_traits) {
            return true;
        }

        // If all required traits are completely disjoint, they don't overlap
        // (a type implementing all of A's traits wouldn't need to implement
        // any of B's, and vice versa — so no single type triggers both).
        // However, a type could implement traits from both sets, so this is
        // only safe if we know traits are mutually exclusive. Without that
        // info, conservatively report overlap.
        true
    }

    /// Check if a blanket impl covers a concrete impl's type.
    ///
    /// A blanket impl `impl<T> Trait for T` covers every concrete type.
    /// A blanket impl `impl<T: Bound> Trait for T` covers the concrete type
    /// only if that type satisfies `Bound`.
    fn blanket_covers_concrete(&self, blanket: &ImplBlock, concrete: &ImplBlock) -> bool {
        // Unconstrained blanket impl covers everything
        if blanket.generic_params.iter().all(|p| p.bounds.is_empty()) {
            return true;
        }

        // Bounded blanket impl: check if the concrete type satisfies the
        // blanket's bounds. We need to look up whether the concrete type
        // implements the required traits.
        let concrete_type_def = self.extract_type_def_id(concrete.self_ty);
        let Some(concrete_type_id) = concrete_type_def else {
            return false;
        };

        // Check each bound on the blanket impl's generic params
        for param in &blanket.generic_params {
            for bound in &param.bounds {
                // Does the concrete type implement this bound's trait?
                if !self.type_implements_trait(concrete_type_id, bound.trait_ref) {
                    // The concrete type doesn't satisfy this bound,
                    // so the blanket impl doesn't cover it.
                    return false;
                }
            }
        }

        // The concrete type satisfies all blanket bounds — conflict
        true
    }

    /// Check if a type has an impl for a given trait
    fn type_implements_trait(&self, type_def_id: TypeDefId, trait_id: TraitId) -> bool {
        for impl_block in self.impl_blocks.values() {
            if impl_block.trait_ref != Some(trait_id) {
                continue;
            }
            if impl_block.is_blanket {
                continue; // Only check concrete impls to avoid circularity
            }
            if let Some(def) = self.extract_type_def_id(impl_block.self_ty) {
                if def == type_def_id {
                    return true;
                }
            }
        }
        false
    }

    /// Check two inherent impl blocks for duplicate method names
    fn check_duplicate_methods(
        &self,
        type_def_id: TypeDefId,
        a: &ImplBlock,
        b: &ImplBlock,
        errors: &mut Vec<CoherenceError>,
    ) {
        for a_method_id in &a.methods {
            let Some(a_func) = self.functions.get(a_method_id) else {
                continue;
            };
            for b_method_id in &b.methods {
                let Some(b_func) = self.functions.get(b_method_id) else {
                    continue;
                };
                if a_func.name == b_func.name {
                    errors.push(CoherenceError::DuplicateInherentMethod {
                        type_def_id,
                        method_name: a_func.name,
                        impl1: a.id,
                        span1: a.span,
                        impl2: b.id,
                        span2: b.span,
                    });
                }
            }
        }
    }

    /// Extract TypeDefId from a TypeId
    fn extract_type_def_id(&self, type_id: rv_hir::TypeId) -> Option<TypeDefId> {
        let ty = &self.types[type_id];
        match ty {
            Type::Named { def, .. } => *def,
            _ => None,
        }
    }
}

/// Run coherence checking on a set of impl blocks.
///
/// This is the main entry point for coherence analysis. Call after HIR
/// lowering and before type inference / MIR lowering.
///
/// # Returns
///
/// An empty `Ok(())` if no coherence violations are found, or a list of
/// errors describing all detected conflicts.
pub fn check_coherence(
    impl_blocks: &HashMap<ImplId, ImplBlock>,
    _traits: &HashMap<TraitId, TraitDef>,
    types: &Arena<Type>,
    functions: &HashMap<rv_hir::FunctionId, rv_hir::Function>,
) -> Result<(), Vec<CoherenceError>> {
    let checker = CoherenceChecker::new(impl_blocks, types, functions);
    let errors = checker.check_all();
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}
