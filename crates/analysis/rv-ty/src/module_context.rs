//! Module-level type context
//!
//! This module provides the infrastructure for module-level type inference,
//! allowing types to be inferred across function boundaries with proper
//! constraint solving.

use crate::constraint::{Constraint, Constraints};
use crate::context::TyContext;
use crate::ty::TyId;
use rustc_hash::FxHashMap;
use rv_hir::{FunctionId, GenericParam};

/// Function signature before type inference
#[derive(Debug, Clone)]
pub struct FunctionSignature {
    /// Parameter types
    pub params: Vec<TyId>,
    /// Return type
    pub return_type: TyId,
    /// Generic parameters with bounds
    pub generic_params: Vec<GenericParam>,
}

impl FunctionSignature {
    /// Create a new function signature
    #[must_use]
    pub fn new(
        params: Vec<TyId>,
        return_type: TyId,
        generic_params: Vec<GenericParam>,
    ) -> Self {
        Self {
            params,
            return_type,
            generic_params,
        }
    }

    /// Get the number of parameters
    #[must_use]
    pub fn param_count(&self) -> usize {
        self.params.len()
    }

    /// Get the number of generic parameters
    #[must_use]
    pub fn generic_param_count(&self) -> usize {
        self.generic_params.len()
    }

    /// Get a parameter type by index
    #[must_use]
    pub fn get_param(&self, index: usize) -> Option<TyId> {
        self.params.get(index).copied()
    }

    /// Get a generic parameter by index
    #[must_use]
    pub fn get_generic_param(&self, index: usize) -> Option<&GenericParam> {
        self.generic_params.get(index)
    }
}

/// Module-level type context
///
/// Manages type inference across an entire module, collecting constraints
/// from all functions and solving them together.
pub struct ModuleTypeContext {
    /// Shared type context for the entire module
    pub ctx: TyContext,

    /// All type constraints collected from the module
    pub constraints: Constraints,

    /// Generic instantiations for each function
    /// Maps function ID to a list of type arguments for each generic parameter
    pub generic_instantiations: FxHashMap<FunctionId, Vec<TyId>>,

    /// Function signatures (before full body inference)
    /// Maps function ID to its signature
    pub signatures: FxHashMap<FunctionId, FunctionSignature>,

    /// Cache of inferred types per function
    /// Maps function ID to its inferred context
    function_contexts: FxHashMap<FunctionId, TyContext>,
}

impl ModuleTypeContext {
    /// Create a new module type context
    #[must_use]
    pub fn new() -> Self {
        Self {
            ctx: TyContext::new(),
            constraints: Constraints::new(),
            generic_instantiations: FxHashMap::default(),
            signatures: FxHashMap::default(),
            function_contexts: FxHashMap::default(),
        }
    }

    /// Add a function signature
    pub fn add_function_signature(&mut self, id: FunctionId, sig: FunctionSignature) {
        self.signatures.insert(id, sig);
    }

    /// Get a function signature
    #[must_use]
    pub fn get_signature(&self, id: FunctionId) -> Option<&FunctionSignature> {
        self.signatures.get(&id)
    }

    /// Add a constraint to the module
    pub fn add_constraint(&mut self, constraint: Constraint) {
        self.constraints.all_mut().push(constraint);
    }

    /// Add multiple constraints at once
    pub fn add_constraints(&mut self, constraints: Constraints) {
        self.constraints.extend(constraints);
    }

    /// Create a fresh type variable
    pub fn fresh_var(&mut self) -> TyId {
        self.ctx.fresh_ty_var()
    }

    /// Set the generic instantiation for a function
    pub fn set_generic_instantiation(&mut self, function: FunctionId, type_args: Vec<TyId>) {
        self.generic_instantiations.insert(function, type_args);
    }

    /// Get the generic instantiation for a function
    #[must_use]
    pub fn get_generic_instantiation(&self, function: FunctionId) -> Option<&[TyId]> {
        self.generic_instantiations.get(&function).map(Vec::as_slice)
    }

    /// Add a generic type argument for a function
    pub fn add_generic_arg(&mut self, function: FunctionId, ty: TyId) {
        self.generic_instantiations
            .entry(function)
            .or_default()
            .push(ty);
    }

    /// Cache the inferred context for a function
    pub fn cache_function_context(&mut self, function: FunctionId, ctx: TyContext) {
        self.function_contexts.insert(function, ctx);
    }

    /// Get the cached context for a function
    #[must_use]
    pub fn get_function_context(&self, function: FunctionId) -> Option<&TyContext> {
        self.function_contexts.get(&function)
    }

    /// Get a mutable reference to the cached context for a function
    pub fn get_function_context_mut(&mut self, function: FunctionId) -> Option<&mut TyContext> {
        self.function_contexts.get_mut(&function)
    }

    /// Clear all cached function contexts
    pub fn clear_function_contexts(&mut self) {
        self.function_contexts.clear();
    }

    /// Get all constraints
    #[must_use]
    pub fn all_constraints(&self) -> &[Constraint] {
        self.constraints.all()
    }

    /// Get mutable access to constraints
    pub fn constraints_mut(&mut self) -> &mut Constraints {
        &mut self.constraints
    }

    /// Clear all constraints (useful after solving)
    pub fn clear_constraints(&mut self) {
        self.constraints.clear();
    }

    /// Get the number of constraints
    #[must_use]
    pub fn constraint_count(&self) -> usize {
        self.constraints.len()
    }

    /// Get all function signatures
    #[must_use]
    pub fn all_signatures(&self) -> &FxHashMap<FunctionId, FunctionSignature> {
        &self.signatures
    }

    /// Get all generic instantiations
    #[must_use]
    pub fn all_generic_instantiations(&self) -> &FxHashMap<FunctionId, Vec<TyId>> {
        &self.generic_instantiations
    }

    /// Check if a function has a cached signature
    #[must_use]
    pub fn has_signature(&self, function: FunctionId) -> bool {
        self.signatures.contains_key(&function)
    }

    /// Check if a function has generic instantiations
    #[must_use]
    pub fn has_generic_instantiation(&self, function: FunctionId) -> bool {
        self.generic_instantiations.contains_key(&function)
    }

    /// Apply all substitutions from the context to a type
    #[must_use]
    pub fn apply_subst(&self, ty: TyId) -> TyId {
        self.ctx.apply_subst(ty)
    }

    /// Merge constraints from another module context
    pub fn merge(&mut self, other: ModuleTypeContext) {
        self.constraints.extend(other.constraints);
        self.generic_instantiations
            .extend(other.generic_instantiations);
        self.signatures.extend(other.signatures);
        self.function_contexts.extend(other.function_contexts);
    }
}

impl Default for ModuleTypeContext {
    fn default() -> Self {
        Self::new()
    }
}
