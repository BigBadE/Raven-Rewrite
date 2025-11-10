//! Constraint solver
//!
//! This module implements the constraint solving algorithm for type inference.
//! It takes a set of constraints and produces a substitution that satisfies
//! all constraints or reports errors.

use crate::bounds::{BoundChecker, BoundError};
use crate::constraint::{Constraint, Constraints};
use crate::context::TyContext;
use crate::infer::TypeError;
use crate::ty::TyId;
use crate::unify::Unifier;
use rustc_hash::FxHashMap;
use rv_hir::FunctionId;

/// Constraint solver
pub struct ConstraintSolver<'a> {
    /// Type context (shared with module context)
    ctx: &'a mut TyContext,

    /// Constraints to solve
    constraints: Vec<Constraint>,

    /// Bound checker for trait constraints
    bound_checker: Option<&'a BoundChecker>,

    /// Errors encountered during solving
    errors: Vec<TypeError>,

    /// Generic instantiations collected during solving
    /// Maps (FunctionId, param_index) to concrete type
    generic_instantiations: FxHashMap<(FunctionId, usize), TyId>,
}

impl<'a> ConstraintSolver<'a> {
    /// Create a new constraint solver
    #[must_use]
    pub fn new(ctx: &'a mut TyContext, constraints: Constraints) -> Self {
        Self {
            ctx,
            constraints: constraints.into_iter().collect(),
            bound_checker: None,
            errors: Vec::new(),
            generic_instantiations: FxHashMap::default(),
        }
    }

    /// Create a constraint solver with bound checking support
    #[must_use]
    pub fn with_bound_checker(
        ctx: &'a mut TyContext,
        constraints: Constraints,
        bound_checker: &'a BoundChecker,
    ) -> Self {
        Self {
            ctx,
            constraints: constraints.into_iter().collect(),
            bound_checker: Some(bound_checker),
            errors: Vec::new(),
            generic_instantiations: FxHashMap::default(),
        }
    }

    /// Solve all constraints
    ///
    /// Returns all errors encountered. An empty error list means all
    /// constraints were satisfied.
    pub fn solve(&mut self) -> Result<(), Vec<TypeError>> {
        // Phase 1: Process equality constraints
        self.process_equality_constraints()?;

        // Phase 2: Instantiate generic type variables
        self.instantiate_generics()?;

        // Phase 3: Check trait bounds after variables are resolved
        self.check_trait_bounds()?;

        // Return any accumulated errors
        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(self.errors.clone())
        }
    }

    /// Process all equality constraints through unification
    fn process_equality_constraints(&mut self) -> Result<(), Vec<TypeError>> {
        let mut errors = Vec::new();

        // Extract equality constraints
        let equality_constraints: Vec<_> = self
            .constraints
            .iter()
            .filter_map(|c| match c {
                Constraint::Equality { left, right, .. } => Some((*left, *right)),
                _ => None,
            })
            .collect();

        // Process each equality constraint
        for (left, right) in equality_constraints {
            let mut unifier = Unifier::new(self.ctx);
            if let Err(error) = unifier.unify(left, right) {
                errors.push(TypeError::Unification {
                    error,
                    expr: None,
                });
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            self.errors.extend(errors.clone());
            Err(errors)
        }
    }

    /// Instantiate generic type variables with concrete types
    fn instantiate_generics(&mut self) -> Result<(), Vec<TypeError>> {
        // Extract generic instantiation constraints
        for constraint in &self.constraints {
            if let Constraint::GenericInstantiation {
                function,
                param_index,
                ty,
                ..
            } = constraint
            {
                // Apply substitutions to get the concrete type
                let concrete_ty = self.ctx.apply_subst(*ty);

                // Record the instantiation
                self.generic_instantiations
                    .insert((*function, *param_index), concrete_ty);
            }
        }

        Ok(())
    }

    /// Check trait bound constraints
    fn check_trait_bounds(&mut self) -> Result<(), Vec<TypeError>> {
        let Some(bound_checker) = self.bound_checker else {
            // No bound checker available, skip trait bound checking
            return Ok(());
        };

        let mut errors = Vec::new();

        // Extract trait bound constraints
        let trait_bounds: Vec<_> = self
            .constraints
            .iter()
            .filter_map(|c| match c {
                Constraint::TraitBound { ty, trait_id, .. } => Some((*ty, *trait_id)),
                _ => None,
            })
            .collect();

        // Check each trait bound
        for (ty, trait_id) in trait_bounds {
            // Apply substitutions to get concrete type
            let concrete_ty = self.ctx.apply_subst(ty);

            // Check if this is a struct/enum type that can implement traits
            if let Some(type_def_id) = self.extract_type_def_id(concrete_ty) {
                // Create a synthetic trait bound for checking
                let trait_bound = rv_hir::TraitBound {
                    trait_ref: trait_id,
                    args: vec![],
                };

                // Check if the bound is satisfied
                if !bound_checker.check_bound(type_def_id, &trait_bound) {
                    // Create a placeholder symbol for the error
                    // In a real implementation, we'd track which parameter this is
                    let placeholder_symbol = rv_intern::Interner::new().intern("_");
                    errors.push(TypeError::BoundError {
                        error: BoundError::UnsatisfiedBound {
                            param_name: placeholder_symbol,
                            trait_id,
                        },
                        expr: None,
                    });
                }
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            self.errors.extend(errors.clone());
            Err(errors)
        }
    }

    /// Extract TypeDefId from a TyId if it's a struct or named type
    fn extract_type_def_id(&self, ty: TyId) -> Option<rv_hir::TypeDefId> {
        let ty_kind = &self.ctx.types.get(ty).kind;
        match ty_kind {
            crate::ty::TyKind::Struct { def_id, .. } => Some(*def_id),
            crate::ty::TyKind::Named { def, .. } => Some(*def),
            crate::ty::TyKind::Enum { def_id, .. } => Some(*def_id),
            _ => None,
        }
    }

    /// Get the generic instantiations collected during solving
    #[must_use]
    pub fn generic_instantiations(&self) -> &FxHashMap<(FunctionId, usize), TyId> {
        &self.generic_instantiations
    }

    /// Get errors encountered during solving
    #[must_use]
    pub fn errors(&self) -> &[TypeError] {
        &self.errors
    }

    /// Check if solving was successful (no errors)
    #[must_use]
    pub fn is_successful(&self) -> bool {
        self.errors.is_empty()
    }
}

/// Solve constraints in a module context
///
/// This is a convenience function that creates a solver and solves all
/// constraints in the given module context.
pub fn solve_constraints(
    ctx: &mut TyContext,
    constraints: Constraints,
    bound_checker: Option<&BoundChecker>,
) -> Result<FxHashMap<(FunctionId, usize), TyId>, Vec<TypeError>> {
    let mut solver = if let Some(checker) = bound_checker {
        ConstraintSolver::with_bound_checker(ctx, constraints, checker)
    } else {
        ConstraintSolver::new(ctx, constraints)
    };

    solver.solve()?;
    Ok(solver.generic_instantiations().clone())
}

/// Result of constraint solving
pub struct SolverResult {
    /// Generic instantiations discovered during solving
    pub generic_instantiations: FxHashMap<(FunctionId, usize), TyId>,
    /// Errors encountered during solving
    pub errors: Vec<TypeError>,
}

impl SolverResult {
    /// Create a new solver result
    #[must_use]
    pub fn new(
        generic_instantiations: FxHashMap<(FunctionId, usize), TyId>,
        errors: Vec<TypeError>,
    ) -> Self {
        Self {
            generic_instantiations,
            errors,
        }
    }

    /// Check if solving was successful
    #[must_use]
    pub fn is_successful(&self) -> bool {
        self.errors.is_empty()
    }

    /// Get the generic instantiations
    #[must_use]
    pub fn instantiations(&self) -> &FxHashMap<(FunctionId, usize), TyId> {
        &self.generic_instantiations
    }

    /// Get the errors
    #[must_use]
    pub fn errors(&self) -> &[TypeError] {
        &self.errors
    }
}
