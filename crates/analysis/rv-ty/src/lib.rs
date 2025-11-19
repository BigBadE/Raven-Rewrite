//! Type system and type inference
//!
//! This crate handles:
//! - Type representation
//! - Type inference with constraint generation
//! - Unification algorithm
//! - Type checking
//! - Trait bound checking
#![allow(
    clippy::min_ident_chars,
    reason = "Ty and TyId are conventional names in type system implementations"
)]

pub mod bounds;
pub mod constraint;
pub mod context;
pub mod infer;
pub mod module_context;
pub mod solver;
pub mod ty;
pub mod unify;
pub mod visitor;

pub use bounds::{BoundChecker, BoundError};
pub use constraint::{Constraint, ConstraintSource, Constraints};
pub use context::{NormalizeError, NormalizedTy, TyContext};
pub use infer::{InferenceResult, TypeError, TypeInference};
pub use module_context::{FunctionSignature, ModuleTypeContext};
pub use solver::{solve_constraints, ConstraintSolver, SolverResult};
pub use ty::{StructLayout, Ty, TyId, TyKind, VariantTy};
pub use unify::{UnificationError, Unifier};

/// Generate constraints for a function
///
/// This is the first phase of module-level type inference. It runs type
/// inference on the function body in constraint generation mode, collecting
/// all type constraints without solving them.
///
/// # Parameters
/// - `body`: The function body to infer
/// - `module_ctx`: Module context to add constraints to
///
/// # Returns
/// The collected constraints from this function
pub fn generate_constraints_for_function(
    function: &rv_hir::Function,
    module_ctx: &mut ModuleTypeContext,
    impl_blocks: &std::collections::HashMap<rv_hir::ImplId, rv_hir::ImplBlock>,
    functions: &std::collections::HashMap<rv_hir::FunctionId, rv_hir::Function>,
    hir_types: &la_arena::Arena<rv_hir::Type>,
    structs: &std::collections::HashMap<rv_hir::TypeDefId, rv_hir::StructDef>,
    enums: &std::collections::HashMap<rv_hir::TypeDefId, rv_hir::EnumDef>,
    traits: &std::collections::HashMap<rv_hir::TraitId, rv_hir::TraitDef>,
    interner: &rv_intern::Interner,
) -> Constraints {
    let mut inference = TypeInference::with_hir_context(
        impl_blocks,
        functions,
        hir_types,
        structs,
        enums,
        traits,
        interner,
    );

    // Enable constraint generation mode
    inference.enable_constraint_generation(module_ctx);

    // Run inference on the function
    inference.infer_function(function);

    // Extract the constraints
    inference.take_constraints()
}

/// Solve all constraints in a module
///
/// This is the second phase of module-level type inference. It takes all
/// constraints collected from functions and solves them together.
///
/// # Parameters
/// - `module_ctx`: Module context with collected constraints
///
/// # Returns
/// Result with generic instantiations or errors
pub fn solve_module_constraints(
    module_ctx: &mut ModuleTypeContext,
    bound_checker: Option<&BoundChecker>,
) -> Result<(), Vec<TypeError>> {
    let constraints = std::mem::take(&mut module_ctx.constraints);
    let result = solve_constraints(&mut module_ctx.ctx, constraints, bound_checker);

    match result {
        Ok(generic_instantiations) => {
            // Store the generic instantiations back in the module context
            for ((func_id, param_idx), ty) in generic_instantiations {
                module_ctx
                    .generic_instantiations
                    .entry(func_id)
                    .or_default();

                // Ensure the vector is large enough
                let instantiations = module_ctx.generic_instantiations.get_mut(&func_id).unwrap();
                if instantiations.len() <= param_idx {
                    instantiations.resize(param_idx + 1, module_ctx.ctx.types.error());
                }
                instantiations[param_idx] = ty;
            }
            Ok(())
        }
        Err(errors) => Err(errors),
    }
}
