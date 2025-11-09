//! Monomorphization pass
//!
//! Converts generic MIR to monomorphic (concrete type) MIR by instantiating
//! generic functions for each unique type combination.

use indexmap::IndexMap;
use rv_hir::FunctionId;
use rv_hir_lower::LoweringContext;
use rv_mir::{MirFunction, MirType};
use rv_ty::TyContext;

/// Monomorphization context
pub struct MonoContext {
    /// Map from (FunctionId, type arguments) to monomorphized MirFunction
    instances: IndexMap<(FunctionId, Vec<MirType>), MirFunction>,

    /// Type context for type operations
    #[allow(dead_code, reason = "Will be used for future generic support")]
    ty_ctx: TyContext,
}

impl MonoContext {
    /// Create a new monomorphization context
    #[must_use]
    pub fn new(ty_ctx: TyContext) -> Self {
        Self {
            instances: IndexMap::new(),
            ty_ctx,
        }
    }

    /// Register a monomorphized instance
    ///
    /// Stores a MIR function with its type arguments for later retrieval
    pub fn register_instance(
        &mut self,
        function_id: FunctionId,
        type_args: Vec<MirType>,
        mir_function: MirFunction,
    ) {
        let key = (function_id, type_args);
        self.instances.insert(key, mir_function);
    }

    /// Get a monomorphized instance if it exists
    #[must_use]
    pub fn get_instance(
        &self,
        function_id: FunctionId,
        type_args: &[MirType],
    ) -> Option<&MirFunction> {
        let key = (function_id, type_args.to_vec());
        self.instances.get(&key)
    }

    /// Check if an instance exists
    #[must_use]
    pub fn has_instance(&self, function_id: FunctionId, type_args: &[MirType]) -> bool {
        let key = (function_id, type_args.to_vec());
        self.instances.contains_key(&key)
    }

    /// Get all monomorphized instances
    #[must_use]
    pub fn instances(&self) -> &IndexMap<(FunctionId, Vec<MirType>), MirFunction> {
        &self.instances
    }
}

/// Monomorphization collector
///
/// Walks MIR and collects all generic function instantiations needed
pub struct MonoCollector {
    /// Functions that need to be instantiated with specific types
    needed_instances: Vec<(FunctionId, Vec<MirType>)>,
}

impl MonoCollector {
    /// Create a new collector
    #[must_use]
    pub fn new() -> Self {
        Self {
            needed_instances: Vec::new(),
        }
    }

    /// Collect generic instantiations from a MIR function
    pub fn collect_from_mir(&mut self, mir: &MirFunction) {
        use rv_mir::{Operand, RValue, Statement, Terminator};

        // Walk all basic blocks
        for bb in &mir.basic_blocks {
            // Check statements for function calls in RValue::Call
            for stmt in &bb.statements {
                if let Statement::Assign { rvalue, .. } = stmt {
                    if let RValue::Call { func, args, .. } = rvalue {
                        // Extract argument types from operands
                        let arg_types: Vec<MirType> = args.iter().map(|operand| {
                            match operand {
                                Operand::Copy(place) | Operand::Move(place) => {
                                    // Find the local type
                                    mir.locals.iter()
                                        .find(|local| local.id == place.local)
                                        .map(|local| local.ty.clone())
                                        .unwrap_or(MirType::Unknown)
                                }
                                Operand::Constant(constant) => {
                                    // Infer type from constant
                                    use rv_hir::LiteralKind;
                                    match &constant.kind {
                                        LiteralKind::Integer(_) => MirType::Int,
                                        LiteralKind::Float(_) => MirType::Float,
                                        LiteralKind::Bool(_) => MirType::Bool,
                                        LiteralKind::String(_) => MirType::String,
                                        LiteralKind::Unit => MirType::Unit,
                                    }
                                }
                            }
                        }).collect();

                        self.needed_instances.push((*func, arg_types));
                    }
                }
            }

            // Check terminator for Call
            if let Terminator::Call { func, args, .. } = &bb.terminator {
                // Extract argument types
                let arg_types: Vec<MirType> = args.iter().map(|operand| {
                    match operand {
                        Operand::Copy(place) | Operand::Move(place) => {
                            mir.locals.iter()
                                .find(|local| local.id == place.local)
                                .map(|local| local.ty.clone())
                                .unwrap_or(MirType::Unknown)
                        }
                        Operand::Constant(constant) => {
                            use rv_hir::LiteralKind;
                            match &constant.kind {
                                LiteralKind::Integer(_) => MirType::Int,
                                LiteralKind::Float(_) => MirType::Float,
                                LiteralKind::Bool(_) => MirType::Bool,
                                LiteralKind::String(_) => MirType::String,
                                LiteralKind::Unit => MirType::Unit,
                            }
                        }
                    }
                }).collect();

                self.needed_instances.push((*func, arg_types));
            }
        }
    }

    /// Get all needed instantiations
    #[must_use]
    pub fn needed_instances(&self) -> &[(FunctionId, Vec<MirType>)] {
        &self.needed_instances
    }
}

impl Default for MonoCollector {
    fn default() -> Self {
        Self::new()
    }
}

/// Monomorphize all needed function instances
///
/// Takes HIR lowering context and ty context, and generates specialized MIR functions
/// for each (FunctionId, type_args) pair collected
pub fn monomorphize_functions(
    hir_ctx: &LoweringContext,
    ty_ctx: &TyContext,
    needed_instances: &[(FunctionId, Vec<MirType>)],
) -> Vec<MirFunction> {
    use std::collections::HashSet;
    let mut generated = Vec::new();
    let mut seen = HashSet::new();

    for (func_id, type_args) in needed_instances {
        // Skip duplicates
        let key = (*func_id, type_args.clone());
        if !seen.insert(key) {
            continue;
        }

        // Look up the HIR function
        if let Some(hir_func) = hir_ctx.functions.get(func_id) {
            // Lower to MIR (type substitution happens during lowering via ty_ctx)
            let mir_func = rv_mir::lower::LoweringContext::lower_function(
                hir_func,
                ty_ctx,
                &hir_ctx.structs,
                &hir_ctx.impl_blocks,
                &hir_ctx.functions,
                &hir_ctx.types,
                &hir_ctx.traits,
            );
            generated.push(mir_func);
        }
    }

    generated
}
