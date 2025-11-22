//! Monomorphization pass
//!
//! Converts generic MIR to monomorphic (concrete type) MIR by instantiating
//! generic functions for each unique type combination.

use indexmap::IndexMap;
use std::collections::HashMap;
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
/// Walks HIR expressions and collects all generic function instantiations needed
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
                        let arg_types: Vec<MirType> = args.iter().enumerate().map(|(_idx, operand)| {
                            match operand {
                                Operand::Copy(place) | Operand::Move(place) => {
                                    // Find the local type
                                    mir.locals.iter()
                                        .find(|local| local.id == place.local)
                                        .map(|local| local.ty.clone())
                                        .expect("Failed to find local type for monomorphization - internal compiler error")
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
                                .expect("Failed to find local type for monomorphization in terminator - internal compiler error")
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
///
/// Returns: (Vec<MirFunction>, HashMap mapping (template_id, types) -> instance_id)
pub fn monomorphize_functions(
    hir_ctx: &LoweringContext,
    _ty_ctx: &TyContext,
    needed_instances: &[(FunctionId, Vec<MirType>)],
    mut next_func_id: u32,
) -> (Vec<MirFunction>, HashMap<(FunctionId, Vec<MirType>), FunctionId>) {
    use std::collections::{HashMap, HashSet};
    use rv_intern::Symbol;

    let mut generated = Vec::new();
    let mut seen = HashSet::new();
    let mut instance_map = HashMap::new();

    for (func_id, type_args) in needed_instances {
        // Skip duplicates
        let key = (*func_id, type_args.clone());
        if !seen.insert(key) {
            continue;
        }

        // Look up the HIR function
        if let Some(hir_func) = hir_ctx.functions.get(func_id) {
            // Skip non-generic functions - they're already lowered and don't need monomorphization
            if hir_func.generics.is_empty() {
                continue;
            }

            // Generate a unique FunctionId for this monomorphized instance
            let instance_id = FunctionId(next_func_id);
            next_func_id += 1;

            // Record the mapping from (template_id, types) -> instance_id
            instance_map.insert((*func_id, type_args.clone()), instance_id);

            // Create type substitution map: generic param name -> concrete MirType
            let mut type_subst: HashMap<Symbol, MirType> = HashMap::new();
            for (i, generic_param) in hir_func.generics.iter().enumerate() {
                if let Some(concrete_ty) = type_args.get(i) {
                    type_subst.insert(generic_param.name, concrete_ty.clone());
                }
            }

            // ARCHITECTURE: Run type inference with concrete type substitutions
            // Create a fresh type context for this monomorphized instance
            let mut ty_ctx_clone = TyContext::new();

            // ARCHITECTURE: Store parameter types by DefId (not Symbol name)
            // For each function parameter, look up its type from type_subst
            for (param_idx, param) in hir_func.parameters.iter().enumerate() {
                // Check if this parameter's HIR type is a generic parameter
                let hir_ty = &hir_ctx.types[param.ty];
                let ty_id = match hir_ty {
                    // Generic parameter (e.g., T in fn foo<T>(x: T))
                    rv_hir::Type::Generic { name, .. } => {
                        if let Some(mir_ty) = type_subst.get(name) {
                            // Convert MirType to TyId for concrete substitution
                            match mir_ty {
                                MirType::Int => ty_ctx_clone.types.int(),
                                MirType::Float => ty_ctx_clone.types.float(),
                                MirType::Bool => ty_ctx_clone.types.bool(),
                                MirType::Unit => ty_ctx_clone.types.unit(),
                                MirType::String => ty_ctx_clone.types.string(),
                                _ => {
                                    panic!("Unsupported MirType for generic substitution: {:?}", mir_ty);
                                }
                            }
                        } else {
                            panic!("Generic parameter '{}' has no substitution in type_subst",
                                hir_ctx.interner.resolve(name));
                        }
                    }
                    // Reference to generic (e.g., &T in fn foo<T>(x: &T))
                    rv_hir::Type::Reference { inner, mutable, .. } => {
                        // Check if the inner type is a generic
                        let inner_ty = &hir_ctx.types[**inner];
                        let inner_ty_id = match inner_ty {
                            rv_hir::Type::Generic { name, .. } => {
                                if let Some(mir_ty) = type_subst.get(name) {
                                    // Convert MirType to TyId for concrete substitution
                                    match mir_ty {
                                        MirType::Int => ty_ctx_clone.types.int(),
                                        MirType::Float => ty_ctx_clone.types.float(),
                                        MirType::Bool => ty_ctx_clone.types.bool(),
                                        MirType::Unit => ty_ctx_clone.types.unit(),
                                        MirType::String => ty_ctx_clone.types.string(),
                                        MirType::Named(_sym) => {
                                            // For named types, we need the TypeDefId which we don't have here
                                            // Let type inference resolve this from the HIR type
                                            ty_ctx_clone.fresh_ty_var()
                                        }
                                        _ => {
                                            panic!("Unsupported MirType for generic substitution: {:?}", mir_ty);
                                        }
                                    }
                                } else {
                                    panic!("Generic parameter '{}' has no substitution in type_subst",
                                        hir_ctx.interner.resolve(name));
                                }
                            }
                            // Non-generic inner type - will be inferred
                            _ => ty_ctx_clone.fresh_ty_var(),
                        };

                        // Create reference type
                        ty_ctx_clone.types.alloc(rv_ty::TyKind::Ref {
                            inner: Box::new(inner_ty_id),
                            mutable: *mutable,
                        })
                    }
                    // Named type (e.g., struct name) - will be inferred
                    _ => ty_ctx_clone.fresh_ty_var(),
                };

                // Store by DefId
                let local_id = rv_hir::LocalId(param_idx as u32);
                let def_id = rv_hir::DefId::Local(local_id);
                ty_ctx_clone.set_def_type(def_id, ty_id);
            }

            // Run type inference on the generic function
            // This populates expr_types in ty_ctx_clone, which lower_function_with_subst needs
            use rv_ty::TypeInference;
            let mut type_inference = TypeInference::with_hir_context_and_tyctx(
                &hir_ctx.impl_blocks,
                &hir_ctx.functions,
                &hir_ctx.types,
                &hir_ctx.structs,
                &hir_ctx.enums,
                &hir_ctx.traits,
                &hir_ctx.interner,
                ty_ctx_clone,
            );
            type_inference.infer_function(hir_func);
            let inference_result = type_inference.finish();
            let mut ty_ctx_with_inference = inference_result.ctx;

            // Lower to MIR with type substitution and unique instance ID
            // The type_subst map handles generic parameter substitution (T -> Int, etc.)
            // The ty_ctx_with_inference has expression types from inference above
            let mir_func = rv_mir_lower::LoweringContext::lower_function_with_subst(
                hir_func,
                &mut ty_ctx_with_inference,
                &hir_ctx.structs,
                &hir_ctx.enums,
                &hir_ctx.impl_blocks,
                &hir_ctx.functions,
                &hir_ctx.types,
                &hir_ctx.traits,
                &type_subst,
                instance_id,
                &hir_ctx.interner,
            );
            generated.push(mir_func);
        }
    }

    (generated, instance_map)
}

/// Rewrite function calls in MIR to use monomorphized instance IDs
///
/// After monomorphization, we have new FunctionIds for specialized versions of generic functions.
/// This function updates all Call sites in the given MIR functions to use the new instance IDs
/// instead of the original template IDs.
pub fn rewrite_calls_to_instances(
    mir_funcs: &mut [MirFunction],
    instance_map: &HashMap<(FunctionId, Vec<MirType>), FunctionId>,
) {
    use rv_mir::{Statement, Terminator, RValue, Operand};

    for mir_func in mir_funcs {
        // Rewrite calls in basic blocks
        for bb in &mut mir_func.basic_blocks {
            // Rewrite calls in statements
            for stmt in &mut bb.statements {
                if let Statement::Assign { rvalue, .. } = stmt {
                    if let RValue::Call { func, args } = rvalue {
                        // Extract argument types to look up in instance_map
                        let arg_types: Vec<MirType> = args.iter().map(|operand| {
                            match operand {
                                Operand::Copy(place) | Operand::Move(place) => {
                                    mir_func.locals.iter()
                                        .find(|local| local.id == place.local)
                                        .map(|local| local.ty.clone())
                                        .unwrap_or(MirType::Unit)
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

                        // Look up the monomorphized instance
                        if let Some(&instance_id) = instance_map.get(&(*func, arg_types)) {
                            *func = instance_id;
                        }
                    }
                }
            }

            // Rewrite calls in terminators
            if let Terminator::Call { func, args, .. } = &mut bb.terminator {
                // Extract argument types
                let arg_types: Vec<MirType> = args.iter().map(|operand| {
                    match operand {
                        Operand::Copy(place) | Operand::Move(place) => {
                            mir_func.locals.iter()
                                .find(|local| local.id == place.local)
                                .map(|local| local.ty.clone())
                                .unwrap_or(MirType::Unit)
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

                // Look up the monomorphized instance
                if let Some(&instance_id) = instance_map.get(&(*func, arg_types)) {
                    *func = instance_id;
                }
            }
        }
    }
}
