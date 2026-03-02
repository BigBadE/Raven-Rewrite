//! Monomorphization pass
//!
//! Converts generic MIR to monomorphic (concrete type) MIR by instantiating
//! generic functions for each unique type combination.

use indexmap::IndexMap;
use rv_hir::FunctionId;
use rv_hir_lower::LoweringContext;
use rv_mir::{MirFunction, MirType};
use rv_ty::{TyContext, TyId, TyKind};
use std::collections::HashMap;

/// Helper function to recursively convert MirType to TyId
///
/// Takes HIR structs and enums maps to properly resolve Struct/Enum types
/// to their full TyKind representations with TypeDefId and field names.
fn convert_mir_type_to_ty_id(
    mir_ty: &MirType,
    ty_ctx: &mut TyContext,
    structs: &HashMap<rv_hir::TypeDefId, rv_hir::StructDef>,
    enums: &HashMap<rv_hir::TypeDefId, rv_hir::EnumDef>,
) -> TyId {
    match mir_ty {
        MirType::Int(w, s) => ty_ctx.types.int_typed(*w, *s),
        MirType::Float(w) => ty_ctx.types.float_typed(*w),
        MirType::Char => ty_ctx.types.char(),
        MirType::Bool => ty_ctx.types.bool(),
        MirType::Unit => ty_ctx.types.unit(),
        MirType::String => ty_ctx.types.string(),
        MirType::Ref {
            inner,
            mutable,
            lifetime,
        } => {
            // Recursively convert the inner type
            let inner_ty_id = convert_mir_type_to_ty_id(inner, ty_ctx, structs, enums);
            // Create a reference type
            ty_ctx.types.alloc(TyKind::Ref {
                inner: Box::new(inner_ty_id),
                mutable: *mutable,
                lifetime: *lifetime,
            })
        }
        MirType::Named(sym) => {
            // Named types should have been resolved to Struct/Enum during MIR lowering.
            // If one reaches monomorphization, it indicates a compiler bug.
            panic!(
                "ICE: Unresolved named type {:?} reached monomorphization. \
                 MIR lowering should have resolved this to a concrete Struct or Enum type.",
                sym
            );
        }
        MirType::Function { params, ret } => {
            let param_tys: Vec<TyId> = params
                .iter()
                .map(|p| convert_mir_type_to_ty_id(p, ty_ctx, structs, enums))
                .collect();
            let ret_ty = convert_mir_type_to_ty_id(ret, ty_ctx, structs, enums);
            ty_ctx.types.alloc(TyKind::Function {
                params: param_tys,
                ret: Box::new(ret_ty),
            })
        }
        MirType::Struct { name, fields } => {
            // Look up the struct definition by name to get TypeDefId and field names
            let struct_def = structs
                .iter()
                .find(|(_, s)| s.name == *name)
                .map(|(id, s)| (*id, s));

            if let Some((def_id, s_def)) = struct_def {
                // Build field types: use HIR field names paired with converted MIR field types
                let ty_fields: Vec<(rv_intern::Symbol, TyId)> = s_def
                    .fields
                    .iter()
                    .zip(fields.iter())
                    .map(|(hir_field, mir_field_ty)| {
                        let field_ty =
                            convert_mir_type_to_ty_id(mir_field_ty, ty_ctx, structs, enums);
                        (hir_field.name, field_ty)
                    })
                    .collect();
                ty_ctx.types.alloc(TyKind::Struct {
                    def_id,
                    fields: ty_fields,
                })
            } else {
                panic!(
                    "ICE: Struct '{:?}' not found in HIR during monomorphization. \
                     All struct types should be defined before monomorphization runs.",
                    name
                );
            }
        }
        MirType::Tuple(elements) => {
            let elem_tys: Vec<TyId> = elements
                .iter()
                .map(|e| convert_mir_type_to_ty_id(e, ty_ctx, structs, enums))
                .collect();
            ty_ctx.types.alloc(TyKind::Tuple { elements: elem_tys })
        }
        MirType::Array { element, size } => {
            let elem_ty = convert_mir_type_to_ty_id(element, ty_ctx, structs, enums);
            ty_ctx.types.alloc(TyKind::Array {
                element: Box::new(elem_ty),
                size: *size,
            })
        }
        MirType::Slice { element } => {
            let elem_ty = convert_mir_type_to_ty_id(element, ty_ctx, structs, enums);
            ty_ctx.types.alloc(TyKind::Slice {
                element: Box::new(elem_ty),
            })
        }
        MirType::Enum { name, variants } => {
            // Look up the enum definition by name to get TypeDefId
            let enum_def = enums
                .iter()
                .find(|(_, e)| e.name == *name)
                .map(|(id, _)| *id);

            if let Some(def_id) = enum_def {
                let ty_variants: Vec<(rv_intern::Symbol, rv_ty::VariantTy)> = variants
                    .iter()
                    .map(|v| {
                        let variant_ty = if v.fields.is_empty() {
                            rv_ty::VariantTy::Unit
                        } else {
                            let field_tys: Vec<TyId> = v
                                .fields
                                .iter()
                                .map(|f| convert_mir_type_to_ty_id(f, ty_ctx, structs, enums))
                                .collect();
                            rv_ty::VariantTy::Tuple(field_tys)
                        };
                        (v.name, variant_ty)
                    })
                    .collect();
                ty_ctx.types.alloc(TyKind::Enum {
                    def_id,
                    variants: ty_variants,
                })
            } else {
                panic!(
                    "ICE: Enum '{:?}' not found in HIR during monomorphization. \
                     All enum types should be defined before monomorphization runs.",
                    name
                );
            }
        }
        MirType::Pointer { inner, mutable } => {
            let inner_ty = convert_mir_type_to_ty_id(inner, ty_ctx, structs, enums);
            ty_ctx.types.alloc(TyKind::Pointer {
                inner: Box::new(inner_ty),
                mutable: *mutable,
            })
        }
        MirType::Never => ty_ctx.types.alloc(TyKind::Never),
        MirType::DynTrait {
            principal,
            trait_id,
        } => ty_ctx.types.alloc(TyKind::DynTrait {
            principal: trait_id.unwrap_or(rv_hir::TraitId(u32::MAX)),
            principal_name: *principal,
        }),
        MirType::ImplTrait { principal } => ty_ctx.types.alloc(TyKind::ImplTrait {
            principal: *principal,
        }),
        MirType::FunctionPointer { params, ret, abi } => {
            let param_tys: Vec<TyId> = params
                .iter()
                .map(|p| convert_mir_type_to_ty_id(p, ty_ctx, structs, enums))
                .collect();
            let ret_ty = convert_mir_type_to_ty_id(ret, ty_ctx, structs, enums);
            ty_ctx.types.alloc(TyKind::FunctionPointer {
                params: param_tys,
                ret: Box::new(ret_ty),
                abi: abi.clone(),
            })
        }
        MirType::Box { inner } => {
            let inner_ty = convert_mir_type_to_ty_id(inner, ty_ctx, structs, enums);
            ty_ctx.types.alloc(TyKind::Box {
                inner: Box::new(inner_ty),
            })
        }
    }
}

/// Monomorphization context
pub struct MonoContext {
    /// Map from (FunctionId, type arguments) to monomorphized MirFunction
    instances: IndexMap<(FunctionId, Vec<MirType>), MirFunction>,
}

impl MonoContext {
    /// Create a new monomorphization context
    #[must_use]
    pub fn new() -> Self {
        Self {
            instances: IndexMap::new(),
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

    /// Collect generic instantiations from a MIR function.
    ///
    /// Takes HIR context to look up function signatures for type matching.
    pub fn collect_from_mir(
        &mut self,
        mir: &MirFunction,
        hir_functions: &HashMap<FunctionId, rv_hir::Function>,
        hir_types: &la_arena::Arena<rv_hir::Type>,
    ) {
        use rv_mir::{RValue, Statement, Terminator};

        for bb in &mir.basic_blocks {
            for stmt in &bb.statements {
                if let Statement::Assign { rvalue, .. } = stmt {
                    if let RValue::Call { func, args, .. } = rvalue {
                        let arg_types = extract_arg_types(args, &mir.locals);
                        let type_args = infer_generic_args_for_call(
                            *func,
                            &arg_types,
                            hir_functions,
                            hir_types,
                        );
                        self.needed_instances.push((*func, type_args));
                    }
                }
            }

            if let Terminator::Call { func, args, .. } = &bb.terminator {
                let arg_types = extract_arg_types(args, &mir.locals);
                let type_args =
                    infer_generic_args_for_call(*func, &arg_types, hir_functions, hir_types);
                self.needed_instances.push((*func, type_args));
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
/// Takes HIR lowering context and generates specialized MIR functions
/// for each (FunctionId, type_args) pair collected
///
/// Returns: (Vec<MirFunction>, HashMap mapping (template_id, types) -> instance_id)
pub fn monomorphize_functions(
    hir_ctx: &LoweringContext,
    needed_instances: &[(FunctionId, Vec<MirType>)],
    mut next_func_id: u32,
    bound_checker: Option<&rv_ty::BoundChecker>,
) -> (
    Vec<MirFunction>,
    HashMap<(FunctionId, Vec<MirType>), FunctionId>,
) {
    use rv_intern::Symbol;
    use std::collections::{HashMap, HashSet};

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

            // Skip core library functions - they cannot be lowered to MIR
            // Core library functions have incomplete type information and are only
            // used for trait definitions and type signatures.
            if hir_func.is_core_library {
                continue;
            }

            // Generate a unique FunctionId for this monomorphized instance
            let instance_id = FunctionId(next_func_id);
            next_func_id += 1;

            // Record the mapping from (template_id, types) -> instance_id
            instance_map.insert((*func_id, type_args.clone()), instance_id);

            // Create type substitution map: generic param name -> concrete MirType
            let mut type_subst: HashMap<Symbol, MirType> = HashMap::new();
            for (_i, generic_param) in hir_func.generics.iter().enumerate() {
                if let Some(concrete_ty) = type_args.get(_i) {
                    type_subst.insert(generic_param.name, concrete_ty.clone());
                }
            }

            // Check trait bounds on generic parameters
            if let Some(bound_checker) = &bound_checker {
                for generic_param in &hir_func.generics {
                    if generic_param.bounds.is_empty() {
                        continue;
                    }
                    if let Some(concrete_ty) = type_subst.get(&generic_param.name) {
                        // Extract TypeDefId from the concrete MirType
                        let type_def_id = match concrete_ty {
                            MirType::Struct { name, .. } => hir_ctx
                                .structs
                                .iter()
                                .find(|(_, s)| s.name == *name)
                                .map(|(id, _)| *id),
                            MirType::Enum { name, .. } => hir_ctx
                                .enums
                                .iter()
                                .find(|(_, e)| e.name == *name)
                                .map(|(id, _)| *id),
                            _ => None,
                        };
                        if let Some(type_def_id) = type_def_id {
                            let errors =
                                bound_checker.check_generic_bounds(type_def_id, generic_param);
                            if !errors.is_empty() {
                                let param_name = hir_ctx.interner.resolve(&generic_param.name);
                                for error in &errors {
                                    match error {
                                        rv_ty::BoundError::UnsatisfiedBound {
                                            trait_id, ..
                                        } => {
                                            let trait_name = hir_ctx
                                                .traits
                                                .get(trait_id)
                                                .map(|t| {
                                                    hir_ctx.interner.resolve(&t.name).to_string()
                                                })
                                                .unwrap_or_else(|| format!("{:?}", trait_id));
                                            panic!(
                                                "Bound check error: type '{}' does not satisfy \
                                                 trait bound '{}' required by generic parameter '{}'",
                                                hir_ctx.interner.resolve(&match concrete_ty {
                                                    MirType::Struct { name, .. }
                                                    | MirType::Enum { name, .. } => *name,
                                                    _ => generic_param.name,
                                                }),
                                                trait_name,
                                                param_name
                                            );
                                        }
                                        rv_ty::BoundError::UnsizedType { .. } => {
                                            panic!(
                                                "Bound check error: type substituted for generic \
                                                 parameter '{}' is not Sized. Use `?Sized` bound \
                                                 to allow unsized types.",
                                                param_name
                                            );
                                        }
                                        _ => {
                                            panic!(
                                                "Bound check error: {:?} for generic parameter '{}'",
                                                error, param_name
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
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
                            convert_mir_type_to_ty_id(
                                &mir_ty,
                                &mut ty_ctx_clone,
                                &hir_ctx.structs,
                                &hir_ctx.enums,
                            )
                        } else {
                            // Generic parameter has no substitution - let type inference handle it
                            ty_ctx_clone.fresh_ty_var()
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
                                    convert_mir_type_to_ty_id(
                                        &mir_ty,
                                        &mut ty_ctx_clone,
                                        &hir_ctx.structs,
                                        &hir_ctx.enums,
                                    )
                                } else {
                                    // Generic parameter has no substitution - let type inference handle it
                                    ty_ctx_clone.fresh_ty_var()
                                }
                            }
                            // Non-generic inner type - will be inferred
                            _ => ty_ctx_clone.fresh_ty_var(),
                        };

                        // Create reference type
                        ty_ctx_clone.types.alloc(rv_ty::TyKind::Ref {
                            inner: Box::new(inner_ty_id),
                            mutable: *mutable,
                            lifetime: None,
                        })
                    }
                    // Named type (e.g., struct name) - will be inferred
                    _ => ty_ctx_clone.fresh_ty_var(),
                };

                // Store by DefId
                let local_id = rv_hir::LocalId(param_idx as u32);
                let def_id = rv_hir::DefId::Local {
                    func: *func_id,
                    local: local_id,
                };
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
                &hir_ctx.interner,
                ty_ctx_clone,
            );
            type_inference.infer_function(hir_func);
            let inference_result = type_inference.finish();
            let mut ty_ctx_with_inference = inference_result.ctx;

            // Evaluate const and static items
            let const_values =
                rv_const_eval::evaluate_const_items(&hir_ctx.const_items, &hir_ctx.interner);
            let static_values = rv_const_eval::evaluate_static_items(
                &hir_ctx.static_items,
                &hir_ctx.const_items,
                &const_values,
                &hir_ctx.interner,
            );

            // Lower to MIR with type substitution and unique instance ID
            // The type_subst map handles generic parameter substitution (T -> Int, etc.)
            // The ty_ctx_with_inference has expression types from inference above
            let mir_result = rv_mir_lower::LoweringContext::lower_function_with_subst(
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
                &hir_ctx.lang_items,
                &const_values,
                &static_values,
            );
            generated.push(mir_result.function);
        }
    }

    (generated, instance_map)
}

/// Infer generic type arguments by matching call argument types against function parameter types.
///
/// This is the canonical way to compute the instance map key for a given call site.
/// Both `MonoCollector::collect_from_mir` and `rewrite_calls_to_instances` must use
/// this same logic so keys are consistent.
fn infer_generic_args_for_call(
    func_id: FunctionId,
    arg_types: &[MirType],
    hir_functions: &HashMap<FunctionId, rv_hir::Function>,
    hir_types: &la_arena::Arena<rv_hir::Type>,
) -> Vec<MirType> {
    let Some(hir_func) = hir_functions.get(&func_id) else {
        return vec![];
    };

    if hir_func.generics.is_empty() {
        return vec![];
    }

    let mut substitutions: HashMap<rv_intern::Symbol, MirType> = HashMap::new();

    for (arg_idx, arg_type) in arg_types.iter().enumerate() {
        if let Some(param) = hir_func.parameters.get(arg_idx) {
            let param_hir_type = &hir_types[param.ty];
            match_type_for_generics(arg_type, param_hir_type, hir_types, &mut substitutions);
        }
    }

    hir_func
        .generics
        .iter()
        .map(|gen_param| {
            substitutions
                .get(&gen_param.name)
                .cloned()
                .unwrap_or(MirType::Unit)
        })
        .collect()
}

/// Match an argument type against a parameter type pattern, collecting generic substitutions.
fn match_type_for_generics(
    arg_type: &MirType,
    param_type: &rv_hir::Type,
    hir_types: &la_arena::Arena<rv_hir::Type>,
    substitutions: &mut HashMap<rv_intern::Symbol, MirType>,
) {
    match param_type {
        rv_hir::Type::Generic { name, .. } => {
            substitutions.insert(*name, arg_type.clone());
        }
        rv_hir::Type::Reference { inner, .. } => {
            if let MirType::Ref {
                inner: arg_inner, ..
            } = arg_type
            {
                let param_inner_type = &hir_types[**inner];
                match_type_for_generics(arg_inner, param_inner_type, hir_types, substitutions);
            }
        }
        _ => {}
    }
}

/// Extract argument types from a list of MIR operands using the function's locals.
fn extract_arg_types(args: &[rv_mir::Operand], locals: &[rv_mir::Local]) -> Vec<MirType> {
    args.iter()
        .map(|operand| match operand {
            rv_mir::Operand::Copy(place) | rv_mir::Operand::Move(place) => locals
                .iter()
                .find(|local| local.id == place.local)
                .map(|local| local.ty.clone())
                .unwrap_or(MirType::Unit),
            rv_mir::Operand::Constant(constant) => {
                use rv_hir::LiteralKind;
                match &constant.kind {
                    LiteralKind::Integer(_, Some((w, s))) => MirType::Int(*w, *s),
                    LiteralKind::Integer(_, None) => {
                        MirType::Int(rv_hir::IntWidth::I32, rv_hir::Signedness::Signed)
                    }
                    LiteralKind::Float(_, Some(w)) => MirType::Float(*w),
                    LiteralKind::Float(_, None) => MirType::Float(rv_hir::FloatWidth::F64),
                    LiteralKind::Char(_) => MirType::Char,
                    LiteralKind::Bool(_) => MirType::Bool,
                    LiteralKind::String(_) => MirType::String,
                    LiteralKind::Unit => MirType::Unit,
                }
            }
        })
        .collect()
}

/// Rewrite function calls in MIR to use monomorphized instance IDs.
///
/// After monomorphization, we have new FunctionIds for specialized versions of generic functions.
/// This function updates all Call sites in the given MIR functions to use the new instance IDs
/// instead of the original template IDs.
///
/// Requires HIR context to correctly infer generic type arguments from call argument types,
/// ensuring the lookup key matches the key format used during monomorphization.
pub fn rewrite_calls_to_instances(
    mir_funcs: &mut [MirFunction],
    instance_map: &HashMap<(FunctionId, Vec<MirType>), FunctionId>,
    hir_functions: &HashMap<FunctionId, rv_hir::Function>,
    hir_types: &la_arena::Arena<rv_hir::Type>,
) {
    use rv_mir::{RValue, Statement, Terminator};

    for mir_func in mir_funcs {
        for bb in &mut mir_func.basic_blocks {
            // Rewrite calls in statements
            for stmt in &mut bb.statements {
                if let Statement::Assign { rvalue, .. } = stmt {
                    if let RValue::Call { func, args } = rvalue {
                        let arg_types = extract_arg_types(args, &mir_func.locals);
                        let type_args = infer_generic_args_for_call(
                            *func,
                            &arg_types,
                            hir_functions,
                            hir_types,
                        );
                        if let Some(&instance_id) = instance_map.get(&(*func, type_args)) {
                            *func = instance_id;
                        }
                    }
                }
            }

            // Rewrite calls in terminators
            if let Terminator::Call { func, args, .. } = &mut bb.terminator {
                let arg_types = extract_arg_types(args, &mir_func.locals);
                let type_args =
                    infer_generic_args_for_call(*func, &arg_types, hir_functions, hir_types);
                if let Some(&instance_id) = instance_map.get(&(*func, type_args)) {
                    *func = instance_id;
                }
            }
        }
    }
}
