//! Type checking context

#![allow(
    clippy::min_ident_chars,
    reason = "Ty and TyId are conventional names in type system implementations"
)]

use crate::ty::{TyArena, TyId, TyKind, TyVarId};
use rustc_hash::FxHashMap;
use rv_hir::{DefId, ExprId};

/// A type that has been fully normalized (all type variables resolved).
///
/// This newtype wrapper provides compile-time guarantees that:
/// - All type variables have been resolved via substitution
/// - The type is ready for code generation
/// - No `apply_subst` calls are needed
///
/// Use `TyContext::normalize()` to create normalized types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NormalizedTy(TyId);

impl NormalizedTy {
    /// Get the underlying TyId (only for internal use after normalization)
    pub fn ty_id(self) -> TyId {
        self.0
    }

    /// Create a NormalizedTy without checking normalization.
    ///
    /// Caller must ensure the TyId contains no unresolved type variables.
    /// This is a logical invariant, not a memory safety invariant.
    pub(crate) fn new_unchecked(ty_id: TyId) -> Self {
        Self(ty_id)
    }

    /// Wrap a TyId that is known to be a child of a normalized type.
    ///
    /// Since the parent NormalizedTy was produced by normalize(), all TyIds
    /// contained within its structure are also normalized. This method allows
    /// accessing those nested TyIds as NormalizedTy for recursive operations.
    pub fn wrap_child(ty_id: TyId) -> Self {
        Self::new_unchecked(ty_id)
    }

    /// Assume a TyId is already normalized (for use after type inference completes).
    ///
    /// This should only be used when you know type inference has successfully completed
    /// and all type variables have been resolved. Typically used during MIR lowering.
    pub fn assume_normalized(ty_id: TyId) -> Self {
        Self::new_unchecked(ty_id)
    }
}

/// Error during type normalization
#[derive(Debug, Clone)]
pub enum NormalizeError {
    /// Encountered an unresolved type variable
    UnresolvedVariable {
        /// The type variable ID that wasn't resolved
        var_id: TyVarId,
        /// The type ID containing the unresolved variable
        ty_id: TyId,
    },
}

/// Type checking context
/// Type context for type inference and checking
///
/// ARCHITECTURE: This is the single source of truth for all types in the compiler.
/// - `def_types`: Maps DefId (Function, Local, Type) to their inferred types
/// - `expr_types`: Maps expression IDs to their inferred types
/// - `subst`: Type variable solutions from unification
///
/// NO Symbol-based lookups - everything uses structured IDs (DefId, ExprId)
#[derive(Debug, Clone, PartialEq)]
pub struct TyContext {
    /// Type arena
    pub types: TyArena,
    /// Next type variable ID
    next_var_id: u32,
    /// Type variable substitutions (solutions from unification)
    pub subst: FxHashMap<TyVarId, TyId>,
    /// Expression types
    pub expr_types: FxHashMap<ExprId, TyId>,
    /// Definition types (DefId::Local for parameters, DefId::Function, etc.)
    pub def_types: FxHashMap<DefId, TyId>,
    /// Receiver mutability for method calls (ExprId → is_mutable)
    pub receiver_mutability: FxHashMap<ExprId, bool>,
}

impl TyContext {
    /// Create a new type context
    pub fn new() -> Self {
        Self {
            types: TyArena::new(),
            next_var_id: 0,
            subst: FxHashMap::default(),
            expr_types: FxHashMap::default(),
            def_types: FxHashMap::default(),
            receiver_mutability: FxHashMap::default(),
        }
    }

    /// Allocate a fresh type variable
    pub fn fresh_var(&mut self) -> TyVarId {
        let id = TyVarId(self.next_var_id);
        self.next_var_id += 1;
        id
    }

    /// Create a fresh type variable and allocate it
    pub fn fresh_ty_var(&mut self) -> TyId {
        let var_id = self.fresh_var();
        self.types.var(var_id)
    }

    /// Create a fresh integer inference variable (for unsuffixed integer literals).
    /// Can unify with any concrete integer type; defaults to i32 when unconstrained.
    pub fn fresh_int_var(&mut self) -> TyId {
        let var_id = self.fresh_var();
        self.types.alloc(TyKind::IntVar { id: var_id })
    }

    /// Create a fresh float inference variable (for unsuffixed float literals).
    /// Can unify with any concrete float type; defaults to f64 when unconstrained.
    pub fn fresh_float_var(&mut self) -> TyId {
        let var_id = self.fresh_var();
        self.types.alloc(TyKind::FloatVar { id: var_id })
    }

    /// Follow type variable substitution chains (shallow - doesn't recurse into structural types).
    ///
    /// This is used during unification to follow chains of type variable substitutions.
    /// Unlike `normalize()`, this does NOT recurse into structural types like Struct, Function, etc.
    /// It only follows Var -> Var -> ... -> concrete type chains.
    ///
    /// This is safe to use during unification when the substitution map is still being built.
    pub fn follow_var(&self, ty_id: TyId) -> TyId {
        let ty = self.types.get(ty_id);
        match &ty.kind {
            TyKind::Var { id } | TyKind::IntVar { id } | TyKind::FloatVar { id } => self
                .subst
                .get(id)
                .map_or(ty_id, |subst_ty| self.follow_var(*subst_ty)),
            _ => ty_id,
        }
    }

    /// Normalize a type by deeply resolving all type variables.
    ///
    /// This recursively traverses the type structure and replaces all type variables
    /// with their substitutions. If any unresolved type variable is encountered,
    /// returns an error.
    ///
    /// # Errors
    /// Returns `NormalizeError::UnresolvedVariable` if a type variable has no substitution.
    #[allow(
        unused_variables,
        unused_assignments,
        reason = "Pattern matching extracts only used fields"
    )]
    pub fn normalize(&mut self, ty_id: TyId) -> Result<NormalizedTy, NormalizeError> {
        let ty = self.types.get(ty_id);

        match &ty.kind.clone() {
            TyKind::Var { id } => {
                // Follow the substitution chain
                if let Some(&subst_ty) = self.subst.get(id) {
                    // Recursively normalize the substitution
                    let normalized = self.normalize(subst_ty)?;
                    // Path compression: update substitution to point directly to normalized type
                    self.subst.insert(*id, normalized.ty_id());
                    Ok(normalized)
                } else {
                    // Unresolved type variable - this is an error
                    Err(NormalizeError::UnresolvedVariable { var_id: *id, ty_id })
                }
            }

            TyKind::IntVar { id } => {
                // Follow the substitution chain
                if let Some(&subst_ty) = self.subst.get(id) {
                    let normalized = self.normalize(subst_ty)?;
                    self.subst.insert(*id, normalized.ty_id());
                    Ok(normalized)
                } else {
                    // Unconstrained integer inference variable defaults to i32
                    let default_ty = self.types.int();
                    self.subst.insert(*id, default_ty);
                    Ok(NormalizedTy::new_unchecked(default_ty))
                }
            }

            TyKind::FloatVar { id } => {
                // Follow the substitution chain
                if let Some(&subst_ty) = self.subst.get(id) {
                    let normalized = self.normalize(subst_ty)?;
                    self.subst.insert(*id, normalized.ty_id());
                    Ok(normalized)
                } else {
                    // Unconstrained float inference variable defaults to f64
                    let default_ty = self.types.float();
                    self.subst.insert(*id, default_ty);
                    Ok(NormalizedTy::new_unchecked(default_ty))
                }
            }

            // Structural types: recursively normalize all contained types
            TyKind::Struct { def_id, fields } => {
                let normalized_fields: Result<Vec<_>, _> = fields
                    .iter()
                    .map(|(name, field_ty)| {
                        self.normalize(*field_ty).map(|norm| (*name, norm.ty_id()))
                    })
                    .collect();

                let new_ty_id = self.types.alloc(TyKind::Struct {
                    def_id: *def_id,
                    fields: normalized_fields?,
                });
                Ok(NormalizedTy::new_unchecked(new_ty_id))
            }

            TyKind::Function { params, ret } => {
                let normalized_params: Result<Vec<_>, _> = params
                    .iter()
                    .map(|p| self.normalize(*p).map(|n| n.ty_id()))
                    .collect();
                let normalized_ret = self.normalize(**ret)?;

                let new_ty_id = self.types.alloc(TyKind::Function {
                    params: normalized_params?,
                    ret: Box::new(normalized_ret.ty_id()),
                });
                Ok(NormalizedTy::new_unchecked(new_ty_id))
            }

            TyKind::Tuple { elements } => {
                let normalized_elements: Result<Vec<_>, _> = elements
                    .iter()
                    .map(|e| self.normalize(*e).map(|n| n.ty_id()))
                    .collect();

                let new_ty_id = self.types.alloc(TyKind::Tuple {
                    elements: normalized_elements?,
                });
                Ok(NormalizedTy::new_unchecked(new_ty_id))
            }

            TyKind::Ref {
                mutable,
                inner,
                lifetime,
            } => {
                let normalized_inner = self.normalize(**inner)?;

                let new_ty_id = self.types.alloc(TyKind::Ref {
                    mutable: *mutable,
                    inner: Box::new(normalized_inner.ty_id()),
                    lifetime: *lifetime,
                });
                Ok(NormalizedTy::new_unchecked(new_ty_id))
            }

            TyKind::Array { element, size } => {
                let normalized_element = self.normalize(**element)?;

                let new_ty_id = self.types.alloc(TyKind::Array {
                    element: Box::new(normalized_element.ty_id()),
                    size: *size,
                });
                Ok(NormalizedTy::new_unchecked(new_ty_id))
            }

            TyKind::Slice { element } => {
                let normalized_element = self.normalize(**element)?;

                let new_ty_id = self.types.alloc(TyKind::Slice {
                    element: Box::new(normalized_element.ty_id()),
                });
                Ok(NormalizedTy::new_unchecked(new_ty_id))
            }

            TyKind::Enum { def_id, variants } => {
                use crate::ty::VariantTy;

                let normalized_variants: Result<Vec<_>, _> = variants
                    .iter()
                    .map(|(name, variant_ty)| {
                        let norm_variant = match variant_ty {
                            VariantTy::Unit => Ok(VariantTy::Unit),
                            VariantTy::Tuple(types) => {
                                let norm_types: Result<Vec<_>, _> = types
                                    .iter()
                                    .map(|t| self.normalize(*t).map(|n| n.ty_id()))
                                    .collect();
                                norm_types.map(VariantTy::Tuple)
                            }
                            VariantTy::Struct(fields) => {
                                let norm_fields: Result<Vec<_>, _> = fields
                                    .iter()
                                    .map(|(fname, fty)| {
                                        self.normalize(*fty).map(|n| (*fname, n.ty_id()))
                                    })
                                    .collect();
                                norm_fields.map(VariantTy::Struct)
                            }
                        };
                        norm_variant.map(|v| (*name, v))
                    })
                    .collect();

                let new_ty_id = self.types.alloc(TyKind::Enum {
                    def_id: *def_id,
                    variants: normalized_variants?,
                });
                Ok(NormalizedTy::new_unchecked(new_ty_id))
            }

            TyKind::Pointer { mutable, inner } => {
                let normalized_inner = self.normalize(**inner)?;

                let new_ty_id = self.types.alloc(TyKind::Pointer {
                    mutable: *mutable,
                    inner: Box::new(normalized_inner.ty_id()),
                });
                Ok(NormalizedTy::new_unchecked(new_ty_id))
            }

            // Named types - may contain type variables in args that need normalization
            TyKind::Named { name, def, args } => {
                if args.is_empty() {
                    // No args to normalize, return as-is
                    Ok(NormalizedTy::new_unchecked(ty_id))
                } else {
                    // Normalize all generic args
                    let normalized_args: Result<Vec<_>, _> = args
                        .iter()
                        .map(|arg| self.normalize(*arg).map(|n| n.ty_id()))
                        .collect();

                    let new_ty_id = self.types.alloc(TyKind::Named {
                        name: *name,
                        def: *def,
                        args: normalized_args?,
                    });
                    Ok(NormalizedTy::new_unchecked(new_ty_id))
                }
            }

            // Leaf types that contain no nested type variables
            TyKind::Int(..)
            | TyKind::Float(..)
            | TyKind::Char
            | TyKind::Bool
            | TyKind::String
            | TyKind::Unit
            | TyKind::Never
            | TyKind::Param { .. }
            | TyKind::DynTrait { .. }
            | TyKind::ImplTrait { .. } => Ok(NormalizedTy::new_unchecked(ty_id)),

            // Function pointers and Box types (no type variable substitution needed for these)
            TyKind::FunctionPointer { params, ret, abi } => {
                let normalized_params: Vec<TyId> = params
                    .iter()
                    .map(|p| self.normalize(*p).map(|n| n.ty_id()))
                    .collect::<Result<_, _>>()?;
                let normalized_ret = self.normalize(**ret)?.ty_id();
                let new_kind = TyKind::FunctionPointer {
                    params: normalized_params,
                    ret: Box::new(normalized_ret),
                    abi: abi.clone(),
                };
                let new_id = self.types.alloc(new_kind);
                Ok(NormalizedTy::new_unchecked(new_id))
            }
            TyKind::Box { inner } => {
                let normalized_inner = self.normalize(**inner)?.ty_id();
                let new_kind = TyKind::Box {
                    inner: Box::new(normalized_inner),
                };
                let new_id = self.types.alloc(new_kind);
                Ok(NormalizedTy::new_unchecked(new_id))
            }

            TyKind::Projection {
                base,
                assoc_type,
                trait_ref,
            } => {
                // First normalize the base type
                let normalized_base = self.normalize(**base)?;

                // After normalization, the base should be a concrete type
                // We try to resolve the projection by looking up impl blocks
                // This is done during type inference resolution, not here
                // For now, preserve the projection with normalized base
                let new_kind = TyKind::Projection {
                    base: Box::new(normalized_base.ty_id()),
                    assoc_type: *assoc_type,
                    trait_ref: *trait_ref,
                };
                let new_id = self.types.alloc(new_kind);
                Ok(NormalizedTy::new_unchecked(new_id))
            }
        }
    }

    /// Normalize an optional type
    pub fn normalize_opt(
        &mut self,
        ty_id: Option<TyId>,
    ) -> Result<Option<NormalizedTy>, NormalizeError> {
        ty_id.map(|id| self.normalize(id)).transpose()
    }

    /// Record the type of an expression
    pub fn set_expr_type(&mut self, expr: ExprId, ty: TyId) {
        self.expr_types.insert(expr, ty);
    }

    /// Get the type of an expression
    pub fn get_expr_type(&self, expr: ExprId) -> Option<TyId> {
        self.expr_types.get(&expr).copied()
    }

    /// Record the type of a definition
    pub fn set_def_type(&mut self, def: DefId, ty: TyId) {
        self.def_types.insert(def, ty);
    }

    /// Get the type of a definition
    pub fn get_def_type(&self, def: DefId) -> Option<TyId> {
        self.def_types.get(&def).copied()
    }

    /// Clear all local variable types from def_types
    /// This should be called at the start of each function inference to avoid
    /// LocalId collisions between different functions
    pub fn clear_local_types(&mut self) {
        self.def_types
            .retain(|def_id, _| !matches!(def_id, DefId::Local { .. }));
    }

    /// Clear expression type mappings.
    /// Must be called before each function's MIR lowering when multiple functions
    /// share the same TyContext, because ExprIds are local to each function body
    /// and will collide between different functions.
    pub fn clear_expr_types(&mut self) {
        self.expr_types.clear();
    }
}

impl Default for TyContext {
    fn default() -> Self {
        Self::new()
    }
}
