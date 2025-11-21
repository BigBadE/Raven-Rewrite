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
    /// Only use when you can guarantee the type is already normalized.
    ///
    /// # Safety
    /// Caller must ensure the TyId contains no unresolved type variables.
    #[allow(unsafe_code, reason = "Intentionally unsafe for performance")]
    pub(crate) unsafe fn new_unchecked(ty_id: TyId) -> Self {
        Self(ty_id)
    }

    /// Safely wrap a TyId that is known to be a child of this normalized type.
    ///
    /// Since this NormalizedTy was produced by normalize(), all TyIds contained
    /// within its structure are also normalized. This method allows accessing
    /// those nested TyIds as NormalizedTy for recursive operations.
    ///
    /// # Safety
    /// Only use this for TyIds that are directly contained within the structure
    /// of this normalized type (e.g., struct fields, function parameters).
    #[allow(unsafe_code, reason = "Safety documented in comment")]
    pub fn wrap_child(ty_id: TyId) -> Self {
        // If the parent is normalized, all children are too
        // SAFETY: Child types of normalized types are also normalized
        unsafe { Self::new_unchecked(ty_id) }
    }

    /// Assume a TyId is already normalized (for use after type inference completes).
    ///
    /// This should only be used when you know type inference has successfully completed
    /// and all type variables have been resolved. Typically used during MIR lowering.
    ///
    /// # Panics
    /// In debug builds, this will panic if the type contains unresolved variables.
    /// In release builds, behavior is undefined if the type is not normalized.
    #[allow(unsafe_code, reason = "Safety documented - assumes type inference completed")]
    pub fn assume_normalized(ty_id: TyId) -> Self {
        // In debug builds, we could add a check here
        // For now, just wrap it
        // SAFETY: Caller guarantees type inference has completed
        unsafe { Self::new_unchecked(ty_id) }
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
        ty_id: TyId
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
            TyKind::Var { id } => self
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
    #[allow(unused_variables, unused_assignments, unsafe_code, reason = "Pattern matching extracts only used fields, unsafe blocks create normalized types")]
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
                    Err(NormalizeError::UnresolvedVariable {
                        var_id: *id,
                        ty_id
                    })
                }
            }

            // Structural types: recursively normalize all contained types
            TyKind::Struct { def_id, fields } => {
                let normalized_fields: Result<Vec<_>, _> = fields.iter()
                    .map(|(name, field_ty)| {
                        self.normalize(*field_ty)
                            .map(|norm| (*name, norm.ty_id()))
                    })
                    .collect();

                let new_ty_id = self.types.alloc(TyKind::Struct {
                    def_id: *def_id,
                    fields: normalized_fields?,
                });
                // SAFETY: All fields were normalized, so the struct is normalized
                Ok(unsafe { NormalizedTy::new_unchecked(new_ty_id) })
            }

            TyKind::Function { params, ret } => {
                let normalized_params: Result<Vec<_>, _> = params.iter()
                    .map(|p| self.normalize(*p).map(|n| n.ty_id()))
                    .collect();
                let normalized_ret = self.normalize(**ret)?;

                let new_ty_id = self.types.alloc(TyKind::Function {
                    params: normalized_params?,
                    ret: Box::new(normalized_ret.ty_id()),
                });
                // SAFETY: All params and ret were normalized, so function is normalized
                Ok(unsafe { NormalizedTy::new_unchecked(new_ty_id) })
            }

            TyKind::Tuple { elements } => {
                let normalized_elements: Result<Vec<_>, _> = elements.iter()
                    .map(|e| self.normalize(*e).map(|n| n.ty_id()))
                    .collect();

                let new_ty_id = self.types.alloc(TyKind::Tuple {
                    elements: normalized_elements?,
                });
                // SAFETY: All elements were normalized, so tuple is normalized
                Ok(unsafe { NormalizedTy::new_unchecked(new_ty_id) })
            }

            TyKind::Ref { mutable, inner } => {
                let normalized_inner = self.normalize(**inner)?;

                let new_ty_id = self.types.alloc(TyKind::Ref {
                    mutable: *mutable,
                    inner: Box::new(normalized_inner.ty_id()),
                });
                // SAFETY: Inner type was normalized, so reference is normalized
                Ok(unsafe { NormalizedTy::new_unchecked(new_ty_id) })
            }

            TyKind::Array { element, size } => {
                let normalized_element = self.normalize(**element)?;

                let new_ty_id = self.types.alloc(TyKind::Array {
                    element: Box::new(normalized_element.ty_id()),
                    size: *size,
                });
                // SAFETY: Element type was normalized, so array is normalized
                Ok(unsafe { NormalizedTy::new_unchecked(new_ty_id) })
            }

            TyKind::Slice { element } => {
                let normalized_element = self.normalize(**element)?;

                let new_ty_id = self.types.alloc(TyKind::Slice {
                    element: Box::new(normalized_element.ty_id()),
                });
                // SAFETY: Element type was normalized, so slice is normalized
                Ok(unsafe { NormalizedTy::new_unchecked(new_ty_id) })
            }

            TyKind::Enum { def_id, variants } => {
                use crate::ty::VariantTy;

                let normalized_variants: Result<Vec<_>, _> = variants.iter()
                    .map(|(name, variant_ty)| {
                        let norm_variant = match variant_ty {
                            VariantTy::Unit => Ok(VariantTy::Unit),
                            VariantTy::Tuple(types) => {
                                let norm_types: Result<Vec<_>, _> = types.iter()
                                    .map(|t| self.normalize(*t).map(|n| n.ty_id()))
                                    .collect();
                                norm_types.map(VariantTy::Tuple)
                            }
                            VariantTy::Struct(fields) => {
                                let norm_fields: Result<Vec<_>, _> = fields.iter()
                                    .map(|(fname, fty)| {
                                        self.normalize(*fty)
                                            .map(|n| (*fname, n.ty_id()))
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
                // SAFETY: All variant types were normalized, so enum is normalized
                Ok(unsafe { NormalizedTy::new_unchecked(new_ty_id) })
            }

            // Leaf types that contain no nested type variables
            TyKind::Int | TyKind::Float | TyKind::Bool | TyKind::String |
            TyKind::Unit | TyKind::Never | TyKind::Error |
            TyKind::Named { .. } | TyKind::Param { .. } => {
                // These types don't contain nested TyIds, so they're already normalized
                // SAFETY: Leaf types and parameters have no nested types to normalize
                Ok(unsafe { NormalizedTy::new_unchecked(ty_id) })
            }
        }
    }

    /// Normalize an optional type
    pub fn normalize_opt(&mut self, ty_id: Option<TyId>) -> Result<Option<NormalizedTy>, NormalizeError> {
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
}

impl Default for TyContext {
    fn default() -> Self {
        Self::new()
    }
}
