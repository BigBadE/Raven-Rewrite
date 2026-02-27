//! Variance calculation for generic type parameters
//!
//! Variance describes how subtyping relates through type constructors:
//! - **Covariant**: If `T <: U`, then `F<T> <: F<U>`
//! - **Contravariant**: If `T <: U`, then `F<U> <: F<T>` (reversed)
//! - **Invariant**: `F<T>` and `F<U>` are only subtypes if `T == U`
//! - **Bivariant**: `F<T>` and `F<U>` are always subtypes (rare, usually phantom data)
//!
//! # Examples
//!
//! - `Vec<T>` is covariant in `T`: `Vec<Cat>` <: `Vec<Animal>` if `Cat <: Animal`
//! - `&T` is covariant in `T`: `&Cat` <: `&Animal`
//! - `&mut T` is invariant in `T`: cannot treat `&mut Cat` as `&mut Animal`
//! - `fn(T)` is contravariant in `T`: `fn(Animal)` <: `fn(Cat)`

use rv_hir::TypeDefId;
use std::collections::HashMap;

use crate::ty::{TyId, TyKind};
use crate::context::TyContext;

/// Variance of a type parameter
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Variance {
    /// Covariant: subtyping flows in the same direction
    /// `T <: U` implies `F<T> <: F<U>`
    Covariant,
    /// Contravariant: subtyping flows in the opposite direction
    /// `T <: U` implies `F<U> <: F<T>`
    Contravariant,
    /// Invariant: types must be equal
    /// `F<T> <: F<U>` only if `T == U`
    Invariant,
    /// Bivariant: any relationship is valid (phantom type parameter)
    /// This is rare and usually indicates the parameter isn't actually used
    Bivariant,
}

impl Variance {
    /// Combine two variances (when passing through nested type constructors)
    ///
    /// When a type `F<G<T>>` appears, we need to combine the variance of `T` in `G`
    /// with the variance of `G<T>` in `F`.
    #[must_use]
    pub fn combine(self, inner: Self) -> Self {
        match (self, inner) {
            // Bivariant absorbs everything
            (Self::Bivariant, _) | (_, Self::Bivariant) => Self::Bivariant,

            // Invariant from either position is invariant
            (Self::Invariant, _) | (_, Self::Invariant) => Self::Invariant,

            // Covariant * Covariant = Covariant
            (Self::Covariant, Self::Covariant) => Self::Covariant,

            // Covariant * Contravariant = Contravariant
            (Self::Covariant, Self::Contravariant) => Self::Contravariant,

            // Contravariant * Covariant = Contravariant
            (Self::Contravariant, Self::Covariant) => Self::Contravariant,

            // Contravariant * Contravariant = Covariant
            (Self::Contravariant, Self::Contravariant) => Self::Covariant,
        }
    }

    /// Meet of two variances (when a type parameter appears in multiple positions)
    ///
    /// If a type parameter `T` appears in both covariant and contravariant positions,
    /// the result is invariant.
    #[must_use]
    pub fn meet(self, other: Self) -> Self {
        match (self, other) {
            // Same variance stays the same
            (Self::Covariant, Self::Covariant) => Self::Covariant,
            (Self::Contravariant, Self::Contravariant) => Self::Contravariant,
            (Self::Bivariant, Self::Bivariant) => Self::Bivariant,
            (Self::Invariant, Self::Invariant) => Self::Invariant,

            // Bivariant is the identity for meet
            (Self::Bivariant, other) | (other, Self::Bivariant) => other,

            // Anything meeting invariant is invariant
            (Self::Invariant, _) | (_, Self::Invariant) => Self::Invariant,

            // Covariant meet Contravariant = Invariant
            (Self::Covariant, Self::Contravariant)
            | (Self::Contravariant, Self::Covariant) => Self::Invariant,
        }
    }

    /// Flip variance (for contravariant positions like function parameters)
    #[must_use]
    pub fn flip(self) -> Self {
        match self {
            Self::Covariant => Self::Contravariant,
            Self::Contravariant => Self::Covariant,
            Self::Invariant => Self::Invariant,
            Self::Bivariant => Self::Bivariant,
        }
    }
}

/// Variance information for a type definition
#[derive(Debug, Clone)]
pub struct TypeVariances {
    /// Variance for each generic parameter by index
    pub params: Vec<Variance>,
}

impl TypeVariances {
    /// Create a new variance info with all parameters bivariant (unused)
    #[must_use]
    pub fn new(param_count: usize) -> Self {
        Self {
            params: vec![Variance::Bivariant; param_count],
        }
    }

    /// Set the variance for a parameter (via meet operation)
    pub fn add_variance(&mut self, param_idx: usize, variance: Variance) {
        if param_idx < self.params.len() {
            self.params[param_idx] = self.params[param_idx].meet(variance);
        }
    }
}

/// Variance calculator for type definitions
pub struct VarianceCalculator<'ctx> {
    /// Type context for looking up types
    ctx: &'ctx TyContext,
    /// Computed variances for each type definition
    variances: HashMap<TypeDefId, TypeVariances>,
    /// Types currently being computed (for cycle detection)
    in_progress: Vec<TypeDefId>,
}

impl<'ctx> VarianceCalculator<'ctx> {
    /// Create a new variance calculator
    #[must_use]
    pub fn new(ctx: &'ctx TyContext) -> Self {
        Self {
            ctx,
            variances: HashMap::new(),
            in_progress: Vec::new(),
        }
    }

    /// Get the computed variances (consuming the calculator)
    #[must_use]
    pub fn into_variances(self) -> HashMap<TypeDefId, TypeVariances> {
        self.variances
    }

    /// Calculate variances for a struct type
    pub fn calculate_struct_variance(
        &mut self,
        def_id: TypeDefId,
        param_count: usize,
        field_types: impl Iterator<Item = TyId>,
    ) {
        if self.variances.contains_key(&def_id) {
            return; // Already computed
        }

        // Check for cycles
        if self.in_progress.contains(&def_id) {
            // Recursive type: assume invariant for all parameters
            self.variances.insert(
                def_id,
                TypeVariances {
                    params: vec![Variance::Invariant; param_count],
                },
            );
            return;
        }

        self.in_progress.push(def_id);

        let mut variances = TypeVariances::new(param_count);

        // Struct fields are in covariant position
        for field_ty in field_types {
            self.collect_variances(field_ty, Variance::Covariant, &mut variances);
        }

        self.in_progress.pop();
        self.variances.insert(def_id, variances);
    }

    /// Calculate variances for an enum type
    pub fn calculate_enum_variance(
        &mut self,
        def_id: TypeDefId,
        param_count: usize,
        variant_field_types: impl Iterator<Item = TyId>,
    ) {
        if self.variances.contains_key(&def_id) {
            return; // Already computed
        }

        // Check for cycles
        if self.in_progress.contains(&def_id) {
            self.variances.insert(
                def_id,
                TypeVariances {
                    params: vec![Variance::Invariant; param_count],
                },
            );
            return;
        }

        self.in_progress.push(def_id);

        let mut variances = TypeVariances::new(param_count);

        // Enum variant fields are in covariant position
        for field_ty in variant_field_types {
            self.collect_variances(field_ty, Variance::Covariant, &mut variances);
        }

        self.in_progress.pop();
        self.variances.insert(def_id, variances);
    }

    /// Collect variance information from a type, tracking current variance context
    fn collect_variances(
        &mut self,
        ty_id: TyId,
        current_variance: Variance,
        variances: &mut TypeVariances,
    ) {
        let ty = self.ctx.types.get(ty_id);

        match &ty.kind {
            // Type parameter: record variance at this position
            TyKind::Param { index, .. } => {
                variances.add_variance(*index as usize, current_variance);
            }

            // Reference types
            TyKind::Ref {
                mutable,
                inner,
                ..
            } => {
                if *mutable {
                    // &mut T is invariant in T (can't treat &mut Cat as &mut Animal)
                    self.collect_variances(**inner, Variance::Invariant, variances);
                } else {
                    // &T is covariant in T
                    self.collect_variances(
                        **inner,
                        current_variance.combine(Variance::Covariant),
                        variances,
                    );
                }
            }

            // Pointer types
            TyKind::Pointer { mutable, inner } => {
                if *mutable {
                    // *mut T is invariant in T
                    self.collect_variances(**inner, Variance::Invariant, variances);
                } else {
                    // *const T is covariant in T
                    self.collect_variances(
                        **inner,
                        current_variance.combine(Variance::Covariant),
                        variances,
                    );
                }
            }

            // Function types
            TyKind::Function { params, ret } => {
                // Return type is covariant
                self.collect_variances(
                    **ret,
                    current_variance.combine(Variance::Covariant),
                    variances,
                );
                // Parameters are contravariant
                for param in params {
                    self.collect_variances(
                        *param,
                        current_variance.combine(Variance::Contravariant),
                        variances,
                    );
                }
            }

            // Function pointer types
            TyKind::FunctionPointer { params, ret, .. } => {
                // Return type is covariant
                self.collect_variances(
                    **ret,
                    current_variance.combine(Variance::Covariant),
                    variances,
                );
                // Parameters are contravariant
                for param in params {
                    self.collect_variances(
                        *param,
                        current_variance.combine(Variance::Contravariant),
                        variances,
                    );
                }
            }

            // Box<T> is covariant in T
            TyKind::Box { inner } => {
                self.collect_variances(
                    **inner,
                    current_variance.combine(Variance::Covariant),
                    variances,
                );
            }

            // Tuple elements are covariant
            TyKind::Tuple { elements } => {
                for elem in elements {
                    self.collect_variances(
                        *elem,
                        current_variance.combine(Variance::Covariant),
                        variances,
                    );
                }
            }

            // Array and slice elements are covariant
            TyKind::Array { element, .. } | TyKind::Slice { element } => {
                self.collect_variances(
                    **element,
                    current_variance.combine(Variance::Covariant),
                    variances,
                );
            }

            // Struct fields are covariant
            TyKind::Struct { fields, .. } => {
                for (_, field_ty) in fields {
                    self.collect_variances(
                        *field_ty,
                        current_variance.combine(Variance::Covariant),
                        variances,
                    );
                }
            }

            // Named types with generic arguments
            TyKind::Named { args, .. } => {
                // For now, treat all generic arguments as covariant
                // A more complete implementation would look up the type's variance info
                for arg in args {
                    self.collect_variances(
                        *arg,
                        current_variance.combine(Variance::Covariant),
                        variances,
                    );
                }
            }

            // Enum variants
            TyKind::Enum { variants, .. } => {
                use crate::ty::VariantTy;
                for (_, variant_ty) in variants {
                    match variant_ty {
                        VariantTy::Unit => {}
                        VariantTy::Tuple(types) => {
                            for ty in types {
                                self.collect_variances(
                                    *ty,
                                    current_variance.combine(Variance::Covariant),
                                    variances,
                                );
                            }
                        }
                        VariantTy::Struct(fields) => {
                            for (_, field_ty) in fields {
                                self.collect_variances(
                                    *field_ty,
                                    current_variance.combine(Variance::Covariant),
                                    variances,
                                );
                            }
                        }
                    }
                }
            }

            // Projection types - treat as covariant for now
            TyKind::Projection { base, .. } => {
                self.collect_variances(
                    **base,
                    current_variance.combine(Variance::Covariant),
                    variances,
                );
            }

            // Leaf types don't affect variance
            TyKind::Int(..)
            | TyKind::Float(..)
            | TyKind::Char
            | TyKind::Bool
            | TyKind::String
            | TyKind::Unit
            | TyKind::Never
            | TyKind::DynTrait { .. }
            | TyKind::ImplTrait { .. }
            | TyKind::Var { .. }
            | TyKind::IntVar { .. }
            | TyKind::FloatVar { .. } => {}
        }
    }
}

/// Check if a type is a subtype of another, considering variance
///
/// Returns `true` if `sub_ty` is a subtype of `super_ty`.
/// This is a simplified check that handles common cases.
pub fn is_subtype(ctx: &TyContext, sub_ty: TyId, super_ty: TyId) -> bool {
    let sub = ctx.types.get(sub_ty);
    let sup = ctx.types.get(super_ty);

    match (&sub.kind, &sup.kind) {
        // Same type
        _ if sub_ty == super_ty => true,

        // Never is a subtype of everything
        (TyKind::Never, _) => true,

        // Reference covariance: &T <: &U if T <: U (for immutable refs)
        (
            TyKind::Ref {
                mutable: false,
                inner: sub_inner,
                ..
            },
            TyKind::Ref {
                mutable: false,
                inner: sup_inner,
                ..
            },
        ) => is_subtype(ctx, **sub_inner, **sup_inner),

        // Mutable reference invariance: &mut T <: &mut U only if T == U
        (
            TyKind::Ref {
                mutable: true,
                inner: sub_inner,
                ..
            },
            TyKind::Ref {
                mutable: true,
                inner: sup_inner,
                ..
            },
        ) => sub_inner == sup_inner,

        // Mutable ref is subtype of immutable ref with same inner type
        (
            TyKind::Ref {
                mutable: true,
                inner: sub_inner,
                ..
            },
            TyKind::Ref {
                mutable: false,
                inner: sup_inner,
                ..
            },
        ) => is_subtype(ctx, **sub_inner, **sup_inner),

        // Box is covariant
        (TyKind::Box { inner: sub_inner }, TyKind::Box { inner: sup_inner }) => {
            is_subtype(ctx, **sub_inner, **sup_inner)
        }

        // Function subtyping: contravariant in parameters, covariant in return
        (
            TyKind::Function {
                params: sub_params,
                ret: sub_ret,
            },
            TyKind::Function {
                params: sup_params,
                ret: sup_ret,
            },
        ) => {
            if sub_params.len() != sup_params.len() {
                return false;
            }

            // Parameters are contravariant
            for (sub_param, sup_param) in sub_params.iter().zip(sup_params.iter()) {
                if !is_subtype(ctx, *sup_param, *sub_param) {
                    return false;
                }
            }

            // Return type is covariant
            is_subtype(ctx, **sub_ret, **sup_ret)
        }

        // Default to strict equality for other types
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_variance_combine() {
        // Covariant * Covariant = Covariant
        assert_eq!(
            Variance::Covariant.combine(Variance::Covariant),
            Variance::Covariant
        );

        // Covariant * Contravariant = Contravariant
        assert_eq!(
            Variance::Covariant.combine(Variance::Contravariant),
            Variance::Contravariant
        );

        // Contravariant * Contravariant = Covariant
        assert_eq!(
            Variance::Contravariant.combine(Variance::Contravariant),
            Variance::Covariant
        );

        // Invariant absorbs everything
        assert_eq!(
            Variance::Invariant.combine(Variance::Covariant),
            Variance::Invariant
        );
    }

    #[test]
    fn test_variance_meet() {
        // Same variance
        assert_eq!(
            Variance::Covariant.meet(Variance::Covariant),
            Variance::Covariant
        );

        // Covariant meet Contravariant = Invariant
        assert_eq!(
            Variance::Covariant.meet(Variance::Contravariant),
            Variance::Invariant
        );

        // Bivariant is identity
        assert_eq!(
            Variance::Bivariant.meet(Variance::Covariant),
            Variance::Covariant
        );
    }
}
