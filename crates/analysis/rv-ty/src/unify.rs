//! Type unification
#![allow(
    clippy::min_ident_chars,
    reason = "Ty and TyId are conventional names in type system implementations"
)]

use crate::context::TyContext;
use crate::ty::{TyId, TyKind, TyVarId};
use thiserror::Error;

/// Unification error
#[derive(Error, Debug, Clone)]
pub enum UnificationError {
    /// Types cannot be unified
    #[error("type mismatch: cannot unify {expected:?} with {found:?}")]
    Mismatch {
        /// Expected type
        expected: TyId,
        /// Found type
        found: TyId,
    },

    /// Occurs check failed (infinite type)
    #[error("occurs check failed: {var} occurs in {ty:?}")]
    OccursCheck {
        /// Type variable
        var: TyVarId,
        /// Type containing the variable
        ty: TyId,
    },
}

/// Type unifier
pub struct Unifier<'ctx> {
    ctx: &'ctx mut TyContext,
}

impl<'ctx> Unifier<'ctx> {
    /// Create a new unifier
    pub fn new(ctx: &'ctx mut TyContext) -> Self {
        Self { ctx }
    }

    /// Unify two types
    ///
    /// # Errors
    ///
    /// Returns `UnificationError` if types cannot be unified
    pub fn unify(&mut self, left: TyId, right: TyId) -> Result<(), UnificationError> {
        // Apply current substitutions
        let left = self.ctx.apply_subst(left);
        let right = self.ctx.apply_subst(right);

        // If same type, already unified
        if left == right {
            return Ok(());
        }

        let left_ty = self.ctx.types.get(left).clone();
        let right_ty = self.ctx.types.get(right).clone();

        match (&left_ty.kind, &right_ty.kind) {
            // Type variable on left
            (TyKind::Var { id: var }, _) => self.unify_var(*var, right),

            // Type variable on right
            (_, TyKind::Var { id: var }) => self.unify_var(*var, left),

            // Function types
            (
                TyKind::Function {
                    params: left_params,
                    ret: left_ret,
                },
                TyKind::Function {
                    params: right_params,
                    ret: right_ret,
                },
            ) => {
                if left_params.len() != right_params.len() {
                    return Err(UnificationError::Mismatch {
                        expected: left,
                        found: right,
                    });
                }

                // Unify parameter types
                for (left_param, right_param) in left_params.iter().zip(right_params.iter()) {
                    self.unify(*left_param, *right_param)?;
                }

                // Unify return types
                self.unify(**left_ret, **right_ret)
            }

            // Tuple types
            (TyKind::Tuple { elements: left_elems }, TyKind::Tuple { elements: right_elems }) => {
                if left_elems.len() != right_elems.len() {
                    return Err(UnificationError::Mismatch {
                        expected: left,
                        found: right,
                    });
                }

                for (left_elem, right_elem) in left_elems.iter().zip(right_elems.iter()) {
                    self.unify(*left_elem, *right_elem)?;
                }

                Ok(())
            }

            // Reference types
            (
                TyKind::Ref {
                    mutable: left_mut,
                    inner: left_inner,
                },
                TyKind::Ref {
                    mutable: right_mut,
                    inner: right_inner,
                },
            ) => {
                if left_mut != right_mut {
                    return Err(UnificationError::Mismatch {
                        expected: left,
                        found: right,
                    });
                }

                self.unify(**left_inner, **right_inner)
            }

            // Primitive types and named types - must match exactly
            (left_kind, right_kind) if left_kind == right_kind => Ok(()),

            // Error type unifies with anything
            (TyKind::Error, _) | (_, TyKind::Error) => Ok(()),

            // Otherwise, mismatch
            _ => Err(UnificationError::Mismatch {
                expected: left,
                found: right,
            }),
        }
    }

    /// Unify a type variable with a type
    ///
    /// # Errors
    ///
    /// Returns `UnificationError::OccursCheck` if variable occurs in type
    fn unify_var(&mut self, var: TyVarId, ty: TyId) -> Result<(), UnificationError> {
        // Occurs check: ensure var doesn't occur in ty
        if self.occurs_in(var, ty) {
            return Err(UnificationError::OccursCheck { var, ty });
        }

        // Add substitution
        self.ctx.subst.insert(var, ty);
        Ok(())
    }

    /// Check if a type variable occurs in a type (for occurs check)
    fn occurs_in(&self, var: TyVarId, ty: TyId) -> bool {
        let ty = self.ctx.apply_subst(ty);
        let ty_kind = &self.ctx.types.get(ty).kind;

        match ty_kind {
            TyKind::Var { id } => *id == var,
            TyKind::Function { params, ret } => {
                params.iter().any(|param| self.occurs_in(var, *param))
                    || self.occurs_in(var, **ret)
            }
            TyKind::Tuple { elements } => elements.iter().any(|elem| self.occurs_in(var, *elem)),
            TyKind::Ref { inner, .. } => self.occurs_in(var, **inner),
            TyKind::Named { args, .. } => args.iter().any(|arg| self.occurs_in(var, *arg)),
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unify_same_type() {
        let mut ctx = TyContext::new();
        let int_ty = ctx.types.int();

        let mut unifier = Unifier::new(&mut ctx);
        assert!(unifier.unify(int_ty, int_ty).is_ok());
    }

    #[test]
    fn test_unify_type_var() {
        let mut ctx = TyContext::new();
        let var = ctx.fresh_var();
        let var_ty = ctx.types.var(var);
        let int_ty = ctx.types.int();

        let mut unifier = Unifier::new(&mut ctx);
        assert!(unifier.unify(var_ty, int_ty).is_ok());
        assert_eq!(ctx.subst.get(&var), Some(&int_ty));
    }

    #[test]
    fn test_unify_mismatch() {
        let mut ctx = TyContext::new();
        let int_ty = ctx.types.int();
        let bool_ty = ctx.types.bool();

        let mut unifier = Unifier::new(&mut ctx);
        assert!(unifier.unify(int_ty, bool_ty).is_err());
    }
}
