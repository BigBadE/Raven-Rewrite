//! Type coercion
//!
//! Implements automatic type conversions allowed by Rust:
//! - Reference weakening: `&mut T` → `&T`
//! - Deref coercions: `&String` → `&str` (via `Deref` trait)
//! - Unsizing coercions: `&[T; N]` → `&[T]`, `&T` → `&dyn Trait`
//! - Pointer coercions: `&T` → `*const T`, `&mut T` → `*mut T`
//! - Never coercion: `!` → any type

use crate::context::TyContext;
use crate::ty::{TyId, TyKind};

/// Result of a coercion attempt
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CoercionResult {
    /// No coercion needed
    NoCoercion,
    /// Successful coercion to target type
    Coerced(TyId),
    /// Coercion not possible
    Failed,
}

/// Type coercion engine
#[derive(Debug)]
pub struct Coercer<'a> {
    /// Type context
    ctx: &'a mut TyContext,
}

impl<'a> Coercer<'a> {
    /// Create a new coercer
    pub fn new(ctx: &'a mut TyContext) -> Self {
        Self { ctx }
    }

    /// Try to coerce `from` to `to`
    ///
    /// Returns:
    /// - `NoCoercion` if types are already equal
    /// - `Coerced(ty)` if coercion is possible
    /// - `Failed` if coercion is not allowed
    pub fn coerce(&mut self, from: TyId, to: TyId) -> CoercionResult {
        // If types are equal, no coercion needed
        if from == to {
            return CoercionResult::NoCoercion;
        }

        // Clone the type kinds to avoid borrowing issues
        let from_kind = self.ctx.types.get(from).kind.clone();
        let to_kind = self.ctx.types.get(to).kind.clone();

        // Never type coerces to anything
        if matches!(from_kind, TyKind::Never) {
            return CoercionResult::Coerced(to);
        }

        // Try each coercion in order
        if let Some(result) = self.try_reference_weakening(from, to, &from_kind, &to_kind) {
            return result;
        }

        if let Some(result) = self.try_deref_coercion(from, to, &from_kind, &to_kind) {
            return result;
        }

        if let Some(result) = self.try_unsizing_coercion(from, to, &from_kind, &to_kind) {
            return result;
        }

        if let Some(result) = self.try_pointer_coercion(from, to, &from_kind, &to_kind) {
            return result;
        }

        CoercionResult::Failed
    }

    /// Try reference weakening: `&mut T` → `&T`
    fn try_reference_weakening(
        &mut self,
        _from: TyId,
        to: TyId,
        from_kind: &TyKind,
        to_kind: &TyKind,
    ) -> Option<CoercionResult> {
        if let (
            TyKind::Ref {
                mutable: true,
                inner: from_inner,
                lifetime: from_lifetime,
            },
            TyKind::Ref {
                mutable: false,
                inner: to_inner,
                lifetime: to_lifetime,
            },
        ) = (from_kind, to_kind)
        {
            // Check that inner types match
            if from_inner == to_inner {
                // Lifetimes must be compatible (for now, just check equality or allow None)
                if from_lifetime == to_lifetime || to_lifetime.is_none() {
                    return Some(CoercionResult::Coerced(to));
                }
            }
        }
        None
    }

    /// Try Deref coercion: `&T` → `&U` where `T: Deref<Target=U>`
    ///
    /// This requires checking if the inner type implements Deref trait.
    /// For now, we handle the built-in cases:
    /// - `&String` → `&str` (once we have proper string types)
    /// - Custom types via trait resolution (deferred)
    fn try_deref_coercion(
        &mut self,
        _from: TyId,
        _to: TyId,
        from_kind: &TyKind,
        to_kind: &TyKind,
    ) -> Option<CoercionResult> {
        // Extract reference types
        let (from_mut, _from_inner, _from_lifetime) = match from_kind {
            TyKind::Ref {
                mutable,
                inner,
                lifetime,
            } => (*mutable, **inner, *lifetime),
            _ => return None,
        };

        let (to_mut, _to_inner, _to_lifetime) = match to_kind {
            TyKind::Ref {
                mutable,
                inner,
                lifetime,
            } => (*mutable, **inner, *lifetime),
            _ => return None,
        };

        // For Deref coercion, the mutability must be compatible:
        // - &T → &U is ok
        // - &mut T → &U is ok (via reference weakening + deref)
        // - &T → &mut U is NOT ok
        if to_mut && !from_mut {
            return None;
        }

        // Check if from_inner implements Deref with Target = to_inner
        // TODO: Implement proper trait resolution here
        // For now, just return None (no deref coercion)

        None
    }

    /// Try unsizing coercion
    ///
    /// Handles:
    /// - `&[T; N]` → `&[T]` (array to slice)
    /// - `&T` → `&dyn Trait` (concrete type to trait object)
    fn try_unsizing_coercion(
        &mut self,
        _from: TyId,
        to: TyId,
        from_kind: &TyKind,
        to_kind: &TyKind,
    ) -> Option<CoercionResult> {
        // Array to slice: &[T; N] → &[T]
        if let (
            TyKind::Ref {
                mutable: from_mut,
                inner: from_inner,
                lifetime: _from_lifetime,
            },
            TyKind::Ref {
                mutable: to_mut,
                inner: to_inner,
                lifetime: _to_lifetime,
            },
        ) = (from_kind, to_kind)
        {
            let from_inner_ty = self.ctx.types.get(**from_inner);
            let to_inner_ty = self.ctx.types.get(**to_inner);

            // Check array to slice
            if let (
                TyKind::Array {
                    element: from_elem,
                    ..
                },
                TyKind::Slice { element: to_elem },
            ) = (&from_inner_ty.kind, &to_inner_ty.kind)
            {
                // Mutability must match or be compatible
                if from_mut >= to_mut && from_elem == to_elem {
                    return Some(CoercionResult::Coerced(to));
                }
            }

            // Check concrete type to trait object: &T → &dyn Trait
            if let TyKind::DynTrait {
                principal: _trait_id,
                ..
            } = &to_inner_ty.kind
            {
                // Check if from_inner implements the trait
                // TODO: Implement proper trait bound checking here
                // For now, we'll accept any coercion (optimistic)
                // This should be replaced with actual trait resolution

                // Mutability must be compatible
                if from_mut >= to_mut {
                    return Some(CoercionResult::Coerced(to));
                }
            }
        }

        None
    }

    /// Try pointer coercion
    ///
    /// Handles:
    /// - `&T` → `*const T`
    /// - `&mut T` → `*mut T`
    /// - `&mut T` → `*const T`
    fn try_pointer_coercion(
        &mut self,
        _from: TyId,
        to: TyId,
        from_kind: &TyKind,
        to_kind: &TyKind,
    ) -> Option<CoercionResult> {
        match (from_kind, to_kind) {
            // &T → *const T
            (
                TyKind::Ref {
                    mutable: false,
                    inner: from_inner,
                    ..
                },
                TyKind::Pointer {
                    mutable: false,
                    inner: to_inner,
                },
            ) if from_inner == to_inner => Some(CoercionResult::Coerced(to)),

            // &mut T → *mut T
            (
                TyKind::Ref {
                    mutable: true,
                    inner: from_inner,
                    ..
                },
                TyKind::Pointer {
                    mutable: true,
                    inner: to_inner,
                },
            ) if from_inner == to_inner => Some(CoercionResult::Coerced(to)),

            // &mut T → *const T
            (
                TyKind::Ref {
                    mutable: true,
                    inner: from_inner,
                    ..
                },
                TyKind::Pointer {
                    mutable: false,
                    inner: to_inner,
                },
            ) if from_inner == to_inner => Some(CoercionResult::Coerced(to)),

            _ => None,
        }
    }
}

/// Helper to check if a coercion is needed and apply it
pub fn try_coerce(ctx: &mut TyContext, from: TyId, to: TyId) -> Option<TyId> {
    let mut coercer = Coercer::new(ctx);
    match coercer.coerce(from, to) {
        CoercionResult::NoCoercion => Some(from),
        CoercionResult::Coerced(ty) => Some(ty),
        CoercionResult::Failed => None,
    }
}
