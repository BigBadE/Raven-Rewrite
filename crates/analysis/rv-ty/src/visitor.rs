//! Type visitor infrastructure for traversing type structures

use crate::context::TyContext;
use crate::ty::{TyId, TyKind, TyVarId, VariantTy};
use rv_hir::TypeDefId;
use rv_intern::Symbol;

/// Visitor trait for immutable type traversal
pub trait TypeVisitor {
    /// Output type produced by visiting
    type Output;

    /// Visit a type ID (entry point)
    fn visit_ty(&mut self, ty_id: TyId, ctx: &TyContext) -> Self::Output {
        let ty = ctx.types.get(ty_id);
        self.visit_ty_kind(&ty.kind, ty_id, ctx)
    }

    /// Visit a type kind (can be overridden for custom behavior)
    fn visit_ty_kind(&mut self, kind: &TyKind, ty_id: TyId, ctx: &TyContext) -> Self::Output {
        match kind {
            TyKind::Var { id } => self.visit_var(*id, ty_id, ctx),
            TyKind::Struct { def_id, fields } => self.visit_struct(*def_id, fields, ty_id, ctx),
            TyKind::Function { params, ret } => self.visit_function(params, ret, ty_id, ctx),
            TyKind::Tuple { elements } => self.visit_tuple(elements, ty_id, ctx),
            TyKind::Ref { mutable, inner } => self.visit_ref(*mutable, inner, ty_id, ctx),
            TyKind::Array { element, size } => self.visit_array(element, *size, ty_id, ctx),
            TyKind::Slice { element } => self.visit_slice(element, ty_id, ctx),
            TyKind::Enum { def_id, variants } => self.visit_enum(*def_id, variants, ty_id, ctx),
            TyKind::Int => self.visit_int(ty_id, ctx),
            TyKind::Float => self.visit_float(ty_id, ctx),
            TyKind::Bool => self.visit_bool(ty_id, ctx),
            TyKind::String => self.visit_string(ty_id, ctx),
            TyKind::Unit => self.visit_unit(ty_id, ctx),
            TyKind::Never => self.visit_never(ty_id, ctx),
            TyKind::Error => self.visit_error(ty_id, ctx),
            TyKind::Named { name, def, args } => self.visit_named(*name, *def, args, ty_id, ctx),
            TyKind::Param { index, name } => self.visit_param(*index, *name, ty_id, ctx),
        }
    }

    // Structural types with automatic recursion

    /// Visit type variable
    fn visit_var(&mut self, _id: TyVarId, ty_id: TyId, ctx: &TyContext) -> Self::Output {
        self.default_output(ty_id, ctx)
    }

    /// Visit struct type
    fn visit_struct(
        &mut self,
        _def_id: TypeDefId,
        fields: &[(Symbol, TyId)],
        ty_id: TyId,
        ctx: &TyContext,
    ) -> Self::Output {
        // Default: recurse into field types
        for (_, field_ty) in fields {
            self.visit_ty(*field_ty, ctx);
        }
        self.default_output(ty_id, ctx)
    }

    /// Visit function type
    fn visit_function(
        &mut self,
        params: &[TyId],
        ret: &TyId,
        ty_id: TyId,
        ctx: &TyContext,
    ) -> Self::Output {
        // Default: recurse into params and return type
        for param in params {
            self.visit_ty(*param, ctx);
        }
        self.visit_ty(*ret, ctx);
        self.default_output(ty_id, ctx)
    }

    /// Visit tuple type
    fn visit_tuple(&mut self, elements: &[TyId], ty_id: TyId, ctx: &TyContext) -> Self::Output {
        // Default: recurse into elements
        for elem in elements {
            self.visit_ty(*elem, ctx);
        }
        self.default_output(ty_id, ctx)
    }

    /// Visit reference type
    fn visit_ref(&mut self, _mutable: bool, inner: &TyId, ty_id: TyId, ctx: &TyContext) -> Self::Output {
        // Default: recurse into inner type
        self.visit_ty(*inner, ctx);
        self.default_output(ty_id, ctx)
    }

    /// Visit array type
    fn visit_array(&mut self, element: &TyId, _size: usize, ty_id: TyId, ctx: &TyContext) -> Self::Output {
        // Default: recurse into element type
        self.visit_ty(*element, ctx);
        self.default_output(ty_id, ctx)
    }

    /// Visit slice type
    fn visit_slice(&mut self, element: &TyId, ty_id: TyId, ctx: &TyContext) -> Self::Output {
        // Default: recurse into element type
        self.visit_ty(*element, ctx);
        self.default_output(ty_id, ctx)
    }

    /// Visit enum type
    fn visit_enum(
        &mut self,
        _def_id: TypeDefId,
        variants: &[(Symbol, VariantTy)],
        ty_id: TyId,
        ctx: &TyContext,
    ) -> Self::Output {
        // Default: recurse into variant types
        for (_, variant) in variants {
            match variant {
                VariantTy::Unit => {}
                VariantTy::Tuple(types) => {
                    for ty in types {
                        self.visit_ty(*ty, ctx);
                    }
                }
                VariantTy::Struct(fields) => {
                    for (_, field_ty) in fields {
                        self.visit_ty(*field_ty, ctx);
                    }
                }
            }
        }
        self.default_output(ty_id, ctx)
    }

    /// Visit named type
    fn visit_named(
        &mut self,
        _name: Symbol,
        _def: TypeDefId,
        args: &[TyId],
        ty_id: TyId,
        ctx: &TyContext,
    ) -> Self::Output {
        // Default: recurse into generic arguments
        for arg in args {
            self.visit_ty(*arg, ctx);
        }
        self.default_output(ty_id, ctx)
    }

    // Leaf types (no recursion needed)

    /// Visit int type
    fn visit_int(&mut self, ty_id: TyId, ctx: &TyContext) -> Self::Output {
        self.default_output(ty_id, ctx)
    }

    /// Visit float type
    fn visit_float(&mut self, ty_id: TyId, ctx: &TyContext) -> Self::Output {
        self.default_output(ty_id, ctx)
    }

    /// Visit bool type
    fn visit_bool(&mut self, ty_id: TyId, ctx: &TyContext) -> Self::Output {
        self.default_output(ty_id, ctx)
    }

    /// Visit string type
    fn visit_string(&mut self, ty_id: TyId, ctx: &TyContext) -> Self::Output {
        self.default_output(ty_id, ctx)
    }

    /// Visit unit type
    fn visit_unit(&mut self, ty_id: TyId, ctx: &TyContext) -> Self::Output {
        self.default_output(ty_id, ctx)
    }

    /// Visit never type
    fn visit_never(&mut self, ty_id: TyId, ctx: &TyContext) -> Self::Output {
        self.default_output(ty_id, ctx)
    }

    /// Visit error type
    fn visit_error(&mut self, ty_id: TyId, ctx: &TyContext) -> Self::Output {
        self.default_output(ty_id, ctx)
    }

    /// Visit type parameter
    fn visit_param(&mut self, _index: usize, _name: Symbol, ty_id: TyId, ctx: &TyContext) -> Self::Output {
        self.default_output(ty_id, ctx)
    }

    /// Default output for a type (must be implemented)
    fn default_output(&mut self, ty_id: TyId, ctx: &TyContext) -> Self::Output;
}

/// Mutable visitor trait for type transformations
pub trait TypeMutVisitor {
    /// Output type produced by visiting
    type Output;
    /// Error type
    type Error;

    /// Visit a type ID and potentially transform it
    fn visit_ty_mut(&mut self, ty_id: TyId, ctx: &mut TyContext) -> Result<Self::Output, Self::Error>;

    /// Default output for a type (must be implemented)
    fn default_output(&mut self, ty_id: TyId, ctx: &mut TyContext) -> Result<Self::Output, Self::Error>;
}
