//! Type lowering from MIR types to LLVM types

use inkwell::context::Context;
use inkwell::types::{BasicType, BasicTypeEnum};
use rv_lir::LirType;

pub struct TypeLowering<'ctx> {
    context: &'ctx Context,
}

impl<'ctx> TypeLowering<'ctx> {
    pub fn new(context: &'ctx Context) -> Self {
        Self { context }
    }

    /// Lower a MIR type to an LLVM type
    pub fn lower_type(&self, ty: &LirType) -> BasicTypeEnum<'ctx> {
        match ty {
            LirType::Int(rv_hir::IntWidth::I8, _) => self.context.i8_type().into(),
            LirType::Int(rv_hir::IntWidth::I16, _) => self.context.i16_type().into(),
            LirType::Int(rv_hir::IntWidth::I32, _) => self.context.i32_type().into(),
            LirType::Int(rv_hir::IntWidth::I64, _) | LirType::Int(rv_hir::IntWidth::Isize, _) => {
                self.context.i64_type().into()
            }
            LirType::Int(rv_hir::IntWidth::I128, _) => self.context.i128_type().into(),
            LirType::Float(rv_hir::FloatWidth::F32) => self.context.f32_type().into(),
            LirType::Float(rv_hir::FloatWidth::F64) => self.context.f64_type().into(),
            LirType::Char => self.context.i32_type().into(),
            LirType::Bool => self.context.bool_type().into(),
            LirType::String => {
                // &str is a fat pointer: { ptr: *const u8, len: usize }
                // Represented as a struct { ptr, i64 } in LLVM
                let ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
                let len_type = self.context.i64_type();
                self.context
                    .struct_type(&[ptr_type.into(), len_type.into()], false)
                    .into()
            }
            LirType::Unit => {
                // Unit type as i64(0) for consistency with the rest of the compiler
                self.context.i64_type().into()
            }
            LirType::Function { .. } => {
                // Function types become function pointers
                self.context
                    .ptr_type(inkwell::AddressSpace::default())
                    .into()
            }
            LirType::Struct { fields, .. } => {
                // Create proper LLVM struct type with field layout
                let field_types: Vec<BasicTypeEnum<'ctx>> = fields
                    .iter()
                    .map(|field_ty| self.lower_type(field_ty))
                    .collect();

                self.context.struct_type(&field_types, false).into()
            }
            LirType::Enum { variants, .. } => {
                // Enum layout: { i64 discriminant, fields... }
                // Use the largest variant to determine the struct layout
                let mut field_types: Vec<BasicTypeEnum<'ctx>> =
                    vec![self.context.i64_type().into()];

                // Find the variant with the most fields and use its types
                if let Some(largest) = variants.iter().max_by_key(|v| v.fields.len()) {
                    for field_ty in &largest.fields {
                        field_types.push(self.lower_type(field_ty));
                    }
                }

                self.context.struct_type(&field_types, false).into()
            }
            LirType::Array { element, size } => {
                let elem_type = self.lower_type(element);
                elem_type.array_type(*size as u32).into()
            }
            LirType::Slice { .. } => {
                // Slice types as pointers for now
                self.context
                    .ptr_type(inkwell::AddressSpace::default())
                    .into()
            }
            LirType::Tuple(elements) => {
                // Create proper LLVM struct type for tuples
                if elements.is_empty() {
                    // Empty tuple = unit type
                    self.context.i32_type().into()
                } else {
                    let element_types: Vec<BasicTypeEnum<'ctx>> = elements
                        .iter()
                        .map(|elem_ty| self.lower_type(elem_ty))
                        .collect();
                    self.context.struct_type(&element_types, false).into()
                }
            }
            LirType::Ref { .. } | LirType::Pointer { .. } => {
                // Reference and pointer types become LLVM pointers
                self.context
                    .ptr_type(inkwell::AddressSpace::default())
                    .into()
            }
            LirType::Never => {
                // Never type (!) — diverging functions never return a value.
                // Represented as a void/empty struct in LLVM. Any code path
                // producing a Never value is dead code (unreachable).
                self.context.struct_type(&[], false).into()
            }
            LirType::DynTrait { .. } | LirType::ImplTrait { .. } => {
                // Trait objects become opaque pointers
                self.context
                    .ptr_type(inkwell::AddressSpace::default())
                    .into()
            }
            LirType::FunctionPointer { .. } => {
                // Function pointers become LLVM function pointers
                self.context
                    .ptr_type(inkwell::AddressSpace::default())
                    .into()
            }
            LirType::Box { .. } => {
                // Box<T> is a pointer to heap-allocated T
                self.context
                    .ptr_type(inkwell::AddressSpace::default())
                    .into()
            }
        }
    }
}
