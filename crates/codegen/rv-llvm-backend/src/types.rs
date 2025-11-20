//! Type lowering from MIR types to LLVM types

use inkwell::context::Context;
use inkwell::types::BasicTypeEnum;
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
            LirType::Int => self.context.i32_type().into(),
            LirType::Float => self.context.f64_type().into(),
            LirType::Bool => self.context.i32_type().into(), // Use i32 for booleans
            LirType::String => {
                // String as pointer to i8 array
                self.context.ptr_type(inkwell::AddressSpace::default()).into()
            }
            LirType::Unit => {
                // Unit type as i32(0) for simplicity
                self.context.i32_type().into()
            }
            LirType::Function { .. } => {
                // Function types become function pointers
                self.context.ptr_type(inkwell::AddressSpace::default()).into()
            }
            LirType::Struct { fields, .. } => {
                // Create proper LLVM struct type with field layout
                let field_types: Vec<BasicTypeEnum<'ctx>> = fields
                    .iter()
                    .map(|field_ty| self.lower_type(field_ty))
                    .collect();

                self.context.struct_type(&field_types, false).into()
            }
            LirType::Enum { .. } => {
                // Enum types as i32 (discriminant) for now
                self.context.i32_type().into()
            }
            LirType::Array { .. } => {
                // Array types as pointers for now
                self.context.ptr_type(inkwell::AddressSpace::default()).into()
            }
            LirType::Slice { .. } => {
                // Slice types as pointers for now
                self.context.ptr_type(inkwell::AddressSpace::default()).into()
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
            LirType::Ref { .. } => {
                // Reference types become pointers
                self.context.ptr_type(inkwell::AddressSpace::default()).into()
            }
        }
    }
}
