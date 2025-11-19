//! Type lowering from MIR types to LLVM types

use inkwell::context::Context;
use inkwell::types::BasicTypeEnum;
use rv_mir::MirType;

pub struct TypeLowering<'ctx> {
    context: &'ctx Context,
}

impl<'ctx> TypeLowering<'ctx> {
    pub fn new(context: &'ctx Context) -> Self {
        Self { context }
    }

    /// Lower a MIR type to an LLVM type
    pub fn lower_type(&self, ty: &MirType) -> BasicTypeEnum<'ctx> {
        eprintln!("DEBUG LLVM lower_type: lowering {:?}", ty);
        let result = match ty {
            MirType::Int => self.context.i32_type().into(),
            MirType::Float => self.context.f64_type().into(),
            MirType::Bool => self.context.i32_type().into(), // Use i32 for booleans
            MirType::String => {
                // String as pointer to i8 array
                self.context.ptr_type(inkwell::AddressSpace::default()).into()
            }
            MirType::Unit => {
                // Unit type as i32(0) for simplicity
                self.context.i32_type().into()
            }
            MirType::Named(name) => {
                // Named types should have been resolved during MIR lowering
                // If we hit this, it's a bug in type resolution
                panic!(
                    "Unresolved named type in LLVM codegen: {:?}. \
                    This indicates a bug in MIR lowering - primitive types should be resolved to \
                    MirType::Int/Float/Bool/String, and user-defined types should be resolved to \
                    MirType::Struct/Enum.",
                    name
                )
            }
            MirType::Function { .. } => {
                // Function types become function pointers
                self.context.ptr_type(inkwell::AddressSpace::default()).into()
            }
            MirType::Struct { fields, .. } => {
                // Create proper LLVM struct type with field layout
                let field_types: Vec<BasicTypeEnum<'ctx>> = fields
                    .iter()
                    .map(|field_ty| self.lower_type(field_ty))
                    .collect();

                self.context.struct_type(&field_types, false).into()
            }
            MirType::Enum { .. } => {
                // Enum types as i32 (discriminant) for now
                self.context.i32_type().into()
            }
            MirType::Array { .. } => {
                // Array types as pointers for now
                self.context.ptr_type(inkwell::AddressSpace::default()).into()
            }
            MirType::Slice { .. } => {
                // Slice types as pointers for now
                self.context.ptr_type(inkwell::AddressSpace::default()).into()
            }
            MirType::Tuple(elements) => {
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
            MirType::Ref { .. } => {
                // Reference types become pointers
                self.context.ptr_type(inkwell::AddressSpace::default()).into()
            }
        };
        eprintln!("DEBUG LLVM lower_type: result = {:?}", result);
        result
    }
}
