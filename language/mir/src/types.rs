use crate::{MediumSyntaxLevel, MirFunctionContext};
use hir::types::{HighType, TypeData};
use hir::HighSyntaxLevel;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use syntax::structure::traits::Type;
use syntax::structure::visitor::Translate;
use syntax::structure::Modifier;
use syntax::util::translation::Translatable;
use syntax::util::CompileError;
use syntax::{get_monomorphized_name, GenericTypeRef, SyntaxLevel, TypeRef};

/// A type in the MIR
#[derive(Serialize, Deserialize, Clone)]
pub struct MediumType<T: SyntaxLevel> {
    /// The reference to the type
    pub reference: T::TypeReference,
    /// The type's modifiers
    pub modifiers: Vec<Modifier>,
    /// The type's fields
    pub fields: Vec<T::TypeReference>,
}

impl<T: SyntaxLevel> Type<T::TypeReference> for MediumType<T> {
    fn reference(&self) -> &T::TypeReference {
        &self.reference
    }
}

impl<'a> Translate<(), MirFunctionContext<'a>> for HighType<HighSyntaxLevel>
{
    fn translate(
        &self,
        context: &mut MirFunctionContext<'a>,
    ) -> Result<(), CompileError> {
        if !self.generics.is_empty() {
            return Ok(());
        }

        if let TypeData::Struct { fields } = &self.data {
            let types = MediumType::<MediumSyntaxLevel> {
                reference: HighSyntaxLevel::translate_type_ref(&self.reference, context)?,
                modifiers: self.modifiers.clone(),
                fields: fields
                    .iter()
                    .map(|(_, types)| HighSyntaxLevel::translate_type_ref(types, context))
                    .collect::<Result<_, _>>()?,
            };
            context.output.types.insert(types.reference.clone(), types);
        }
        Ok(())
    }
}

impl<'a> Translate<TypeRef, MirFunctionContext<'a>> for GenericTypeRef {
    fn translate(&self, context: &mut MirFunctionContext<'a>) -> Result<TypeRef, CompileError> {
        match self {
            GenericTypeRef::Struct { reference, generics } => {
                if generics.is_empty() {
                    translate_empty_generic_struct(reference, context)
                } else {
                    translate_parameterized_struct(reference, generics, context)
                }
            }
            GenericTypeRef::Generic { reference } => {
                if let Some(concrete_type) = context.generics.get(self) {
                    Ok(concrete_type.clone())
                } else {
                    Ok(reference.clone())
                }
            }
        }
    }
}

/// Translates a struct type reference with no generic parameters
fn translate_empty_generic_struct(
    reference: &TypeRef,
    context: &mut MirFunctionContext,
) -> Result<TypeRef, CompileError> {
    let base_type_ref = GenericTypeRef::Struct {
        reference: reference.clone(),
        generics: vec![],
    };

    if let Some(base_type) = context.source.syntax.types.get(&base_type_ref) {
        if !base_type.generics.is_empty() {
            return try_infer_and_recurse(reference, base_type, context);
        }
    }

    Ok(reference.clone())
}

/// Attempts to infer generic types and recurse with the inferred type
fn try_infer_and_recurse(
    reference: &TypeRef,
    base_type: &HighType<HighSyntaxLevel>,
    context: &mut MirFunctionContext,
) -> Result<TypeRef, CompileError> {
    let inferred_generics = infer_generic_types_for_struct(
        base_type,
        &context.generics,
        context,
    )?;

    if !inferred_generics.is_empty() {
        let inferred_type = GenericTypeRef::Struct {
            reference: reference.clone(),
            generics: inferred_generics,
        };
        return Translate::translate(&inferred_type, context);
    }

    Ok(reference.clone())
}

/// Translates a struct type with generic parameters
fn translate_parameterized_struct(
    reference: &TypeRef,
    generics: &[GenericTypeRef],
    context: &mut MirFunctionContext,
) -> Result<TypeRef, CompileError> {
    let translated_generics = generics.iter()
        .map(|generic| Translate::translate(generic, context))
        .collect::<Result<Vec<_>, _>>()?;
    let monomorphized_reference = get_monomorphized_name(reference,
                                                         translated_generics.iter(), &context.source.syntax.symbols)?;

    if context.output.types.contains_key(&monomorphized_reference) {
        return Ok(monomorphized_reference);
    }

    let specialized_type = create_monomorphized_type(
        reference,
        &translated_generics,
        &monomorphized_reference,
        context,
    )?;

    context.output.types.insert(monomorphized_reference.clone(), specialized_type);
    Ok(monomorphized_reference)
}

/// Infers generic types for a struct using advanced unification
fn infer_generic_types_for_struct(
    base_type: &HighType<HighSyntaxLevel>,
    context_generics: &HashMap<GenericTypeRef, TypeRef>,
    _context: &MirFunctionContext,
) -> Result<Vec<GenericTypeRef>, CompileError> {
    let mut inferred_generics = Vec::new();

    // For each generic parameter in the struct definition
    for generic_param in base_type.generics.keys() {
        let generic_key = GenericTypeRef::Generic { reference: vec![*generic_param] };

        // Use the advanced substitution system to resolve the generic
        if let Some(concrete_type) = context_generics.get(&generic_key) {
            inferred_generics.push(GenericTypeRef::from(concrete_type.clone()));
        } else {
            // If we can't infer all generics, return empty to fall back to base type
            return Ok(vec![]);
        }
    }

    Ok(inferred_generics)
}

/// Creates a monomorphized type using advanced substitution algorithms
fn create_monomorphized_type(
    reference: &TypeRef,
    translated_generics: &[TypeRef],
    monomorphized_reference: &TypeRef,
    context: &mut MirFunctionContext,
) -> Result<MediumType<MediumSyntaxLevel>, CompileError> {
    let base_type_ref = GenericTypeRef::Struct {
        reference: reference.clone(),
        generics: vec![],
    };

    let base_type = &context.source.syntax.types[&base_type_ref];
    let substitutions = build_substitution_map(base_type, translated_generics);

    match &base_type.data {
        TypeData::Struct { fields } => {
            let specialized_fields = substitute_field_types(fields, &substitutions, context)?;
            Ok(MediumType {
                reference: monomorphized_reference.clone(),
                modifiers: base_type.modifiers.clone(),
                fields: specialized_fields,
            })
        }
        TypeData::Trait { .. } => {
            Ok(MediumType {
                reference: monomorphized_reference.clone(),
                modifiers: base_type.modifiers.clone(),
                fields: vec![],
            })
        }
    }
}


/// Builds a substitution map for generic parameters
fn build_substitution_map(
    base_type: &HighType<HighSyntaxLevel>,
    translated_generics: &[TypeRef],
) -> HashMap<GenericTypeRef, TypeRef> {
    let mut substitutions = HashMap::new();

    for (generic_param, translated_generic) in base_type.generics.keys().zip(translated_generics) {
        let generic_key = GenericTypeRef::Generic { reference: vec![*generic_param] };
        substitutions.insert(generic_key, translated_generic.clone());
    }

    substitutions
}


/// Substitutes generic types in struct fields
fn substitute_field_types(
    fields: &Vec<(lasso::Spur, GenericTypeRef)>,
    substitutions: &HashMap<GenericTypeRef, TypeRef>,
    context: &mut MirFunctionContext,
) -> Result<Vec<TypeRef>, CompileError> {
    fields.iter().map(|(_name, field_type)| {
        let substituted_field_type = field_type.substitute_generics_in_type(substitutions)?;
        Translate::translate(&substituted_field_type, context)
    }).collect()
}

