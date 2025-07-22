use indexmap::IndexMap;
use crate::errors::{expect, context};
use crate::function::function;
use crate::util::{identifier, ignored, modifiers, struct_field, tag_parser, type_ref};
use crate::{IResult, Span};
use hir::types::{HighType, TypeData};
use hir::{RawSyntaxLevel, RawTypeRef};
use hir::impl_block::HighImpl;
use lasso::Spur;
use nom::Parser;
use nom::branch::alt;
use nom::combinator::{map, opt};
use nom::multi::{many0, separated_list0, separated_list1};
use nom::sequence::{delimited, preceded, terminated, tuple};

/// Parses a structure or trait definition
pub fn parse_structure(input: Span) -> IResult<Span, HighType<RawSyntaxLevel>> {
    map(
        tuple((
            modifiers,
            alt((
                tuple((
                    preceded(delimited(ignored, context(tag_parser("struct"), "struct keyword 'struct'", Some("struct definitions start with 'struct'")), ignored), expect(identifier, "struct name", Some("struct names must be valid identifiers"))),
                    opt(generics),
                    map(
                        delimited(
                            delimited(ignored, expect(tag_parser("{"), "opening brace '{'", Some("struct bodies start with '{'")), ignored),
                            terminated(separated_list0(delimited(ignored, tag_parser(","), ignored), delimited(ignored, struct_field, ignored)), opt(delimited(ignored, tag_parser(","), ignored))),
                            delimited(ignored, expect(tag_parser("}"), "closing brace '}'", Some("struct bodies end with '}'")), ignored),
                        ),
                        |fields| TypeData::Struct { fields },
                    ),
                )),
                tuple((
                    preceded(delimited(ignored, context(tag_parser("trait"), "trait keyword 'trait'", Some("trait definitions start with 'trait'")), ignored), identifier),
                    opt(generics),
                    map(
                        delimited(
                            delimited(ignored, expect(tag_parser("{"), "opening brace '{'", Some("trait bodies start with '{'")), ignored),
                            many0(delimited(ignored, function, ignored)),
                            delimited(ignored, expect(tag_parser("}"), "closing brace '}'", Some("trait bodies end with '}'")), ignored),
                        ),
                        |functions| TypeData::Trait { functions },
                    ),
                )),
            )),
        )),
        |(modifiers, (name, generics, data))| {
            let mut reference = input.extra.file.clone();
            reference.push(name);
            HighType {
                reference: reference.into(),
                generics: generics.unwrap_or_default(),
                modifiers,
                data,
            }
        },
    )(input.clone())
}

/// Parses generics
pub fn generics(input: Span) -> IResult<Span, IndexMap<Spur, Vec<RawTypeRef>>> {
    map(opt(delimited(
        delimited(ignored, tag_parser("<"), ignored),
        map(separated_list1(
            delimited(ignored, tag_parser(","), ignored),
            tuple((
                identifier,
                map(
                    opt(preceded(context(tag_parser(":"), "colon ':'", Some("generic constraints use ':' separator")), separated_list0(tag_parser("+"), type_ref))),
                    |generics| generics.unwrap_or_default(),
                ),
            )),
        ), |list| IndexMap::from_iter(list.into_iter())),
        delimited(ignored, expect(tag_parser(">"), "closing angle bracket '>'", Some("generic parameters end with '>'")), ignored),
    )), |generics| {
        generics.unwrap_or_default()
    })
    .parse(input)
}

/// Parses an impl block
pub fn parse_impl(input: Span) -> IResult<Span, HighImpl<RawSyntaxLevel>> {
    map(
        tuple((
            modifiers,
            preceded(
                delimited(ignored, context(tag_parser("impl"), "impl keyword 'impl'", Some("impl blocks start with 'impl'")), ignored),
                alt((
                    // impl Trait for Type
                    map(
                        tuple((
                            type_ref,
                            preceded(delimited(ignored, tag_parser("for"), ignored), type_ref),
                        )),
                        |(trait_ref, target_type)| (Some(trait_ref), target_type)
                    ),
                    // impl Type
                    map(type_ref, |target_type| (None, target_type))
                ))
            ),
            opt(generics),
            delimited(
                delimited(ignored, expect(tag_parser("{"), "opening brace '{'", Some("impl block bodies start with '{'")), ignored),
                many0(delimited(ignored, function, ignored)),
                delimited(ignored, expect(tag_parser("}"), "closing brace '}'", Some("impl block bodies end with '}'")), ignored),
            ),
        )),
        |(modifiers, (trait_ref, target_type), generics, functions)| {
            HighImpl {
                trait_ref,
                target_type,
                generics: generics.unwrap_or_default(),
                modifiers,
                functions,
            }
        },
    )(input)
}
