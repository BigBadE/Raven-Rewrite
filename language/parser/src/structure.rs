use indexmap::IndexMap;
use crate::errors::{expect, context};
use crate::function::function;
use crate::util::{identifier, ignored, modifiers, parameter, tag_parser, type_ref};
use crate::{IResult, Span};
use hir::types::{HighType, TypeData};
use hir::{RawSyntaxLevel, RawTypeRef};
use lasso::Spur;
use nom::Parser;
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::combinator::{map, opt};
use nom::multi::{many0, separated_list0, separated_list1};
use nom::sequence::{delimited, preceded, terminated, tuple};

/// Parses a structure or trait definition
pub fn parse_structure(input: Span) -> IResult<Span, HighType<RawSyntaxLevel>> {
    map(
        tuple((
            expect(modifiers, "modifiers", Some("modifiers like 'pub' can appear before struct/trait definitions")),
            alt((
                tuple((
                    preceded(delimited(ignored, context(tag_parser("struct"), "struct keyword 'struct'", Some("struct definitions start with 'struct'")), ignored), expect(identifier, "struct name", Some("struct names must be valid identifiers"))),
                    opt(generics),
                    map(
                        delimited(
                            delimited(ignored, expect(tag_parser("{"), "opening brace '{'", Some("struct bodies start with '{'")), ignored),
                            terminated(separated_list0(delimited(ignored, tag(","), ignored), delimited(ignored, parameter, ignored)), opt(delimited(ignored, tag(","), ignored))),
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
            delimited(ignored, tag(","), ignored),
            tuple((
                identifier,
                map(
                    opt(preceded(expect(tag_parser(":"), "colon ':'", Some("generic constraints use ':' separator")), separated_list0(tag("+"), type_ref))),
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
