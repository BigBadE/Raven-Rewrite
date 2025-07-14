use indexmap::IndexMap;
use crate::function::function;
use crate::util::{identifier, ignored, modifiers, parameter, type_ref};
use crate::{IResult, Span};
use hir::types::{HighType, TypeData};
use hir::{RawSyntaxLevel, RawTypeRef};
use lasso::Spur;
use nom::Parser;
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::combinator::{map, opt};
use nom::multi::{many0, separated_list0, separated_list1};
use nom::sequence::{delimited, preceded, tuple};

/// Parses a structure or trait definition
pub fn parse_structure(input: Span) -> IResult<Span, HighType<RawSyntaxLevel>> {
    map(
        tuple((
            modifiers,
            alt((
                tuple((
                    preceded(delimited(ignored, tag("struct"), ignored), identifier),
                    opt(generics),
                    map(
                        delimited(
                            delimited(ignored, tag("{"), ignored),
                            separated_list0(tag(","), delimited(ignored, parameter, ignored)),
                            delimited(ignored, tag("}"), ignored),
                        ),
                        |fields| TypeData::Struct { fields },
                    ),
                )),
                tuple((
                    preceded(delimited(ignored, tag("trait"), ignored), identifier),
                    opt(generics),
                    map(
                        delimited(
                            delimited(ignored, tag("{"), ignored),
                            many0(delimited(ignored, function, ignored)),
                            delimited(ignored, tag("}"), ignored),
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
        delimited(ignored, tag("<"), ignored),
        map(separated_list1(
            delimited(ignored, tag(","), ignored),
            tuple((
                identifier,
                map(
                    opt(preceded(tag(":"), separated_list0(tag("+"), type_ref))),
                    |generics| generics.unwrap_or_default(),
                ),
            )),
        ), |list| IndexMap::from_iter(list.into_iter())),
        delimited(ignored, tag(">"), ignored),
    )), |generics| {
        generics.unwrap_or_default()
    })
    .parse(input)
}
