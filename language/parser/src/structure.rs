use crate::function::function;
use crate::util::{identifier, ignored, modifiers, parameter};
use crate::{IResult, Span};
use hir::types::{HighType, TypeData};
use hir::RawSyntaxLevel;
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::combinator::map;
use nom::multi::many0;
use nom::sequence::{delimited, preceded, tuple};
use nom_supreme::ParserExt;

pub fn parse_structure(input: Span) -> IResult<Span, HighType<RawSyntaxLevel>> {
    map(
        tuple((
            modifiers.context("Modifiers"),
            alt((tuple((preceded(delimited(ignored, tag("struct"), ignored), identifier).context("Keyword"),
                       map(delimited(
                           delimited(ignored, tag("{"), ignored),
                           many0(delimited(ignored, parameter, ignored)),
                           delimited(ignored, tag("}"), ignored).context("Struct"),
                       ), |fields| TypeData::Struct { fields }))),
                tuple((preceded(delimited(ignored, tag("trait"), ignored), identifier).context("Keyword"),
                       map(delimited(
                           delimited(ignored, tag("{"), ignored),
                           many0(delimited(ignored, function, ignored)),
                           delimited(ignored, tag("}"), ignored).context("Struct"),
                       ), |functions| TypeData::Trait { functions })))
            )),
        ))
            .context("Structure"),
        |(modifiers, (name, data))| HighType {
            name,
            file: input.extra.file.clone(),
            modifiers,
            data,
        },
    )(input.clone())
}
