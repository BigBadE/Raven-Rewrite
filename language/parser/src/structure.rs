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
            alt((tuple((preceded(delimited(ignored, tag("struct"), ignored), identifier),
                       map(delimited(
                           delimited(ignored, tag("{"), ignored).context("Opening"),
                           many0(delimited(ignored, parameter, ignored)),
                           delimited(ignored, tag("}"), ignored).context("Closing"),
                       ), |fields| TypeData::Struct { fields }).context("Struct"))),
                tuple((preceded(delimited(ignored, tag("trait"), ignored), identifier),
                       map(delimited(
                           delimited(ignored, tag("{"), ignored).context("Opening"),
                           many0(delimited(ignored, function, ignored)),
                           delimited(ignored, tag("}"), ignored).context("Closing"),
                       ), |functions| TypeData::Trait { functions })
                .context("Trait"))),
            )),
        ))
            .context("Type"),
        |(modifiers, (name, data))| HighType {
            name,
            file: input.extra.file.clone(),
            modifiers,
            data,
        },
    )(input.clone())
}
