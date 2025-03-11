use crate::util::{identifier, ignored, modifiers, parameter};
use crate::{IResult, Span};
use lasso::Spur;
use nom::bytes::complete::tag;
use nom::combinator::map;
use nom::multi::many0;
use nom::sequence::{delimited, preceded, tuple};
use nom_supreme::ParserExt;
use syntax::hir::types::{Type, TypeData};

pub fn parse_structure(input: Span) -> IResult<Span, Type<Spur>> {
    map(
        tuple((
            modifiers.context("Modifiers"),
            preceded(delimited(ignored, tag("struct"), ignored), identifier).context("Keyword"),
            delimited(delimited(ignored, tag("{"), ignored),
                      many0(delimited(ignored, parameter, ignored)),
                      delimited(ignored, tag("}"), ignored).context("Struct")
        ))).context("Structure"),
        |(modifiers, name, fields)| Type {
            name,
            file: input.extra.file.clone(),
            modifiers,
            data: TypeData::Struct {
                fields
            }
        })(input.clone())
}