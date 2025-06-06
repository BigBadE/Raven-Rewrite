use crate::function::function;
use crate::structure::parse_structure;
use crate::util::{file_path, ignored};
use crate::{IResult, Span, TopLevelItem};
use nom::Parser;
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::combinator::map;
use nom::sequence::delimited;
use nom_supreme::ParserExt;
use syntax::util::path::FilePath;

/// Parses a top-level element in the source code
pub fn parse_top_element(input: Span) -> IResult<Span, TopLevelItem> {
    alt((
        map(parse_import, |import| TopLevelItem::Import(import)),
        map(function, |function| TopLevelItem::Function(function)),
        map(parse_structure, |types| TopLevelItem::Type(types)),
    ))
    .context("Top")
    .parse(input)
}

/// Parses an import statement
pub fn parse_import(input: Span) -> IResult<Span, FilePath> {
    tag("import")
        .precedes(delimited(ignored, file_path, ignored))
        .terminated(tag(";"))
        .parse(input)
}
