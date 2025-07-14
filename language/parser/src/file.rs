use crate::function::function;
use crate::structure::parse_structure;
use crate::util::{file_path, ignored};
use crate::{IResult, Span, TopLevelItem};
use nom::Parser;
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::combinator::map;
use nom::sequence::{delimited, preceded, terminated};
use syntax::util::path::FilePath;

/// Parses a top-level element in the source code
pub fn parse_top_element(input: Span) -> IResult<Span, TopLevelItem> {
    alt((
        map(parse_import, |import| TopLevelItem::Import(import)),
        map(function, |function| {
            println!("Found function!");
            TopLevelItem::Function(function)
        }),
        map(parse_structure, |types| TopLevelItem::Type(types)),
    ))
    .parse(input)
}

/// Parses an import statement
pub fn parse_import(input: Span) -> IResult<Span, FilePath> {
    terminated(preceded(tag("import"), delimited(ignored, file_path, ignored)), tag(";"))
        .parse(input)
}
