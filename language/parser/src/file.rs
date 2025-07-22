use crate::errors::{context, expect};
use crate::function::function;
use crate::structure::{parse_structure, parse_impl};
use crate::util::{file_path, ignored, tag_parser};
use crate::{IResult, Span, TopLevelItem};
use nom::branch::alt;
use nom::combinator::map;
use nom::sequence::{delimited, preceded, terminated};
use nom::Parser;
use syntax::util::path::FilePath;

/// Parses a top-level element in the source code
pub fn parse_top_element(input: Span) -> IResult<Span, TopLevelItem> {
    alt((
        map(parse_import, |import| TopLevelItem::Import(import)),
        map(function, |function| TopLevelItem::Function(function)),
        map(parse_structure, |types| TopLevelItem::Type(types)),
        map(parse_impl, |impl_block| TopLevelItem::Impl(impl_block))
    ))(input)
}

/// Parses an import statement
pub fn parse_import(input: Span) -> IResult<Span, FilePath> {
    terminated(preceded(context(tag_parser("import"), "import keyword 'import'", Some("imports must start with 'import'")), delimited(ignored, expect(file_path, "import path", Some("import paths must be valid module paths like 'module::submodule'")), ignored)), expect(tag_parser(";"), "semicolon ';'", Some("import statements must end with ';'")))
        .parse(input)
}
