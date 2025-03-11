use crate::structure::visitor::{visit_syntax, Visitor};
use crate::util::path::FilePath;
use crate::{FunctionRef, LowSyntax, Syntax, TypeRef};
use lasso::Spur;
use std::collections::HashMap;
use crate::util::ParseError;

pub mod types;

#[derive(Default)]
pub struct RawSource {
    pub syntax: Syntax<Spur, Spur>,
    pub imports: HashMap<FilePath, Vec<FilePath>>,
    pub types: HashMap<FilePath, TypeRef>,
    pub functions: HashMap<FilePath, FunctionRef>,
}

pub fn resolve_to_hir(source: RawSource) -> Result<LowSyntax, Vec<ParseError>> {
    visit_syntax(&source.syntax, &mut HirVisitor {
        syntax: &source,
        type_cache: HashMap::default(),
        func_cache: HashMap::default(),
    })
}

pub struct HirVisitor<'a> {
    syntax: &'a RawSource,
    type_cache: HashMap<Spur, TypeRef>,
    func_cache: HashMap<Spur, FunctionRef>,
}

impl<'a> Visitor<Spur, Spur, TypeRef, FunctionRef> for HirVisitor<'a> {
    fn visit_type_ref(&mut self, node: &Spur, file: &FilePath) -> Result<TypeRef, ParseError> {
        for import in &self.syntax.imports[file] {
            if import.last().unwrap() == node {
                if let Some(types) = self.syntax.types.get(import) {
                    return Ok(*types);
                }
                
            }
        }
        todo!()
    }

    fn visit_function_ref(&mut self, node: &Spur, file: &FilePath) -> Result<FunctionRef, ParseError> {
        todo!()
    }
}