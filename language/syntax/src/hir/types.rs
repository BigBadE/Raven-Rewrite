use lasso::Spur;
use crate::structure::Modifier;
use crate::util::path::FilePath;

#[derive(Debug)]
pub struct Type<S> {
    pub name: Spur,
    pub file: FilePath,
    pub modifiers: Vec<Modifier>,
    pub data: TypeData<S>
}

#[derive(Debug)]
pub enum TypeData<S> {
    Struct {
        fields: Vec<(Spur, S)>,
    }
}