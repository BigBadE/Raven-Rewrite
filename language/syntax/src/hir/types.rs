use lasso::Spur;
use crate::TypeRef;

#[derive(Debug)]
pub enum Type {
    Struct {
        name: Spur,
        fields: Vec<(Spur, TypeRef)>,
    }
}