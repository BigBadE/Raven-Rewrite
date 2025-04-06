use std::collections::HashMap;
use lasso::Spur;
use syntax::TypeRef;

pub fn check_type(target: TypeRef, expected: TypeRef, _generics: HashMap<Spur, Vec<TypeRef>>) -> Result<(), String> {
    if target == expected {
        Ok(())
    } else {
        Err(format!(
            "Type mismatch: expected {:?}, found {:?}",
            expected, target
        ))
    }
}