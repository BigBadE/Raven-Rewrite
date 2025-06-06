use lasso::Spur;
use std::collections::HashMap;
use syntax::TypeRef;

/// Compares two types to see if target fits the bounds of expected
pub fn check_type(
    target: TypeRef,
    expected: TypeRef,
    _generics: HashMap<Spur, Vec<TypeRef>>,
) -> Result<(), String> {
    if target == expected {
        Ok(())
    } else {
        Err(format!(
            "Type mismatch: expected {:?}, found {:?}",
            expected, target
        ))
    }
}
