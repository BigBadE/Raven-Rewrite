use lasso::Spur;
use std::collections::HashMap;
use syntax::GenericTypeRef;

/// Compares two types to see if target fits the bounds of expected
pub fn check_type(
    target: GenericTypeRef,
    expected: GenericTypeRef,
    _generics: HashMap<Spur, Vec<GenericTypeRef>>,
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
