use syntax::TypeRef;

pub fn check_type(target: TypeRef, expected: TypeRef) -> Result<(), String> {
    if target == expected {
        Ok(())
    } else {
        Err(format!(
            "Type mismatch: expected {:?}, found {:?}",
            expected, target
        ))
    }
}