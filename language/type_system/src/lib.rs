use lasso::{Spur, ThreadedRodeo};
use std::collections::HashMap;
use syntax::GenericTypeRef;
use syntax::util::CompileError;
use syntax::util::pretty_print::PrettyPrint;

/// Compares two types to see if target fits the bounds of expected
pub fn check_type(
    interner: &ThreadedRodeo,
    target: GenericTypeRef,
    expected: GenericTypeRef,
    _generics: HashMap<Spur, Vec<GenericTypeRef>>,
) -> Result<(), CompileError> {
    if target == expected {
        Ok(())
    } else {
        let mut error = "Type mismatch: expected ".to_string();
        expected.format_top(interner, &mut error)?;
        error.push_str(", found ");
        target.format_top(interner, &mut error)?;
        Err(CompileError::Basic(error))
    }
}
