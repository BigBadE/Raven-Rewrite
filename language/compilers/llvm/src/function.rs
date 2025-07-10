use crate::types::TypeManager;
use inkwell::types::BasicType;
use inkwell::values::FunctionValue;
use mir::MediumSyntaxLevel;
use mir::function::MediumFunction;
use syntax::util::pretty_print::PrettyPrint;

/// Gets the LLVM type of a MIR function
pub fn get_function_type<'a, 'ctx>(
    type_manager: &mut TypeManager<'a, 'ctx>,
    function: &'ctx MediumFunction<MediumSyntaxLevel>,
) -> FunctionValue<'ctx> {
    let parameters = function
        .parameters
        .iter()
        .map(|param| type_manager.convert_type(param).into())
        .collect::<Vec<_>>();
    let parameters = parameters.as_slice();
    type_manager.module.add_function(
        &function.reference.format_top(&type_manager.syntax.symbols, &mut String::new()).unwrap(),
        function
            .return_type
            .as_ref()
            .map(|inner| type_manager.convert_type(inner).fn_type(parameters, false))
            .unwrap_or_else(|| type_manager.context.void_type().fn_type(parameters, false)),
        None,
    )
}
