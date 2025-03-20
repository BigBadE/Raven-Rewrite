use crate::Span;
use nom_supreme::error::{BaseErrorKind, GenericErrorTree, StackContext};
use std::error::Error;

pub fn error_message<E: Error + ?Sized>(
    error: GenericErrorTree<Span, &str, &str, Box<E>>,
) -> String {
    error_message_recursive(error, &vec![])
}

pub fn error_message_recursive<E: Error + ?Sized>(
    error: GenericErrorTree<Span, &str, &str, Box<E>>,
    context: &Vec<(Span, StackContext<&str>)>,
) -> String {
    match error {
        GenericErrorTree::Base { location, kind } => display_error(location, context, kind),
        GenericErrorTree::Stack { base, mut contexts } => {
            let mut context = context.clone();
            context.append(&mut contexts);
            error_message_recursive(*base, &context)
        }
        GenericErrorTree::Alt(errors) => format!(
            "Possible:\n{}",
            errors
                .into_iter()
                .map(|err| error_message_recursive(err, context))
                .collect::<Vec<_>>()
                .join("\n")
        ),
    }
}

fn display_error<E: Error + ?Sized>(
    location: Span,
    context: &Vec<(Span, StackContext<&str>)>,
    kind: BaseErrorKind<&str, Box<E>>,
) -> String {
    let context = context
        .iter()
        .map(|(_, context)| match context {
            StackContext::Context(context) => *context,
            StackContext::Kind(_) => todo!(),
        })
        .collect::<Vec<_>>()
        .join(", ");
    match kind {
        BaseErrorKind::Kind(nom_error) => format!(
            "Nom error: {:?}\n{}\n\nFor {}",
            nom_error, location, context
        ),
        BaseErrorKind::Expected(custom_error) => format!(
            "Custom error: {}\n{}\n\nFor {}",
            custom_error, location, context
        ),
        BaseErrorKind::External(other_error) => format!("Other error: {:?}", other_error),
    }
}
