use std::error::Error;
use nom_supreme::error::{BaseErrorKind, GenericErrorTree, StackContext};
use crate::Span;

pub fn error_message<E: Error + ?Sized>(error: GenericErrorTree<Span, &str, &str, Box<E>>) -> String {
    match error {
        GenericErrorTree::Base { location, kind } => {
            error_message_with_context(location, vec!(), kind)
        },
        GenericErrorTree::Stack { base, contexts } => {
            match *base {
                GenericErrorTree::Base { location, kind } => {
                    error_message_with_context(location, contexts, kind)
                },
                _ => todo!()
            }
        },
        GenericErrorTree::Alt(_) => "Alt error".to_string()
    }
}

fn error_message_with_context<E: Error + ?Sized>(location: Span, context: Vec<(Span, StackContext<&str>)>, kind: BaseErrorKind<&str, Box<E>>) -> String {
    match kind {
        BaseErrorKind::Kind(nom_error) => format!("Nom error: {:?}\n{}\n\nFor {}", nom_error, location, 
                                                  context.iter().map(|(_, context)| match context {
                                                        StackContext::Context(context) => *context,
                                                        StackContext::Kind(_) => todo!()
                                                  }).collect::<Vec<_>>().join(", ")),
        BaseErrorKind::Expected(custom_error) => format!("Custom error: {}\n{}\n\nFor {}", custom_error, location,
                                                         context.iter().map(|(_, context)| match context {
                                                             StackContext::Context(context) => *context,
                                                             StackContext::Kind(_) => todo!()
                                                         }).collect::<Vec<_>>().join(", ")),
        BaseErrorKind::External(other_error) => format!("Other error: {:?}", other_error),
    }
}