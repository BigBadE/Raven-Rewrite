use crate::code::expression::Expression;
use crate::code::statement::{Conditional, Statement};
use crate::hir::types::{Type, TypeData};
use crate::structure::function::Function;
use crate::util::{collect_results, ParseError};
use crate::util::path::FilePath;
use crate::Syntax;

pub trait Visitor<SI, FI, SO, FO> {
    fn visit_type_ref(&mut self, node: &SI, file: &FilePath) -> Result<SO, ParseError>;

    fn visit_function_ref(&mut self, node: &FI, file: &FilePath) -> Result<FO, ParseError>;

    fn visit_statement(
        &mut self,
        node: &Statement<SI, FI>,
        file: &FilePath,
    ) -> Result<Statement<SO, FO>, ParseError> {
        Ok(match node {
            Statement::Expression(expression) => {
                Statement::Expression(self.visit_expression(expression, file)?)
            }
            Statement::Return => Statement::Return,
            Statement::Break => Statement::Break,
            Statement::Continue => Statement::Continue,
            Statement::If {
                conditions,
                else_branch,
            } => Statement::If {
                conditions: conditions
                    .iter()
                    .map(|condition| {
                        Ok::<_, ParseError>(Conditional {
                            condition: self.visit_expression(&condition.condition, file)?,
                            branch: self.visit_statement(&condition.branch, file)?,
                        })
                    })
                    .collect::<Result<_, _>>()?,
                else_branch: else_branch
                    .as_ref()
                    .map(|branch| {
                        Ok::<_, ParseError>(Box::new(self.visit_statement(branch, file)?))
                    })
                    .transpose()?,
            },
            Statement::For { iterator, body } => Statement::For {
                iterator: Box::new(self.visit_expression(iterator, file)?),
                body: Box::new(self.visit_statement(body, file)?),
            },
            Statement::While { condition } => Statement::While {
                condition: Box::new(Conditional {
                    condition: self.visit_expression(&condition.condition, file)?,
                    branch: self.visit_statement(&condition.branch, file)?,
                }),
            },
            Statement::Loop { body } => Statement::Loop {
                body: Box::new(self.visit_statement(body, file)?),
            },
        })
    }

    fn visit_expression(
        &mut self,
        node: &Expression<SI, FI>,
        file: &FilePath,
    ) -> Result<Expression<SO, FO>, ParseError> {
        Ok(match node {
            Expression::Literal(literal) => Expression::Literal(*literal),
            Expression::CodeBlock(block) => Expression::CodeBlock(
                block
                    .iter()
                    .map(|statement| self.visit_statement(statement, file))
                    .collect::<Result<_, _>>()?,
            ),
            Expression::Variable(variable) => Expression::Variable(*variable),
            Expression::Assignment {
                declaration,
                variable,
                value,
            } => Expression::Assignment {
                declaration: *declaration,
                variable: *variable,
                value: Box::new(self.visit_expression(value, file)?),
            },
            Expression::FunctionCall {
                function,
                target,
                arguments,
            } => Expression::FunctionCall {
                function: self.visit_function_ref(function, file)?,
                target: target
                    .as_ref()
                    .map(|inner| Ok::<_, ParseError>(Box::new(self.visit_expression(inner, file)?)))
                    .transpose()?,
                arguments: arguments
                    .iter()
                    .map(|arg| Ok::<_, ParseError>(self.visit_expression(arg, file)?))
                    .collect::<Result<_, _>>()?,
            },
            Expression::CreateStruct {
                struct_target,
                fields,
            } => Expression::CreateStruct {
                struct_target: self.visit_type_ref(struct_target, file)?,
                fields: fields
                    .iter()
                    .map(|(name, value)| {
                        Ok::<_, ParseError>((*name, self.visit_expression(value, file)?))
                    })
                    .collect::<Result<_, _>>()?,
            },
        })
    }

    fn visit_function(&mut self, node: &Function<SI, FI>) -> Result<Function<SO, FO>, ParseError> {
        Ok(Function {
            name: node.name,
            file: node.file.clone(),
            modifiers: node.modifiers.clone(),
            body: self.visit_statement(&node.body, &node.file)?,
            parameters: node
                .parameters
                .iter()
                .map(|(name, ty)| {
                    Ok::<_, ParseError>((name.clone(), self.visit_type_ref(ty, &node.file)?))
                })
                .collect::<Result<_, _>>()?,
            return_type: node
                .return_type
                .as_ref()
                .map(|ty| self.visit_type_ref(ty, &node.file))
                .transpose()?,
        })
    }

    fn visit_type(&mut self, node: &Type<SI>) -> Result<Type<SO>, ParseError> {
        Ok(Type {
            name: node.name.clone(),
            file: node.file.clone(),
            modifiers: node.modifiers.clone(),
            data: match &node.data {
                TypeData::Struct { fields } => TypeData::Struct {
                    fields: fields
                        .iter()
                        .map(|(key, value)| {
                            Ok::<_, ParseError>((*key, self.visit_type_ref(value, &node.file)?))
                        })
                        .collect::<Result<_, _>>()?,
                },
            },
        })
    }
}

pub fn visit_syntax<SI, FI, SO, FO, V: Visitor<SI, FI, SO, FO>>(
    syntax: &Syntax<SI, FI>,
    visitor: &mut V,
) -> Result<Syntax<SO, FO>, Vec<ParseError>> {
    let functions = collect_results(
        syntax
            .functions
            .iter()
            .map(|function| visitor.visit_function(&function)),
    );

    let types = collect_results(syntax.types.iter().map(|ty| visitor.visit_type(ty)));

    match (functions, types) {
        (Ok(functions), Ok(types)) => Ok(Syntax {
            symbols: syntax.symbols.clone(),
            functions,
            types,
        }),
        (Err(functions), Err(types)) => Err(functions.into_iter().chain(types).collect()),
        (Err(functions), Ok(_)) => Err(functions),
        (Ok(_), Err(types)) => Err(types),
    }
}
