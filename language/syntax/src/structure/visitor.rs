use crate::code::expression::Expression;
use crate::code::statement::{Conditional, Statement};
use crate::structure::function::Function;
use crate::Syntax;

pub trait Visitor<SI, FI, SO, FO> {
    fn visit_type(&mut self, node: &SI) -> SO;

    fn visit_function_ref(&mut self, node: &FI) -> FO;

    fn visit_statement(&mut self, node: &Statement<SI, FI>) -> Statement<SO, FO> {
        match node {
            Statement::Expression(expression) => {
                Statement::Expression(self.visit_expression(expression))
            }
            Statement::Return => Statement::Return,
            Statement::Break => Statement::Break,
            Statement::Continue => Statement::Continue,
            Statement::If {
                conditions,
                else_branch,
            } => Statement::If {
                conditions: conditions.iter().map(|condition| Conditional {
                    condition: self.visit_expression(&condition.condition),
                    branch: self.visit_statement(&condition.branch),
                }).collect(),
                else_branch: else_branch
                    .as_ref()
                    .map(|branch| Box::new(self.visit_statement(branch))),
            },
            Statement::For { iterator, body } => Statement::For {
                iterator: Box::new(self.visit_expression(iterator)),
                body: Box::new(self.visit_statement(body)),
            },
            Statement::While { condition } => Statement::While {
                condition: Box::new(Conditional {
                    condition: self.visit_expression(&condition.condition),
                    branch: self.visit_statement(&condition.branch),
                }),
            },
            Statement::Loop { body } => Statement::Loop {
                body: Box::new(self.visit_statement(body)),
            }
        }
    }

    fn visit_expression(&mut self, node: &Expression<SI, FI>) -> Expression<SO, FO> {
        match node {
            Expression::Literal(literal) => Expression::Literal(*literal),
            Expression::CodeBlock(block) => Expression::CodeBlock(
                block
                    .iter()
                    .map(|statement| self.visit_statement(statement))
                    .collect(),
            ),
            Expression::Variable(variable) => Expression::Variable(*variable),
            Expression::Assignment {
                declaration,
                variable,
                value,
            } => Expression::Assignment {
                declaration: *declaration,
                variable: *variable,
                value: Box::new(self.visit_expression(value)),
            },
            Expression::FunctionCall {
                function,
                target,
                arguments,
            } => Expression::FunctionCall {
                function: self.visit_function_ref(function),
                target: target.as_ref().map(|inner| Box::new(self.visit_expression(inner))),
                arguments: arguments
                    .iter()
                    .map(|arg| self.visit_expression(arg))
                    .collect(),
            },
            Expression::CreateStruct {
                struct_target,
                fields,
            } => Expression::CreateStruct {
                struct_target: self.visit_type(struct_target),
                fields: fields
                    .iter()
                    .map(|(name, value)| (*name, self.visit_expression(value)))
                    .collect(),
            },
        }
    }

    fn visit_function(&mut self, node: &Function<SI, FI>) -> Function<SO, FO> {
        Function {
            file: node.file.clone(),
            modifiers: node.modifiers.clone(),
            name: node.name,
            return_type: node.return_type.as_ref().map(|ty| self.visit_type(ty)),
            body: self.visit_statement(&node.body),
            parameters: node
                .parameters
                .iter()
                .map(|(name, ty)| (name.clone(), self.visit_type(ty)))
                .collect(),
        }
    }
}

pub fn visit_syntax<SI, FI, SO, FO, V: Visitor<SI, FI, SO, FO>>(syntax: &Syntax<SI, FI>, visitor: &mut V) -> Syntax<SO, FO> {
    let functions = syntax
        .functions
        .iter()
        .map(|function| visitor.visit_function(&function))
        .collect();
    let types = syntax
        .types
        .iter()
        .map(|ty| visitor.visit_type(&ty))
        .collect();

    Syntax {
        symbols: syntax.symbols.clone(),
        functions,
        types,
    }
}
