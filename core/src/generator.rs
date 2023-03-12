//! This module is deprecated, and will be replaced by meta programming later.
use crate::ast::{AstTokenPayload, Node, Scope, SparseToken};
use crate::CompilerError;

#[cfg(test)]
use crate::ast::DenseToken;

fn generate_sparse_node(statement: Node<SparseToken>) -> Result<Node<SparseToken>, CompilerError> {
    match statement.root.payload {
        AstTokenPayload::Pipe => Ok(Node {
            root: statement.args[1].root.clone(),
            args: vec![statement.args[0].clone()],
        }),
        AstTokenPayload::Symbol(_) => Ok(statement), // Function Call
        AstTokenPayload::DefineLocal(_) => Ok(statement),
        _ => Err(CompilerError {
            location: statement.root.loc.clone(),
            msg: format!(
                "Generator Error: Token {:?} is not implemented yet!",
                statement.root.payload
            ),
        }),
    }
}

pub fn generate_sparse(scope: Scope<SparseToken>) -> Result<Scope<SparseToken>, CompilerError> {
    scope.map_into_statements(&generate_sparse_node)
}

/// Fills out the macros and runs all the custom compiler stuff.
#[cfg(test)]
pub fn generate(ast: Scope<DenseToken>) -> Result<Scope<DenseToken>, CompilerError> {
    ast.map_into_statements(
        &|statement: Node<DenseToken>| match statement.root.payload {
            AstTokenPayload::Pipe => Ok(Node {
                root: statement.args[1].root.clone(),
                args: vec![statement.args[0].clone()],
            }),
            AstTokenPayload::Symbol(_) => Ok(statement), // Function Call
            AstTokenPayload::DefineLocal(_) => Ok(statement),
            _ => Err(CompilerError {
                location: statement.root.loc.clone(),
                msg: format!(
                    "Generator Error: Token {:?} is not implemented yet!",
                    statement.root.payload
                ),
            }),
        },
    )
}

#[cfg(test)]
mod specs {
    use super::*;
    use crate::ast::{DenseToken, IntegerProvider, Statement};
    use crate::declaration::Type;
    use crate::error::Location;

    #[test]
    fn milestone_1() {
        let input = Scope {
            statements: vec![Statement::InScope(Node {
                root: DenseToken {
                    payload: AstTokenPayload::Pipe,
                    return_type: Type::Int32,
                    loc: Location {
                        line: 3,
                        begin: 31,
                        end: 32,
                    },
                },
                args: vec![
                    Node::leaf(DenseToken {
                        payload: AstTokenPayload::Integer(IntegerProvider { content: 42 }),
                        return_type: Type::Int32,
                        loc: Location {
                            line: 3,
                            begin: 28,
                            end: 30,
                        },
                    }),
                    Node::leaf(DenseToken {
                        payload: AstTokenPayload::Symbol("stdout".to_owned()),
                        return_type: Type::Int32,
                        loc: Location {
                            line: 3,
                            begin: 33,
                            end: 39,
                        },
                    }),
                ],
            })],
        };

        let actual = generate(input);
        assert_ok!(actual);
        let actual = actual.unwrap();
        let expected = Scope {
            statements: vec![Statement::InScope(Node {
                root: DenseToken {
                    payload: AstTokenPayload::Symbol("stdout".to_owned()),
                    return_type: Type::Int32,
                    loc: Location {
                        line: 3,
                        begin: 33,
                        end: 39,
                    },
                },
                args: vec![Node::leaf(DenseToken {
                    payload: AstTokenPayload::Integer(IntegerProvider { content: 42 }),
                    return_type: Type::Int32,
                    loc: Location {
                        line: 3,
                        begin: 28,
                        end: 30,
                    },
                })],
            })],
        };
        assert_eq!(actual, expected);
    }
}
