use crate::compiler::ast::{Ast, Node, Statement};
use crate::compiler::token::TokenPayload;
use crate::compiler::CompilerError;

/// Fills out the macros and runs all the custom compiler stuff.
pub fn generate(ast: Ast) -> Result<Ast, CompilerError> {
    let statements = ast
        .statements
        .into_iter()
        .map(|statement| match statement.root.root.token {
            TokenPayload::Pipe => Ok(Statement {
                root: Node {
                    root: statement.root.args[1].root.clone(),
                    args: vec![statement.root.args[0].clone()],
                },
            }),
            TokenPayload::Ident(_) => Ok(statement), // Function Call
            _ => Err(CompilerError {
                location: statement.root.root.begin.clone(),
                msg: format!(
                    "Generator Error: Token {:?} is not implemented yet!",
                    statement.root.root.token
                ),
            }),
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Ast { statements })
}

#[cfg(test)]
mod specs {
    use super::*;
    use crate::compiler::token::{Location, Token, TokenPayload};

    #[test]
    fn milestone_1() {
        let input = Ast {
            statements: vec![Statement {
                root: Node {
                    root: Token {
                        token: TokenPayload::Pipe,
                        begin: Location {
                            line: 3,
                            offset: 31,
                        },
                        end: Location {
                            line: 3,
                            offset: 32,
                        },
                    },
                    args: vec![
                        Node::new(Token {
                            token: TokenPayload::Int32(42),
                            begin: Location {
                                line: 3,
                                offset: 28,
                            },
                            end: Location {
                                line: 3,
                                offset: 30,
                            },
                        }),
                        Node::new(Token {
                            token: TokenPayload::Ident("stdout".to_owned()),
                            begin: Location {
                                line: 3,
                                offset: 33,
                            },
                            end: Location {
                                line: 3,
                                offset: 39,
                            },
                        }),
                    ],
                },
            }],
        };

        let actual = generate(input);
        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let expected = Ast {
            statements: vec![Statement {
                root: Node {
                    root: Token {
                        token: TokenPayload::Ident("stdout".to_owned()),
                        begin: Location {
                            line: 3,
                            offset: 33,
                        },
                        end: Location {
                            line: 3,
                            offset: 39,
                        },
                    },
                    args: vec![Node::new(Token {
                        token: TokenPayload::Int32(42),
                        begin: Location {
                            line: 3,
                            offset: 28,
                        },
                        end: Location {
                            line: 3,
                            offset: 30,
                        },
                    })],
                },
            }],
        };
        assert_eq!(actual, expected);
    }
}
