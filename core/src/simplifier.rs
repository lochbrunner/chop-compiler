use crate::ast::Ast;
use crate::token::{Token, TokenPayload};
use crate::CompilerError;

type Node = crate::ast::Node<Token>;

fn get2_int32(args: &Vec<Node>) -> Option<(i32, i32)> {
    if args.len() != 2 {
        None
    } else {
        let a = &args.iter().nth(0).unwrap().root.token;
        let b = &args.iter().nth(1).unwrap().root.token;
        match a {
            TokenPayload::Int32(va) => match b {
                TokenPayload::Int32(vb) => Some((*va, *vb)),
                _ => None,
            },
            _ => None,
        }
    }
}

fn simplify_node(node: Node) -> Result<Node, CompilerError> {
    let Node {
        root: Token { token, begin, end },
        args,
    } = node;
    let args = args
        .into_iter()
        .map(simplify_node)
        .collect::<Result<Vec<_>, CompilerError>>()?;

    if args.iter().any(|arg| {
        if let TokenPayload::Int32(_) = arg.root.token {
            false
        } else {
            true
        }
    }) {
        return Ok(Node {
            root: Token { token, begin, end },
            args,
        });
    }
    match token {
        TokenPayload::Add
        | TokenPayload::Subtract
        | TokenPayload::Multiply
        | TokenPayload::Divide
        | TokenPayload::Remainder => match get2_int32(&args) {
            None => Ok(Node {
                root: Token { token, begin, end },
                args,
            }),
            Some((a, b)) => {
                let token = match token {
                    TokenPayload::Add => TokenPayload::Int32(a + b),
                    TokenPayload::Subtract => TokenPayload::Int32(a - b),
                    TokenPayload::Multiply => TokenPayload::Int32(a * b),
                    TokenPayload::Divide => TokenPayload::Int32(a / b),
                    TokenPayload::Remainder => TokenPayload::Int32(a % b),
                    _ => token,
                };
                Ok(Node {
                    root: Token { token, begin, end },
                    args: vec![],
                })
            }
        },
        _ => Ok(Node {
            root: Token { token, begin, end },
            args,
        }),
    }
}

/// Simplifies constant expressions like 3+5
pub fn simplify(ast: Ast) -> Result<Ast, CompilerError> {
    Ok(Ast {
        statements: ast
            .statements
            .into_iter()
            .map(simplify_node)
            .collect::<Result<Vec<_>, CompilerError>>()?,
    })
}

#[cfg(test)]
mod specs {
    use super::*;
    use crate::token::TokenPayload::*;

    #[test]
    fn flat_operator() {
        let input = Ast {
            statements: vec![Node {
                root: Token::stub(Ident("stdout".to_string())),
                args: vec![Node {
                    root: Token::stub(Add),
                    args: vec![
                        Node {
                            root: Token::stub(Int32(3)),
                            args: vec![],
                        },
                        Node {
                            root: Token::stub(Multiply),
                            args: vec![
                                Node {
                                    root: Token::stub(Int32(5)),
                                    args: vec![],
                                },
                                Node {
                                    root: Token::stub(Int32(7)),
                                    args: vec![],
                                },
                            ],
                        },
                    ],
                }],
            }],
        };

        let actual = simplify(input);
        assert!(actual.is_ok());

        let actual = actual.unwrap();

        let expected = Ast {
            statements: vec![Node {
                root: Token::stub(Ident("stdout".to_string())),
                args: vec![Node {
                    root: Token::stub(Int32(38)),
                    args: vec![],
                }],
            }],
        };

        assert_eq!(actual, expected);
    }
}
