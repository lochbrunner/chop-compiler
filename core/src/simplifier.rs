use crate::ast::{Ast, SparseToken, AstTokenPayload};
use crate::token::{Token, TokenPayload};
use crate::CompilerError;

type Node = crate::ast::Node<SparseToken>;

fn get2_int32(args: &[Node]) -> Option<(i32, i32)> {
    if args.len() != 2 {
        None
    } else {
        let a = &args.get(0).unwrap().root.payload;
        let b = &args.get(1).unwrap().root.payload;
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
        root: SparseToken { payload, loc, return_type },
        args,
    } = node;
    let args = args
        .into_iter()
        .map(simplify_node)
        .collect::<Result<Vec<_>, CompilerError>>()?;

    let is_int32 = args.iter().any(|arg| {
        if let AstTokenPayload::Integer = arg.root.payload {
            false
        } else {
            true
        }
    });

    if is_int32 {
        return Ok(Node {
            root: SparseToken { payload, loc, return_type },
            args,
        });
    }
    match payload {
        AstTokenPayload::Add
        | AstTokenPayload::Subtract
        | AstTokenPayload::Multiply
        | AstTokenPayload::Divide
        | AstTokenPayload::Remainder => match get2_int32(&args) {
            None => Ok(Node {
                root: SparseToken { payload, loc, return_type },
                args,
            }),
            Some((a, b)) => {
                let payload = match payload {
                    AstTokenPayload::Add => AstTokenPayload::Int32(a + b),
                    AstTokenPayload::Subtract => AstTokenPayload::Int32(a - b),
                    AstTokenPayload::Multiply => AstTokenPayload::Int32(a * b),
                    AstTokenPayload::Divide => AstTokenPayload::Int32(a / b),
                    AstTokenPayload::Remainder => AstTokenPayload::Int32(a % b),
                    _ => payload,
                };
                Ok(Node {
                    root: SparseToken { payload, loc, return_type },
                    args: vec![],
                })
            }
        },
        _ => Ok(Node {
            root: SparseToken { payload, loc, return_type },
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
                root: SparseToken::stub(Ident("stdout".to_string())),
                args: vec![Node {
                    root: SparseToken::stub(Add),
                    args: vec![
                        Node {
                            root: SparseToken::stub(Int32(3)),
                            args: vec![],
                        },
                        Node {
                            root: SparseToken::stub(Multiply),
                            args: vec![
                                Node {
                                    root: SparseToken::stub(Int32(5)),
                                    args: vec![],
                                },
                                Node {
                                    root: SparseToken::stub(Int32(7)),
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
                root: SparseToken::stub(Ident("stdout".to_string())),
                args: vec![Node {
                    root: SparseToken::stub(Int32(38)),
                    args: vec![],
                }],
            }],
        };

        assert_eq!(actual, expected);
    }
}
