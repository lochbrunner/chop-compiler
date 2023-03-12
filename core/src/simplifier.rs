use crate::ast::IntegerProvider;
use crate::ast::{AstTokenPayload, DenseToken, Scope};
use crate::CompilerError;

type Node = crate::ast::Node<DenseToken>;

fn get2_int32(args: &[Node]) -> Option<(i32, i32)> {
    if args.len() != 2 {
        None
    } else {
        let a = &args.get(0).unwrap().root.payload;
        let b = &args.get(1).unwrap().root.payload;
        match a {
            AstTokenPayload::Integer(va) => match b {
                AstTokenPayload::Integer(vb) => Some((va.content as i32, vb.content as i32)),
                _ => None,
            },
            _ => None,
        }
    }
}

fn simplify_node(node: Node) -> Result<Node, CompilerError> {
    let Node {
        root: DenseToken {
            payload,
            loc,
            return_type,
        },
        args,
    } = node;
    let args = args
        .into_iter()
        .map(simplify_node)
        .collect::<Result<Vec<_>, CompilerError>>()?;

    let is_int32 = args.iter().any(|arg| {
        if let AstTokenPayload::Integer(_) = arg.root.payload {
            false
        } else {
            true
        }
    });

    if is_int32 {
        return Ok(Node {
            root: DenseToken {
                payload,
                loc,
                return_type,
            },
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
                root: DenseToken {
                    payload,
                    loc,
                    return_type,
                },
                args,
            }),
            Some((a, b)) => {
                let payload = match payload {
                    AstTokenPayload::Add => AstTokenPayload::Integer(IntegerProvider {
                        content: (a + b) as i64,
                    }),
                    AstTokenPayload::Subtract => AstTokenPayload::Integer(IntegerProvider {
                        content: (a - b) as i64,
                    }),
                    AstTokenPayload::Multiply => AstTokenPayload::Integer(IntegerProvider {
                        content: (a * b) as i64,
                    }),
                    AstTokenPayload::Divide => AstTokenPayload::Integer(IntegerProvider {
                        content: (a / b) as i64,
                    }),
                    AstTokenPayload::Remainder => AstTokenPayload::Integer(IntegerProvider {
                        content: (a % b) as i64,
                    }),
                    _ => payload,
                };
                Ok(Node {
                    root: DenseToken {
                        payload,
                        loc,
                        return_type,
                    },
                    args: vec![],
                })
            }
        },
        _ => Ok(Node {
            root: DenseToken {
                payload,
                loc,
                return_type,
            },
            args,
        }),
    }
}

/// Simplifies constant expressions like 3+5
pub fn simplify(scope: Scope<DenseToken>) -> Result<Scope<DenseToken>, CompilerError> {
    scope.map_into_statements(&simplify_node)
}

#[cfg(test)]
mod specs {
    use super::*;
    use crate::ast::{AstTokenPayload, AstTokenPayloadStub, Statement};
    // use crate::token::TokenPayload;

    fn create_int(value: i32) -> AstTokenPayload {
        AstTokenPayload::Integer(IntegerProvider {
            content: value as i64,
        })
    }

    #[test]
    fn flat_operator() {
        let input = Scope {
            statements: vec![Node {
                root: DenseToken::stub(AstTokenPayload::Symbol("stdout".to_string())),
                args: vec![Node {
                    root: DenseToken::stub(AstTokenPayload::Add),
                    args: vec![
                        Node {
                            root: DenseToken::stub(create_int(3)),
                            args: vec![],
                        },
                        Node {
                            root: DenseToken::stub(AstTokenPayload::Multiply),
                            args: vec![
                                Node {
                                    root: DenseToken::stub(create_int(5)),
                                    args: vec![],
                                },
                                Node {
                                    root: DenseToken::stub(create_int(7)),
                                    args: vec![],
                                },
                            ],
                        },
                    ],
                }],
            }]
            .into_iter()
            .map(Statement::InScope)
            .collect(),
        };

        let actual = simplify(input);
        assert_ok!(actual);

        let actual = actual.unwrap();

        let expected = Scope {
            statements: vec![Node {
                root: DenseToken::stub(AstTokenPayload::Symbol("stdout".to_string())),
                args: vec![Node {
                    root: DenseToken::stub(create_int(38)),
                    args: vec![],
                }],
            }]
            .into_iter()
            .map(Statement::InScope)
            .collect(),
        };

        assert_eq!(actual, expected);
    }
}
