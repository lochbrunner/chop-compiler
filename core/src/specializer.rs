use crate::ast::{AstTokenPayload, DenseAst, DenseToken, Node, SparseAst, SparseToken};
use crate::declaration::Type;
use crate::error::{Locatable, Location};
use crate::CompilerError;

type SparseNode<'a> = Node<SparseToken>;
type DenseNode = Node<DenseToken>;

impl<'a> Locatable for SparseNode<'a> {
    fn get_loc(&self) -> &Location {
        &self.root.loc
    }
}

fn destruct_vector_2<T>(vec: Vec<T>) -> (T, T)
where
    T: Default,
{
    let mut a = T::default();
    let mut b = T::default();
    for (i, item) in vec.into_iter().enumerate() {
        match i {
            0 => a = item,
            1 => b = item,
            _ => (),
        }
    }

    return (a, b);
}

fn destruct_vector_3<T>(vec: Vec<T>) -> (T, T, T)
where
    T: Default,
{
    let mut a = T::default();
    let mut b = T::default();
    let mut c = T::default();
    for (i, item) in vec.into_iter().enumerate() {
        match i {
            0 => a = item,
            1 => b = item,
            2 => c = item,
            _ => (),
        }
    }

    return (a, b, c);
}

// fn specialize_declaration<'a>() -> impl FnMut(SparseNode<'a>) -> Result<DenseNode, CompilerError> {
//     |node| {
//         let SparseNode {
//             root:
//                 SparseToken {
//                     payload,
//                     loc,
//                     return_type,
//                 },
//             args,
//         } = node;
//     }
// }

fn specialize_declaration<'a>(
    args: Vec<SparseNode>,
    loc: Location,
) -> Result<DenseNode, CompilerError> {
    match args.len() {
        2 => {
            // variable name, value
            let (name, value) = destruct_vector_2(args);
            let dtype = Some(Type::Int32);
            let args = vec![
                specialize_node(Some(Type::Void))(name)?,
                specialize_node(dtype.clone())(value)?,
            ];
            Ok(DenseNode {
                root: DenseToken {
                    payload: AstTokenPayload::DefineLocal(dtype),
                    loc,
                    return_type: Type::Void,
                },
                args,
            })
        }
        3 => {
            // variable name, type, value
            let (name, dtype, value) = destruct_vector_3(args);
            let dtype = Some(Type::from_sparse_token(&dtype.root));
            let args = vec![
                specialize_node(Some(Type::Void))(name)?,
                specialize_node(dtype.clone())(value)?,
            ];
            Ok(DenseNode {
                root: DenseToken {
                    payload: AstTokenPayload::DefineLocal(dtype),
                    loc,
                    return_type: Type::Void,
                },
                args,
            })
        }
        _ => Err(loc.to_error(format!(
            "Expect Definition to have 2 or 3 arguments. Actually it has {}!",
            args.len()
        ))),
    }
}

fn specialize_node<'a>(
    expected: Option<Type>,
) -> impl FnMut(SparseNode<'a>) -> Result<DenseNode, CompilerError> {
    let expected = expected.unwrap_or(Type::Int32);
    move |node| {
        let SparseNode {
            root:
                SparseToken {
                    payload,
                    loc,
                    return_type,
                },
            args,
        } = node;

        match &payload {
            AstTokenPayload::DefineLocal(_) => specialize_declaration(args, loc),
            // What are the expected types
            // For now assume each is a Int32
            _ => {
                let args = args
                    .into_iter()
                    .map(specialize_node(Some(Type::Int32)))
                    .collect::<Result<Vec<_>, CompilerError>>()?;
                // Find type child from parent
                let r_type = return_type(None).unwrap_or(expected.clone());
                Ok(DenseNode {
                    root: DenseToken {
                        payload,
                        loc,
                        return_type: r_type,
                    },
                    args,
                })
            }
        }
    }
}

/// This function tries to find out the actual concrete types in for each node in the AST
pub fn specialize(ast: SparseAst) -> Result<DenseAst, CompilerError> {
    Ok(DenseAst {
        statements: ast
            .statements
            .into_iter()
            .map(specialize_node(None))
            .collect::<Result<Vec<_>, CompilerError>>()?,
    })
}

#[cfg(test)]
mod specs {
    use super::*;
    use crate::ast::{
        AstTokenPayload::*, AstTokenPayloadStub, IntegerProvider, IntegerStub, StringStub,
    };
    use crate::error::Location;
    use std::rc::Rc;

    fn filter(possibilities: &'static [Type]) -> impl Fn(Option<Type>) -> Option<Type> {
        move |incoming| match incoming {
            None => None,
            Some(t) => {
                if possibilities.contains(&t) {
                    Some(t)
                } else {
                    None
                }
            }
        }
    }

    #[test]
    fn milestone_1() {
        let sparse = SparseAst {
            statements: vec![Node {
                root: SparseToken {
                    payload: Symbol("stdout".to_owned()),
                    return_type: Rc::new(|_| Some(Type::Void)),
                    loc: Default::default(),
                },
                args: vec![Node::leaf(SparseToken {
                    payload: Integer(IntegerProvider { content: 42 }),
                    return_type: Rc::new(filter(&[Type::Int32])),
                    loc: Default::default(),
                })],
            }],
        };

        let expected = DenseAst {
            statements: vec![Node {
                root: AstTokenPayloadStub::stub(Symbol("stdout".to_owned())),
                args: vec![Node::leaf(AstTokenPayloadStub::stub_typed(
                    Integer(IntegerProvider { content: 42 }),
                    Type::Int32,
                ))],
            }],
        };

        let dense = specialize(sparse);
        assert!(dense.is_ok());
        assert_eq!(dense.unwrap(), expected);
    }

    #[test]
    fn declaration_cast() {
        // b: i8 := 5
        let sparse = SparseAst {
            statements: vec![Node {
                root: AstTokenPayloadStub::stub(DefineLocal(None)),
                args: vec![
                    Node::leaf(StringStub::stub("b")),
                    Node::leaf(StringStub::stub("i8")),
                    Node::leaf(IntegerStub::stub(5)),
                ],
            }],
        };

        let dense = specialize(sparse);
        assert!(dense.is_ok());
        let dense = dense.unwrap();

        let expected = DenseAst {
            statements: vec![Node {
                root: DenseToken {
                    payload: DefineLocal(Some(Type::Int8)),
                    return_type: Type::Void,
                    loc: Location::default(),
                },
                args: vec![
                    Node::leaf(DenseToken {
                        payload: Symbol("b".to_owned()),
                        return_type: Type::Void,
                        loc: Location::default(),
                    }),
                    Node::leaf(DenseToken {
                        payload: Integer(IntegerProvider { content: 5 }),
                        return_type: Type::Int8,
                        loc: Location::default(),
                    }),
                ],
            }],
        };
        assert_eq!(dense, expected);
    }

    #[test]
    fn milestone_5_line_2() {
        let sparse = SparseAst {
            statements: vec![Node {
                root: AstTokenPayloadStub::stub(DefineLocal(None)),
                args: vec![
                    Node::leaf(StringStub::stub("b")),
                    Node::leaf(StringStub::stub("i8")),
                    Node {
                        root: AstTokenPayloadStub::stub(Add),
                        args: vec![
                            Node {
                                root: AstTokenPayloadStub::stub(Cast),
                                args: vec![
                                    Node::leaf(StringStub::stub("a")),
                                    Node::leaf(StringStub::stub("i8")),
                                ],
                            },
                            Node::leaf(IntegerStub::stub(5)),
                        ],
                    },
                ],
            }],
        };

        let dense = specialize(sparse);
        assert!(dense.is_ok());
        let dense = dense.unwrap();

        dbg!(dense);

        let expected = DenseAst {
            statements: vec![Node {
                root: AstTokenPayloadStub::stub_typed(DefineLocal(None), Type::Void),
                args: vec![
                    Node::leaf(AstTokenPayloadStub::stub_typed(
                        Symbol("stdout".to_owned()),
                        Type::Int8,
                    )),
                    // Node::leaf(AstTokenPayloadStub::stub_typed(
                    //     Symbol("i8".to_owned()),
                    //     Type::Int8,
                    // )),
                    Node {
                        root: DenseToken {
                            payload: Add,
                            return_type: Type::Int32,
                            loc: Location::default(),
                        },
                        args: vec![
                            Node {
                                root: DenseToken {
                                    payload: Cast,
                                    return_type: Type::Int32,
                                    loc: Location::default(),
                                },
                                args: vec![
                                    Node::leaf(DenseToken {
                                        payload: Symbol("a".to_owned()),
                                        return_type: Type::Int32,
                                        loc: Location::default(),
                                    }),
                                    Node::leaf(DenseToken {
                                        payload: Symbol("i8".to_owned()),
                                        return_type: Type::Int32,
                                        loc: Location::default(),
                                    }),
                                ],
                            },
                            Node::leaf(DenseToken {
                                payload: Integer(IntegerProvider { content: 5 }),
                                return_type: Type::Int32,
                                loc: Location::default(),
                            }),
                        ],
                    },
                ],
            }],
        };
    }
}
