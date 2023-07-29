use crate::ast::{AstTokenPayload, DenseToken, Node, Scope, SparseToken};
use crate::declaration::{Context, Declaration, Signature, Type, Visibility};
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

    (a, b)
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

    (a, b, c)
}

/// Does not support functions yet
fn specialize_declaration(
    args: Vec<SparseNode>,
    loc: Location,
    context: &mut Context,
) -> Result<DenseNode, CompilerError> {
    let (name, value, dtype) = match args.len() {
        2 => {
            let (name, value) = destruct_vector_2(args);
            let value = specialize_node(context, value, None)?;
            let dtype = value.root.return_type.clone();
            (name, value, dtype)
        }
        3 => {
            let (name, dtype, value) = destruct_vector_3(args);
            let dtype = Some(Type::from_sparse_token(&dtype.root));
            let value = specialize_node(context, value, dtype.clone())?;
            (name, value, dtype.unwrap())
        }
        _ => {
            return Err(loc.to_error(format!(
                "Expect Definition to have 2 or 3 arguments. Actually it has {}!",
                args.len()
            )))
        }
    };

    let payload = name.root.payload.clone();
    if let AstTokenPayload::Symbol(ref name_symbol) = payload {
        context
            .declarations
            .insert(name_symbol.to_owned(), Declaration::variable(dtype.clone()));
        let name = specialize_node(context, name, None)?;
        let args = vec![name, value];
        Ok(DenseNode {
            root: DenseToken {
                payload: AstTokenPayload::Define(Some(dtype), Visibility::Local),
                loc,
                return_type: Type::Void,
            },
            args,
        })
    } else {
        Err(loc.to_error(format!(
            "Expected identifier to by a symbol. Got {:?}",
            name.root.payload
        )))
    }
}

fn specialize_cast(
    args: Vec<SparseNode>,
    loc: Location,
    context: &mut Context,
) -> Result<DenseNode, CompilerError> {
    if args.len() != 2 {
        Err(loc.to_error(format!(
            "Expect cast to have two arguments. Got {}",
            args.len()
        )))
    } else {
        let (value, type_node) = destruct_vector_2(args);
        let dtype = Type::from_sparse_token(&type_node.root);
        let value = specialize_node(context, value, None)?;
        let cast = specialize_node(context, type_node, Some(Type::Type))?;
        let args = vec![value, cast];
        Ok(DenseNode {
            root: DenseToken {
                payload: AstTokenPayload::Cast,
                loc,
                return_type: dtype,
            },
            args,
        })
    }
}

pub fn specialize_binary_op(
    payload: AstTokenPayload,
    args: Vec<SparseNode>,
    loc: Location,
    expected: Option<Type>,
    context: &mut Context,
) -> Result<DenseNode, CompilerError> {
    if args.len() != 2 {
        Err(loc.to_error(format!(
            "Expect cast to have two arguments. Got {}",
            args.len()
        )))
    } else {
        let (a, b) = destruct_vector_2(args);

        let a = specialize_node(context, a, expected)?;
        let b = specialize_node(context, b, Some(a.root.return_type.clone()))?;
        let dtype = b.root.return_type.clone();

        let args = vec![a, b];
        Ok(DenseNode {
            root: DenseToken {
                payload,
                loc,
                return_type: dtype,
            },
            args,
        })
    }
}

fn specialize_symbol(
    ident: &str,
    args: Vec<SparseNode>,
    loc: Location,
    expected: Option<Type>,
    context: &mut Context,
) -> Result<DenseNode, CompilerError> {
    let decl = context.get_declaration(ident, &loc)?;
    if decl.req_args_count() != args.len() {
        return Err(loc.to_error(format!(
            "[S?]: Function {} expected {} arguments. Got {}",
            ident,
            decl.req_args_count(),
            args.len()
        )));
    }
    let decl_args = decl.signature.args.to_vec();

    let args = args
        .into_iter()
        .zip(decl_args.into_iter())
        .map(|(n, e)| specialize_node(context, n, e))
        .collect::<Result<Vec<_>, CompilerError>>()?;

    let arg_types = args
        .iter()
        .map(|arg| Some(arg.root.return_type.clone()))
        .collect();

    let decl = context.get_declaration(ident, &loc)?;

    // First use lambda then the return type
    // Change this later to better evaluation
    let dtype = match (decl.deduce_complete)(
        &decl.signature,
        &Signature {
            return_type: expected,
            args: arg_types,
        },
    ) {
        Ok(signature) => signature.return_type,
        Err(msg) => {
            if let Some(ref dtype) = decl.signature.return_type {
                dtype.clone()
            } else {
                return Err(loc.to_error(format!(
                    "[S?]: Signature of variable/function \"{}\" could not be resolved: {}",
                    ident, msg
                )));
            }
        }
    };

    Ok(DenseNode {
        root: DenseToken {
            payload: AstTokenPayload::Symbol(ident.to_owned()),
            loc,
            return_type: dtype,
        },
        args,
    })
}

fn specialize_node<'a>(
    context: &'a mut Context,
    node: SparseNode<'a>,
    expected: Option<Type>,
) -> Result<DenseNode, CompilerError> {
    let SparseNode {
        root: SparseToken {
            payload,
            loc,
            return_type,
        },
        args,
    } = node;
    match &payload {
        AstTokenPayload::Define(_, _) => specialize_declaration(args, loc, context),
        AstTokenPayload::Cast => specialize_cast(args, loc, context),
        AstTokenPayload::Add
        | AstTokenPayload::Subtract
        | AstTokenPayload::Multiply
        | AstTokenPayload::Divide
        | AstTokenPayload::Remainder => specialize_binary_op(payload, args, loc, expected, context),
        AstTokenPayload::FieldRef => specialize_binary_op(payload, args, loc, expected, context),
        AstTokenPayload::Symbol(ident) => specialize_symbol(ident, args, loc, expected, context),
        // What are the expected types
        AstTokenPayload::Integer(_) => {
            let expected = expected.unwrap_or(Type::Int32);
            let args = args
                .into_iter()
                .map(|s| (s, None))
                .map(|(n, e)| specialize_node(context, n, e))
                .collect::<Result<Vec<_>, CompilerError>>()?;
            // Find type child from parent
            let r_type = return_type(None).unwrap_or(expected);
            Ok(DenseNode {
                root: DenseToken {
                    payload,
                    loc,
                    return_type: r_type,
                },
                args,
            })
        }
        AstTokenPayload::Float(_) => {
            let expected = expected.unwrap_or(Type::Float32);
            let args = args
                .into_iter()
                .map(|s| (s, None))
                .map(|(n, e)| specialize_node(context, n, e))
                .collect::<Result<Vec<_>, CompilerError>>()?;
            // Find type child from parent
            let r_type = return_type(None).unwrap_or(expected);
            Ok(DenseNode {
                root: DenseToken {
                    payload,
                    loc,
                    return_type: r_type,
                },
                args,
            })
        }
        AstTokenPayload::Struct(obj) => {
            let args = vec![];
            let obj = obj.clone();
            Ok(DenseNode {
                root: DenseToken {
                    payload,
                    loc,
                    return_type: Type::Struct(obj),
                },
                args,
            })
        }
        _ => Err(loc.to_error(format!("[S2] Unexpected token {:?}", payload))),
    }
}

/// Takes an sparse AST. A sparse AST does not contain all type information for a symbol or function.
/// This function tries to figure out these types and fills gaps.
pub fn specialize<'a>(
    scope: Scope<SparseToken>,
    context: &mut Context,
) -> Result<Scope<DenseToken>, CompilerError> {
    scope.map_into_statements_mut(&mut |node| specialize_node(context, node, None))
}

#[cfg(test)]
mod specs {
    use super::*;
    use crate::ast::{
        AstTokenPayload::*, AstTokenPayloadStub, IntegerProvider, IntegerStub, StringStub,
    };
    use crate::declaration::Declaration;
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
        let sparse = Node {
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
        };

        let expected = Node {
            root: AstTokenPayloadStub::stub(Symbol("stdout".to_owned())),
            args: vec![Node::leaf(AstTokenPayloadStub::stub_typed(
                Integer(IntegerProvider { content: 42 }),
                Type::Int32,
            ))],
        };
        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::full_template_statement(1),
            },
            lower: None,
        };
        let dense = specialize_node(&mut context, sparse, None);
        assert_ok!(dense);
        assert_eq!(dense.unwrap(), expected);
    }

    #[test]
    fn declaration_cast() {
        // b: i8 := 5
        let sparse = Node {
            root: AstTokenPayloadStub::stub(Define(None, Visibility::Local)),
            args: vec![
                Node::leaf(StringStub::stub("b")),
                Node::leaf(StringStub::stub("i8")),
                Node::leaf(IntegerStub::stub(5)),
            ],
        };

        let mut context = Context::new();
        let dense = specialize_node(&mut context, sparse, None);
        assert_ok!(dense);
        let dense = dense.unwrap();

        let expected = Node {
            root: DenseToken {
                payload: Define(Some(Type::Int8), Visibility::Local),
                return_type: Type::Void,
                loc: Location::default(),
            },
            args: vec![
                Node::leaf(DenseToken {
                    payload: Symbol("b".to_owned()),
                    return_type: Type::Int8,
                    loc: Location::default(),
                }),
                Node::leaf(DenseToken {
                    payload: Integer(IntegerProvider { content: 5 }),
                    return_type: Type::Int8,
                    loc: Location::default(),
                }),
            ],
        };
        assert_eq!(dense, expected);
    }

    #[test]
    fn explicit_cast() {
        // b := 5 as i8
        let sparse = Node {
            root: AstTokenPayloadStub::stub(Define(None, Visibility::Local)),
            args: vec![
                Node::leaf(StringStub::stub("b")),
                Node {
                    root: AstTokenPayloadStub::stub(Cast),
                    args: vec![
                        Node::leaf(IntegerStub::stub(5)),
                        Node::leaf(StringStub::stub("i8")),
                    ],
                },
            ],
        };

        let mut context = Context {
            declarations: hashmap! {
                "i8".to_string() => Declaration::variable(Type::Type),
            },
            lower: None,
        };
        let dense = specialize_node(&mut context, sparse, None);
        assert_ok!(dense);
        let dense = dense.unwrap();

        let expected = Node {
            root: DenseToken {
                payload: Define(Some(Type::Int8), Visibility::Local),
                return_type: Type::Void,
                loc: Location::default(),
            },
            args: vec![
                Node::leaf(DenseToken {
                    payload: Symbol("b".to_owned()),
                    return_type: Type::Int8,
                    loc: Location::default(),
                }),
                Node {
                    root: DenseToken {
                        payload: Cast,
                        return_type: Type::Int8,
                        loc: Location::default(),
                    },
                    args: vec![
                        Node::leaf(DenseToken {
                            payload: Integer(IntegerProvider { content: 5 }),
                            return_type: Type::Int32,
                            loc: Location::default(),
                        }),
                        Node::leaf(DenseToken {
                            payload: Symbol("i8".to_owned()),
                            return_type: Type::Type,
                            loc: Location::default(),
                        }),
                    ],
                },
            ],
        };

        assert_eq!(dense, expected);
    }

    #[test]
    fn use_declaration_table() {
        // a := 5 as i8
        // b := a as i8
        let sparse = vec![
            Node {
                root: AstTokenPayloadStub::stub(Define(None, Visibility::Local)),
                args: vec![
                    Node::leaf(StringStub::stub("a")),
                    Node {
                        root: AstTokenPayloadStub::stub(Cast),
                        args: vec![
                            Node::leaf(IntegerStub::stub(5)),
                            Node::leaf(StringStub::stub("i8")),
                        ],
                    },
                ],
            },
            Node {
                root: AstTokenPayloadStub::stub(Define(None, Visibility::Local)),
                args: vec![
                    Node::leaf(StringStub::stub("b")),
                    Node {
                        root: AstTokenPayloadStub::stub(Cast),
                        args: vec![
                            Node::leaf(StringStub::stub("a")),
                            Node::leaf(StringStub::stub("i8")),
                        ],
                    },
                ],
            },
        ];

        let mut context = Context {
            declarations: hashmap! {
                "a".to_string() => Declaration::variable(Type::Int8),
                "i8".to_string() => Declaration::variable(Type::Type),
            },
            lower: None,
        };

        let dense = sparse
            .into_iter()
            .map(|sparse| specialize_node(&mut context, sparse, None))
            .collect::<Vec<_>>();

        let dense = dense.into_iter().map(|d| d.unwrap()).collect::<Vec<_>>();

        let expected = [
            Node {
                root: DenseToken {
                    payload: Define(Some(Type::Int8), Visibility::Local),
                    return_type: Type::Void,
                    loc: Location::default(),
                },
                args: vec![
                    Node::leaf(DenseToken {
                        payload: Symbol("a".to_owned()),
                        return_type: Type::Int8,
                        loc: Location::default(),
                    }),
                    Node {
                        root: DenseToken {
                            payload: Cast,
                            return_type: Type::Int8,
                            loc: Location::default(),
                        },
                        args: vec![
                            Node::leaf(DenseToken {
                                payload: Integer(IntegerProvider { content: 5 }),
                                return_type: Type::Int32,
                                loc: Location::default(),
                            }),
                            Node::leaf(DenseToken {
                                payload: Symbol("i8".to_owned()),
                                return_type: Type::Type,
                                loc: Location::default(),
                            }),
                        ],
                    },
                ],
            },
            Node {
                root: DenseToken {
                    payload: Define(Some(Type::Int8), Visibility::Local),
                    return_type: Type::Void,
                    loc: Location::default(),
                },
                args: vec![
                    Node::leaf(DenseToken {
                        payload: Symbol("b".to_owned()),
                        return_type: Type::Int8,
                        loc: Location::default(),
                    }),
                    Node {
                        root: DenseToken {
                            payload: Cast,
                            return_type: Type::Int8,
                            loc: Location::default(),
                        },
                        args: vec![
                            Node::leaf(DenseToken {
                                payload: Symbol("a".to_owned()),
                                return_type: Type::Int8,
                                loc: Location::default(),
                            }),
                            Node::leaf(DenseToken {
                                payload: Symbol("i8".to_owned()),
                                return_type: Type::Type,
                                loc: Location::default(),
                            }),
                        ],
                    },
                ],
            },
        ];

        assert_eq!(&dense, &expected);
    }

    #[test]
    fn milestone_5_line_2() {
        // b: i8 := a as i8 + 5

        let sparse = Node {
            root: AstTokenPayloadStub::stub(Define(None, Visibility::Local)),
            args: vec![
                Node::leaf(StringStub::stub("b")),
                Node::leaf(StringStub::stub("i8")),
                Node {
                    root: AstTokenPayloadStub::stub(Add),
                    args: vec![
                        Node {
                            root: AstTokenPayloadStub::stub(Cast),
                            args: vec![
                                Node::leaf(SparseToken {
                                    payload: AstTokenPayload::Symbol("a".to_owned()),
                                    return_type: Rc::new(&|_| Some(Type::Int32)),
                                    loc: Default::default(),
                                }),
                                Node::leaf(StringStub::stub("i8")),
                            ],
                        },
                        Node::leaf(IntegerStub::stub(5)),
                    ],
                },
            ],
        };

        let mut context = Context {
            declarations: hashmap! {
                "a".to_string() => Declaration::variable(Type::Int8),
                "i8".to_string() => Declaration::variable(Type::Type),
            },
            lower: None,
        };
        let dense = specialize_node(&mut context, sparse, None);
        assert_ok!(dense);
        let dense = dense.unwrap();

        let expected = Node {
            root: DenseToken {
                payload: Define(Some(Type::Int8), Visibility::Local),
                return_type: Type::Void,
                loc: Location::default(),
            },
            args: vec![
                Node::leaf(DenseToken {
                    payload: Symbol("b".to_owned()),
                    return_type: Type::Int8,
                    loc: Location::default(),
                }),
                Node {
                    root: DenseToken {
                        payload: Add,
                        return_type: Type::Int8,
                        loc: Location::default(),
                    },
                    args: vec![
                        Node {
                            root: DenseToken {
                                payload: Cast,
                                return_type: Type::Int8,
                                loc: Location::default(),
                            },
                            args: vec![
                                Node::leaf(DenseToken {
                                    payload: Symbol("a".to_owned()),
                                    return_type: Type::Int8,
                                    loc: Location::default(),
                                }),
                                Node::leaf(DenseToken {
                                    payload: Symbol("i8".to_owned()),
                                    return_type: Type::Type,
                                    loc: Location::default(),
                                }),
                            ],
                        },
                        Node::leaf(DenseToken {
                            payload: Integer(IntegerProvider { content: 5 }),
                            return_type: Type::Int8,
                            loc: Location::default(),
                        }),
                    ],
                },
            ],
        };

        assert_eq!(dense, expected);
    }
}
