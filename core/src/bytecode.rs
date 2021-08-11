use crate::ast::{AstTokenPayload, DenseAst, DenseToken, Node};
use crate::declaration::{Context, Signature, Type};
use crate::error::{CompilerError, Location, ToCompilerError};
use std::collections::HashMap;

#[derive(PartialEq, Debug, Clone)]
pub enum ByteCode {
    StdOut, // For now hard-coded
    Call2(String, Type, Type, Type),
    PushInt8(i8),
    PushInt16(i16),
    PushInt32(i32),
    PushInt64(i64),
    Add(Type),
    Sub(Type),
    Mul(Type),
    Div(Type),
    Rem(Type),
    Alloca(Type),
    CastInt(Type, Type), // (From, To) See https://llvm.org/docs/LangRef.html#sext-to-instruction
    Store(Type, usize),
    Load(Type, usize),
}

fn get_build_ins(ident: &str) -> Option<ByteCode> {
    match ident {
        "stdout" => Some(ByteCode::StdOut),
        _ => None,
    }
}

fn get_common_type_2(
    name: &str,
    location: &Location,
    args: &[Type],
) -> Result<Type, CompilerError> {
    if args.len() != 2 {
        Err(CompilerError {
            location: location.clone(),
            msg: format!(
                "Exporter Error: Operator/function {} expected 2 arguments but got {}",
                name,
                args.len()
            ),
        })
    } else if args.get(0).unwrap() != args.get(1).unwrap() {
        Err(CompilerError {
            location: location.clone(),
            msg: format!(
                "Exporter Error: Arguments of operator/function \"{}\" expected are different. {:?} and {:?}",
                name,
                args.get(0).unwrap(), args.get(1).unwrap()
            ),
        })
    } else {
        Ok(args.get(0).unwrap().clone())
    }
}

fn unroll_node<'a>(
    register_map: &mut HashMap<&'a str, usize>,
    context: &Context,
    node: &'a Node<DenseToken>,
    bytecode: &mut Vec<ByteCode>,
) -> Result<Type, CompilerError> {
    let mut unroll_node = |node| unroll_node(register_map, context, node, bytecode);
    match node.root.payload {
        AstTokenPayload::Add
        | AstTokenPayload::Subtract
        | AstTokenPayload::Multiply
        | AstTokenPayload::Divide
        | AstTokenPayload::Remainder => {
            let arg_types = node
                .args
                .iter()
                .map(unroll_node)
                .collect::<Result<Vec<_>, CompilerError>>()?;
            let needed_type = get_common_type_2(
                &format!("{:?}", node.root.payload),
                &node.root.loc,
                &arg_types,
            )?;
            let return_type = needed_type.clone();
            bytecode.push(match node.root.payload {
                AstTokenPayload::Add => ByteCode::Add(needed_type),
                AstTokenPayload::Subtract => ByteCode::Sub(needed_type),
                AstTokenPayload::Multiply => ByteCode::Mul(needed_type),
                AstTokenPayload::Divide => ByteCode::Div(needed_type),
                AstTokenPayload::Remainder => ByteCode::Rem(needed_type),
                _ => ByteCode::Add(needed_type),
            });
            Ok(return_type)
        }
        AstTokenPayload::Integer(ref provider) => {
            // TODO: get value of correct type
            // let v = provider.get_i32().convert(&node.root.loc)?;
            let v = provider.content as i32;
            bytecode.push(ByteCode::PushInt32(v));
            Ok(Type::Int32)
        }
        AstTokenPayload::Symbol(ref ident) => {
            let declaration = context.get_declaration(ident, &node.root.loc)?;
            let arg_types = node
                .args
                .iter()
                .map(unroll_node)
                .collect::<Result<Vec<_>, CompilerError>>()?;
            let signature = match (declaration.deduce_complete)(
                &declaration.signature,
                &Signature {
                    return_type: None,
                    args: arg_types.iter().cloned().map(Some).collect::<Vec<_>>(),
                },
            ) {
                Ok(signature) => signature,
                Err(msg) => {
                    return Err(CompilerError::from_token::<DenseToken>(
                        &node.root,
                        format!(
                            "Signature of variable/function \"{}\" could not be resolved: {}",
                            ident, msg
                        ),
                    ))
                }
            };
            if declaration.req_args_count() == 0 {
                if let Some(index) = register_map.get::<str>(ident) {
                    bytecode.push(ByteCode::Load(signature.return_type.clone(), *index));
                } else {
                    return Err(CompilerError::from_token::<DenseToken>(
                        &node.root,
                        format!("No Variable with name {} found in register", ident),
                    ));
                }
            } else {
                let Signature { return_type, args } = signature.clone();
                // Get build-in functions
                match get_build_ins(&ident) {
                    Some(instruction) => bytecode.push(instruction),
                    None => {
                        if arg_types.len() != 2 {
                            return Err(CompilerError::from_token::<DenseToken>(
                                &node.root,
                                format!("No Function {} expects {} arguments, but only 2 arguments are supported yet.", ident, declaration.req_args_count()),
                            ));
                        }
                        bytecode.push(ByteCode::Call2(
                            ident.clone(),
                            return_type.clone(),
                            args.get(0).unwrap().clone(),
                            args.get(1).unwrap().clone(),
                        ));
                    }
                }
            }
            Ok(signature.return_type)
        }
        AstTokenPayload::DefineLocal => {
            // Compile argument
            if node.args.len() != 2 && node.args.len() != 3 {
                // TODO: Handle Type declaration
                return Err(CompilerError::from_token::<DenseToken>(
                    &node.root,
                    format!(
                        "Exporter Error: DefineLocal need two arguments but got {}",
                        node.args.len()
                    ),
                ));
            }
            let has_type = node.args.len() == 3;
            let _arg = unroll_node(
                node.args
                    .get(if has_type { 2 } else { 1 })
                    .expect("Definition"),
            )?;

            let decl_type = if has_type {
                Type::from_dense_token(&node.args.get(1).expect("Type Declaration").root)
            } else {
                Type::Int32
            };
            bytecode.push(ByteCode::Alloca(decl_type.clone()));
            let index = register_map.len();
            bytecode.push(ByteCode::Store(decl_type, index));
            register_map.insert(
                &node
                    .args
                    .get(0)
                    .expect("Definition")
                    .root
                    .payload
                    .get_ident()
                    .expect("ident"),
                index,
            );
            Ok(Type::Void)
        }
        AstTokenPayload::Cast => {
            let arg_type = unroll_node(&node.args.get(0).expect("cast argument"))?;
            let target_type =
                Type::from_dense_token(&node.args.get(1).expect("Type Declaration").root);

            bytecode.push(ByteCode::CastInt(arg_type, target_type.clone()));

            Ok(target_type)
        }
        _ => Err(CompilerError {
            location: node.root.loc.clone(),
            msg: format!("Exporter Error: Unknown token {:?}", node.root.payload),
        }),
    }
}

pub fn compile(context: &Context, ast: DenseAst) -> Result<Vec<ByteCode>, CompilerError> {
    let mut bytecode = vec![];
    let mut register_map: HashMap<&str, usize> = hashmap! {"__init__"=> 1};
    bytecode.push(ByteCode::Alloca(Type::Int32));
    bytecode.push(ByteCode::PushInt32(0));
    bytecode.push(ByteCode::Store(Type::Int32, 0));
    for statement in ast.statements.iter() {
        unroll_node(&mut register_map, context, statement, &mut bytecode)?;
    }
    Ok(bytecode)
}

#[cfg(test)]
mod specs {
    use super::*;
    use crate::ast::{DenseAst, DenseToken, LexerTokenPayloadStub, Node};
    use crate::token::TokenPayload;
    use crate::Declaration;
    use ByteCode::*;
    use TokenPayload::*;

    static HEADER: [ByteCode; 3] = [Alloca(Type::Int32), PushInt32(0), Store(Type::Int32, 0)];

    #[test]
    fn milestone_1() {
        let input = DenseAst {
            statements: vec![Node {
                root: DenseToken::stub(TokenPayload::Ident("stdout".to_owned())),
                args: vec![Node::leaf(DenseToken::stub(TokenPayload::Integer(42)))],
            }],
        };

        let context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };
        let actual = compile(&context, input);
        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let expected = vec![PushInt32(42), StdOut];
        let expected = [&HEADER[..], &expected].concat();

        assert_eq!(actual, expected);
    }

    #[test]
    fn operator_simple() {
        let input = DenseAst {
            statements: vec![Node {
                root: DenseToken::stub(TokenPayload::Ident("stdout".to_owned())),
                args: vec![Node {
                    root: DenseToken::stub(TokenPayload::Add),
                    args: vec![
                        Node::leaf(DenseToken::stub(TokenPayload::Integer(3))),
                        Node::leaf(DenseToken::stub(TokenPayload::Integer(5))),
                    ],
                }],
            }],
        };
        let context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };
        let actual = compile(&context, input);
        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let expected = vec![
            PushInt32(3),
            PushInt32(5),
            ByteCode::Add(Type::Int32),
            StdOut,
        ];
        let expected = [&HEADER[..], &expected].concat();

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_4_main() {
        let input = DenseAst {
            statements: vec![
                Node {
                    root: DenseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("a".to_string()))),
                        Node::leaf(DenseToken::stub(Integer(3))),
                    ],
                },
                Node {
                    root: DenseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("b".to_string()))),
                        Node {
                            root: DenseToken::stub(TokenPayload::Add),
                            args: vec![
                                Node::leaf(DenseToken::stub(Ident("a".to_string()))),
                                Node::leaf(DenseToken::stub(Integer(5))),
                            ],
                        },
                    ],
                },
                Node {
                    root: DenseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("c".to_string()))),
                        Node::leaf(DenseToken::stub(Integer(7))),
                    ],
                },
                Node {
                    root: DenseToken::stub(Ident("stdout".to_string())),
                    args: vec![Node {
                        root: DenseToken::stub(Ident("max".to_string())),
                        args: vec![
                            Node::leaf(DenseToken::stub(Ident("b".to_string()))),
                            Node::leaf(DenseToken::stub(Ident("c".to_string()))),
                        ],
                    }],
                },
            ],
        };

        let context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::function(Type::Void, vec![Type::Int32], true),
                "max".to_string() => Declaration::function(Type::Int32, vec![Type::Int32,Type::Int32], false),
                "a".to_string() => Declaration::variable(Type::Int32),
                "b".to_string() => Declaration::variable(Type::Int32),
                "c".to_string() => Declaration::variable(Type::Int32)
            },
        };

        let actual = compile(&context, input);

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let expected = vec![
            PushInt32(3),
            Alloca(Type::Int32),
            Store(Type::Int32, 1),
            Load(Type::Int32, 1),
            PushInt32(5),
            ByteCode::Add(Type::Int32),
            Alloca(Type::Int32),
            Store(Type::Int32, 2),
            PushInt32(7),
            Alloca(Type::Int32),
            Store(Type::Int32, 3),
            Load(Type::Int32, 2),
            Load(Type::Int32, 3),
            Call2("max".to_string(), Type::Int32, Type::Int32, Type::Int32),
            StdOut,
        ];
        let expected = [&HEADER[..], &expected].concat();
        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_5_explicit_cast() {
        let input = DenseAst {
            statements: vec![
                Node {
                    root: DenseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("a".to_string()))),
                        Node::leaf(DenseToken::stub(Ident("i32".to_string()))),
                        Node::leaf(DenseToken::stub(Integer(3))),
                    ],
                },
                Node {
                    root: DenseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("b".to_string()))),
                        Node::leaf(DenseToken::stub(Ident("i8".to_string()))),
                        Node {
                            root: DenseToken::stub(TokenPayload::Add),
                            args: vec![
                                Node {
                                    root: DenseToken::stub(Cast),
                                    args: vec![
                                        Node::leaf(DenseToken::stub(Ident("a".to_string()))),
                                        Node::leaf(DenseToken::stub(Ident("i8".to_string()))),
                                    ],
                                },
                                Node {
                                    root: DenseToken::stub(Cast),
                                    args: vec![
                                        Node::leaf(DenseToken::stub(Integer(5))),
                                        Node::leaf(DenseToken::stub(Ident("i8".to_string()))),
                                    ],
                                },
                            ],
                        },
                    ],
                },
                Node {
                    root: DenseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("c".to_string()))),
                        Node::leaf(DenseToken::stub(Ident("i8".to_string()))),
                        Node {
                            root: DenseToken::stub(Cast),
                            args: vec![
                                Node::leaf(DenseToken::stub(Integer(7))),
                                Node::leaf(DenseToken::stub(Ident("i8".to_string()))),
                            ],
                        },
                    ],
                },
                Node {
                    root: DenseToken::stub(Ident("stdout".to_string())),
                    args: vec![Node {
                        root: DenseToken::stub(Ident("max".to_string())),
                        args: vec![
                            Node::leaf(DenseToken::stub(Ident("b".to_string()))),
                            Node::leaf(DenseToken::stub(Ident("c".to_string()))),
                        ],
                    }],
                },
            ],
        };

        let context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::full_template_statement(1),
                "max".to_string() => Declaration::full_template_function(2),
                "a".to_string() => Declaration::variable(Type::Int32),
                "b".to_string() => Declaration::variable(Type::Int8),
                "c".to_string() => Declaration::variable(Type::Int8)
            },
        };

        let actual = compile(&context, input);
        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = vec![
            Alloca(Type::Int32),
            PushInt32(0),
            Store(Type::Int32, 0),
            PushInt32(3),
            Alloca(Type::Int32),
            Store(Type::Int32, 1),
            Load(Type::Int32, 1),
            CastInt(Type::Int32, Type::Int8),
            PushInt32(5),
            CastInt(Type::Int32, Type::Int8),
            ByteCode::Add(Type::Int8),
            Alloca(Type::Int8),
            Store(Type::Int8, 2),
            PushInt32(7),
            CastInt(Type::Int32, Type::Int8),
            Alloca(Type::Int8),
            Store(Type::Int8, 3),
            Load(Type::Int8, 2),
            Load(Type::Int8, 3),
            Call2("max".to_string(), Type::Int8, Type::Int8, Type::Int8),
            StdOut,
        ];

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_5_main() {
        let input = DenseAst {
            statements: vec![
                Node {
                    root: DenseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("a".to_string()))),
                        Node::leaf(DenseToken::stub(Ident("i32".to_string()))),
                        Node::leaf(DenseToken::stub(Integer(3))),
                    ],
                },
                Node {
                    root: DenseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("b".to_string()))),
                        Node::leaf(DenseToken::stub(Ident("i8".to_string()))),
                        Node {
                            root: DenseToken::stub(TokenPayload::Add),
                            args: vec![
                                Node {
                                    root: DenseToken::stub(Cast),
                                    args: vec![
                                        Node::leaf(DenseToken::stub(Ident("a".to_string()))),
                                        Node::leaf(DenseToken::stub(Ident("i8".to_string()))),
                                    ],
                                },
                                Node::leaf(DenseToken::stub(Integer(5))),
                            ],
                        },
                    ],
                },
                Node {
                    root: DenseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("c".to_string()))),
                        Node::leaf(DenseToken::stub(Ident("i8".to_string()))),
                        Node::leaf(DenseToken::stub(Integer(7))),
                    ],
                },
                Node {
                    root: DenseToken::stub(Ident("stdout".to_string())),
                    args: vec![Node {
                        root: DenseToken::stub(Ident("max".to_string())),
                        args: vec![
                            Node::leaf(DenseToken::stub(Ident("b".to_string()))),
                            Node::leaf(DenseToken::stub(Ident("c".to_string()))),
                        ],
                    }],
                },
            ],
        };

        let context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::function(Type::Void, vec![Type::Int8], true),
                "max".to_string() => Declaration::function(Type::Int8, vec![Type::Int8,Type::Int8], false),
                "a".to_string() => Declaration::variable(Type::Int32),
                "b".to_string() => Declaration::variable(Type::Int8),
                "c".to_string() => Declaration::variable(Type::Int8)
            },
        };

        let actual = compile(&context, input);
        // assert!(actual.is_ok());
        if let Err(error) = actual {
            error.print("test");
        }
    }
}
