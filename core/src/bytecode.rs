use crate::ast::{AstTokenPayload, DenseToken, Node, Scope, Statement};
use crate::declaration::{Context, Signature, Type, Visibility};
use crate::error::{CompilerError, Location};
use std::collections::HashMap;

#[derive(PartialEq, Debug, Clone)]
pub enum ByteCode {
    StdOut(Type), // For now hard-coded
    // ident, return type, arg1, arg2
    Call2(String, Type, Type, Type),
    PushInt8(i8),
    PushInt16(i16),
    PushInt32(i32),
    PushInt64(i64),
    PushUInt8(u8),
    PushUInt16(u16),
    PushUInt32(u32),
    PushUInt64(u64),
    PushUSize(usize),
    PushFloat32(f32),
    PushFloat64(f64),
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

fn get_build_ins(ident: &str, signature: &Signature<Type>) -> Option<ByteCode> {
    match ident {
        "stdout" => {
            if signature.args.len() != 1 || signature.return_type != Type::Void {
                None
            } else {
                Some(ByteCode::StdOut(signature.args[0].clone()))
            }
        }
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
                "[E1]: Operator/function {} expected 2 arguments but got {}",
                name,
                args.len()
            ),
        })
    } else if args.get(0).unwrap() != args.get(1).unwrap() {
        Err(CompilerError {
            location: location.clone(),
            msg: format!(
                "[E2]: Arguments of operator/function \"{}\" are different. {:?} and {:?}",
                name,
                args.get(0).unwrap(),
                args.get(1).unwrap()
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
            let v = provider.content;
            match node.root.return_type {
                Type::Int8 => {
                    bytecode.push(ByteCode::PushInt8(v as i8));
                }
                Type::Int16 => {
                    bytecode.push(ByteCode::PushInt16(v as i16));
                }
                Type::Int32 => {
                    bytecode.push(ByteCode::PushInt32(v as i32));
                }
                Type::Int64 => {
                    bytecode.push(ByteCode::PushInt64(v as i64));
                }
                Type::UInt8 => {
                    bytecode.push(ByteCode::PushUInt8(v as u8));
                }
                Type::UInt16 => {
                    bytecode.push(ByteCode::PushUInt16(v as u16));
                }
                Type::UInt32 => {
                    bytecode.push(ByteCode::PushUInt32(v as u32));
                }
                Type::UInt64 => {
                    bytecode.push(ByteCode::PushUInt64(v as u64));
                }
                _ => {
                    return Err(node.root.loc.to_error(format!(
                        "[E3]: An integer can not be of type {:?}",
                        node.root.return_type
                    )))
                }
            }
            Ok(node.root.return_type.clone())
        }
        AstTokenPayload::Float(ref provider) => {
            // TODO: get value of correct type
            let v = provider.content;
            match node.root.return_type {
                Type::Float32 => {
                    bytecode.push(ByteCode::PushFloat32(v as f32));
                }
                Type::Float64 => {
                    bytecode.push(ByteCode::PushFloat64(v as f64));
                }
                _ => {
                    return Err(node.root.loc.to_error(format!(
                        "[E4]: A Float can not be of type {:?}",
                        node.root.return_type
                    )))
                }
            }
            Ok(node.root.return_type.clone())
        }
        AstTokenPayload::Struct(_) => todo!(),
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
                            "[E5]: Signature of variable/function \"{}\" could not be resolved: {}",
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
                        format!("[E6]: No Variable with name {} found in register", ident),
                    ));
                }
            } else {
                let Signature { return_type, args } = signature.clone();
                // Get build-in functions
                match get_build_ins(&ident, &signature) {
                    Some(instruction) => bytecode.push(instruction),
                    None => {
                        if arg_types.len() != 2 {
                            return Err(CompilerError::from_token::<DenseToken>(
                                &node.root,
                                format!("[E7]: No Function {} expects {} arguments, but only 2 arguments are supported yet.", ident, declaration.req_args_count()),
                            ));
                        }
                        bytecode.push(ByteCode::Call2(
                            ident.clone(),
                            return_type,
                            args.get(0).unwrap().clone(),
                            args.get(1).unwrap().clone(),
                        ));
                    }
                }
            }
            Ok(signature.return_type)
        }
        AstTokenPayload::Define(ref dtype, Visibility::Local) => {
            // Compile argument
            if node.args.len() != 2 {
                // TODO: Handle Type declaration
                return Err(node.root.loc.to_error(format!(
                    "[E8]: Exporter Error: DefineLocal need two arguments but got {}",
                    node.args.len()
                )));
            }
            let dtype = dtype.clone().unwrap_or(Type::Int32);
            unroll_node(node.args.get(1).expect("Definition"))?;

            bytecode.push(ByteCode::Alloca(dtype.clone()));
            let index = register_map.len();
            bytecode.push(ByteCode::Store(dtype, index));
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
        AstTokenPayload::Define(ref _dtype, Visibility::Public) => unimplemented!(),
        AstTokenPayload::Cast => {
            let arg_type = unroll_node(&node.args.get(0).expect("cast argument"))?;
            let target_type =
                Type::from_dense_token(&node.args.get(1).expect("Type Declaration").root);

            bytecode.push(ByteCode::CastInt(arg_type, target_type.clone()));

            Ok(target_type)
        }
        AstTokenPayload::Pipe => Err(CompilerError {
            location: node.root.loc.clone(),
            msg: format!("[9]: Exporter Error: Unknown token {:?}", node.root.payload),
        }),
        AstTokenPayload::Scope => unimplemented!(),
        AstTokenPayload::FieldRef => todo!(),
    }
}

fn unroll_statement<'a>(
    register_map: &mut HashMap<&'a str, usize>,
    context: &Context,
    statement: &'a Statement<DenseToken>,
    bytecode: &mut Vec<ByteCode>,
) -> Result<Type, CompilerError> {
    match statement {
        Statement::InScope(node) => unroll_node(register_map, context, node, bytecode),
        Statement::Nested(scope) => {
            for statement in scope.statements.iter() {
                unroll_statement(register_map, context, statement, bytecode)?;
            }
            Ok(Type::Void)
        }
    }
}

pub fn compile(context: &Context, ast: Scope<DenseToken>) -> Result<Vec<ByteCode>, CompilerError> {
    let mut bytecode = vec![];
    let mut register_map: HashMap<&str, usize> = hashmap! {"__init__"=> 1};
    bytecode.push(ByteCode::Alloca(Type::Int32));
    bytecode.push(ByteCode::PushInt32(0));
    bytecode.push(ByteCode::Store(Type::Int32, 0));
    unroll_statement(
        &mut register_map,
        context,
        &Statement::Nested(ast),
        &mut bytecode,
    )?;
    Ok(bytecode)
}

#[cfg(test)]
mod specs {
    use super::*;
    use crate::ast::{DenseToken, LexerTokenPayloadStub, Node, Scope};
    use crate::declaration::{Declaration, Visibility};
    use crate::token::TokenPayload;
    use ByteCode::*;
    use TokenPayload::*;

    static HEADER: [ByteCode; 3] = [Alloca(Type::Int32), PushInt32(0), Store(Type::Int32, 0)];

    #[test]
    fn milestone_1() {
        let input = Scope {
            statements: vec![Statement::InScope(Node {
                root: DenseToken::stub(TokenPayload::Ident("stdout".to_owned())),
                args: vec![Node::leaf(DenseToken::stub_typed(
                    TokenPayload::Integer(42),
                    Type::Int32,
                ))],
            })],
        };

        let context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::function(Type::Void, vec![Type::Int32], true, Visibility::Local)
            },
            lower: None,
        };
        let actual = compile(&context, input);
        assert_ok!(actual);
        let actual = actual.unwrap();
        let expected = vec![PushInt32(42), StdOut(Type::Int32)];
        let expected = [&HEADER[..], &expected].concat();

        assert_eq!(actual, expected);
    }

    #[test]
    fn operator_simple() {
        let input = Scope {
            statements: vec![Statement::InScope(Node {
                root: DenseToken::stub(TokenPayload::Ident("stdout".to_owned())),
                args: vec![Node {
                    root: DenseToken::stub(TokenPayload::Add),
                    args: vec![
                        Node::leaf(DenseToken::stub_typed(
                            TokenPayload::Integer(3),
                            Type::Int32,
                        )),
                        Node::leaf(DenseToken::stub_typed(
                            TokenPayload::Integer(5),
                            Type::Int32,
                        )),
                    ],
                }],
            })],
        };
        let context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::function(Type::Void, vec![Type::Int32], true, Visibility::Local)
            },
            lower: None,
        };
        let actual = compile(&context, input);
        assert_ok!(actual);
        let actual = actual.unwrap();
        let expected = vec![
            PushInt32(3),
            PushInt32(5),
            ByteCode::Add(Type::Int32),
            StdOut(Type::Int32),
        ];
        let expected = [&HEADER[..], &expected].concat();

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_4_main() {
        // a := 3
        // b := a + 5
        // c := 7
        // stdout max(b,c)
        let input = Scope {
            statements: vec![
                Node {
                    root: DenseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("a".to_string()))),
                        Node::leaf(DenseToken::stub_typed(Integer(3), Type::Int32)),
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
                                Node::leaf(DenseToken::stub_typed(Integer(5), Type::Int32)),
                            ],
                        },
                    ],
                },
                Node {
                    root: DenseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("c".to_string()))),
                        Node::leaf(DenseToken::stub_typed(Integer(7), Type::Int32)),
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
            ]
            .into_iter()
            .map(Statement::InScope)
            .collect(),
        };

        let context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::function(Type::Void, vec![Type::Int32], true, Visibility::Local),
                "max".to_string() => Declaration::function(Type::Int32, vec![Type::Int32,Type::Int32], false, Visibility::Local),
                "a".to_string() => Declaration::variable(Type::Int32),
                "b".to_string() => Declaration::variable(Type::Int32),
                "c".to_string() => Declaration::variable(Type::Int32)
            },
            lower: None,
        };

        let actual = compile(&context, input);

        assert_ok!(actual);
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
            StdOut(Type::Int32),
        ];
        let expected = [&HEADER[..], &expected].concat();
        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_5_explicit_cast() {
        let input = Scope {
            statements: vec![
                Node {
                    root: DenseToken {
                        payload: AstTokenPayload::Define(Some(Type::Int32), Visibility::Local),
                        return_type: Type::Void,
                        loc: Location::default(),
                    },
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("a".to_string()))),
                        Node::leaf(DenseToken::stub_typed(Integer(3), Type::Int32)),
                    ],
                },
                Node {
                    root: DenseToken {
                        payload: AstTokenPayload::Define(Some(Type::Int8), Visibility::Local),
                        return_type: Type::Void,
                        loc: Location::default(),
                    },
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("b".to_string()))),
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
                                        Node::leaf(DenseToken::stub_typed(Integer(5), Type::Int32)),
                                        Node::leaf(DenseToken::stub(Ident("i8".to_string()))),
                                    ],
                                },
                            ],
                        },
                    ],
                },
                Node {
                    root: DenseToken {
                        payload: AstTokenPayload::Define(Some(Type::Int8), Visibility::Local),
                        return_type: Type::Void,
                        loc: Location::default(),
                    },
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("c".to_string()))),
                        Node {
                            root: DenseToken::stub(Cast),
                            args: vec![
                                Node::leaf(DenseToken::stub_typed(Integer(7), Type::Int32)),
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
            ]
            .into_iter()
            .map(Statement::InScope)
            .collect(),
        };

        let context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::full_template_statement(1),
                "max".to_string() => Declaration::full_template_function(2),
                "a".to_string() => Declaration::variable(Type::Int32),
                "b".to_string() => Declaration::variable(Type::Int8),
                "c".to_string() => Declaration::variable(Type::Int8),
                "i8".to_string() => Declaration::variable(Type::Type),
            },
            lower: None,
        };

        let actual = compile(&context, input);
        assert_ok!(actual);
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
            StdOut(Type::Int8),
        ];

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_5_main() {
        let input = Scope {
            statements: vec![
                Node {
                    root: DenseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("a".to_string()))),
                        Node::leaf(DenseToken::stub_typed(Integer(3), Type::Int32)),
                    ],
                },
                Node {
                    root: DenseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("b".to_string()))),
                        Node {
                            root: DenseToken::stub(TokenPayload::Add),
                            args: vec![
                                Node {
                                    root: DenseToken::stub_typed(Cast, Type::Int8),
                                    args: vec![
                                        Node::leaf(DenseToken::stub_typed(
                                            Ident("a".to_string()),
                                            Type::Int32,
                                        )),
                                        Node::leaf(DenseToken::stub(Ident("i8".to_string()))),
                                    ],
                                },
                                Node::leaf(DenseToken::stub_typed(Integer(5), Type::Int8)),
                            ],
                        },
                    ],
                },
                Node {
                    root: DenseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(DenseToken::stub(Ident("c".to_string()))),
                        Node::leaf(DenseToken::stub_typed(Integer(7), Type::Int8)),
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
            ]
            .into_iter()
            .map(Statement::InScope)
            .collect(),
        };

        let context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::function(Type::Void, vec![Type::Int8], true, Visibility::Local),
                "max".to_string() => Declaration::function(Type::Int8, vec![Type::Int8,Type::Int8], false, Visibility::Local),
                "a".to_string() => Declaration::variable(Type::Int32),
                "b".to_string() => Declaration::variable(Type::Int8),
                "c".to_string() => Declaration::variable(Type::Int8)
            },
            lower: None,
        };

        let actual = compile(&context, input);
        assert_ok!(actual);
        if let Err(error) = actual {
            error.print("test");
        }
    }
}
