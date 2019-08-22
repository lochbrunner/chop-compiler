use crate::ast::{Ast, Node};
use crate::token::{Location, Token, TokenPayload};
use crate::CompilerError;
use crate::Context;
use crate::Type;
use std::collections::HashMap;

#[derive(PartialEq, Debug)]
pub enum ByteCode {
    StdOut, // For now hard-coded
    Max,    // For now hard-coded
    Min,    // For now hard-coded
    PushInt32(i32),
    AddInt32,
    SubInt32,
    MulInt32,
    DivInt32,
    RemInt32,
    StoreInt32(usize),
    LoadInt32(usize),
}

fn get_build_ins(ident: &str, location: &Location) -> Result<ByteCode, CompilerError> {
    match ident {
        "stdout" => Ok(ByteCode::StdOut),
        "min" => Ok(ByteCode::Min),
        "max" => Ok(ByteCode::Max),
        _ => Err(CompilerError {
            location: location.clone(),
            msg: format!("No build-in function \"{}\" was defined.", ident),
        }),
    }
}

fn check_types(
    name: &str,
    location: &Location,
    expected: &[Type],
    actual: &[Type],
) -> Result<(), CompilerError> {
    if expected != actual {
        Err(CompilerError {
            location: location.clone(),
            msg: format!(
                "Exporter Error: Operator/function {} arguments of type {:?} but got {:?}",
                name, expected, actual
            ),
        })
    } else {
        Ok(())
    }
}

fn unroll_node<'a>(
    register_map: &mut HashMap<&'a str, usize>,
    context: &Context,
    node: &'a Node<Token>,
    bytecode: &mut Vec<ByteCode>,
) -> Result<Type, CompilerError> {
    match node.root.token {
        TokenPayload::Add
        | TokenPayload::Subtract
        | TokenPayload::Multiply
        | TokenPayload::Divide
        | TokenPayload::Remainder => {
            let arg_types = node
                .args
                .iter()
                .map(|arg| unroll_node(register_map, context, arg, bytecode))
                .collect::<Result<Vec<_>, CompilerError>>()?;
            check_types(
                &format!("{:?}", node.root.token),
                &node.root.begin,
                &vec![Type::Int32, Type::Int32],
                &arg_types,
            )?;
            bytecode.push(match node.root.token {
                TokenPayload::Add => ByteCode::AddInt32,
                TokenPayload::Subtract => ByteCode::SubInt32,
                TokenPayload::Multiply => ByteCode::MulInt32,
                TokenPayload::Divide => ByteCode::DivInt32,
                TokenPayload::Remainder => ByteCode::RemInt32,
                _ => ByteCode::AddInt32,
            });
            Ok(Type::Int32)
        }
        TokenPayload::Int32(v) => {
            bytecode.push(ByteCode::PushInt32(v));
            Ok(Type::Int32)
        }
        TokenPayload::Ident(ref ident) => {
            let declaration = context.get_declaration(ident, node.root.begin.clone())?;
            // Function or variable? (Function used as argument is a variable here ;) )
            if declaration.post.is_empty() {
                if let Some(index) = register_map.get::<str>(ident) {
                    bytecode.push(ByteCode::LoadInt32(*index));
                } else {
                    return Err(CompilerError::from_token(
                        &node.root,
                        format!("No Variable with name {} found in register", ident),
                    ));
                }
            } else {
                let arg_types = node
                    .args
                    .iter()
                    .map(|arg| unroll_node(register_map, context, arg, bytecode))
                    .collect::<Result<Vec<_>, CompilerError>>()?;
                check_types(ident, &node.root.begin, &declaration.post, &arg_types)?;
                // Get build-in functions
                let instruction = get_build_ins(&ident, &node.root.begin)?;
                bytecode.push(instruction);
            }
            Ok(declaration.return_type.clone())
        }
        TokenPayload::DefineLocal => {
            // Compile argument
            if node.args.len() != 2 {
                return Err(CompilerError::from_token(
                    &node.root,
                    format!(
                        "Exporter Error: DefineLocal need two arguments but got {}",
                        node.args.len()
                    ),
                ));
            }
            let arg = unroll_node(
                register_map,
                context,
                node.args.iter().nth(1).expect("Definition"),
                bytecode,
            )?;
            if arg != Type::Int32 {
                return Err(CompilerError::from_token(
                    &node.root,
                    format!("Exporter Error: Can only define int32, but got {:?}", arg),
                ));
            }
            bytecode.push(ByteCode::StoreInt32(register_map.len()));
            register_map.insert(
                &node
                    .args
                    .iter()
                    .nth(0)
                    .expect("Definition")
                    .root
                    .token
                    .get_ident()
                    .expect("ident"),
                register_map.len(),
            );
            Ok(Type::Void)
        }
        _ => {
            return Err(CompilerError {
                location: node.root.begin.clone(),
                msg: format!("Exporter Error: Unknown token {:?}", node.root.token),
            })
        }
    }
}

pub fn export(context: &Context, ast: Ast) -> Result<Vec<ByteCode>, CompilerError> {
    let mut bytecode = vec![];
    let mut register_map: HashMap<&str, usize> = HashMap::new();
    for statement in ast.statements.iter() {
        unroll_node(&mut register_map, context, statement, &mut bytecode)?;
    }
    Ok(bytecode)
}

#[cfg(test)]
mod specs {
    use super::*;
    use crate::ast::Node;
    use crate::token::{Token, TokenPayload};
    use crate::Declaration;
    use ByteCode::*;
    use TokenPayload::*;

    #[test]
    fn milestone_1() {
        let input = Ast {
            statements: vec![Node {
                root: Token::stub(TokenPayload::Ident("stdout".to_owned())),
                args: vec![Node::new(Token::stub(TokenPayload::Int32(42)))],
            }],
        };

        let context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };
        let actual = export(&context, input);
        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let expected = vec![PushInt32(42), StdOut];

        assert_eq!(actual, expected);
    }

    #[test]
    fn operator_simple() {
        let input = Ast {
            statements: vec![Node {
                root: Token::stub(TokenPayload::Ident("stdout".to_owned())),
                args: vec![Node {
                    root: Token::stub(TokenPayload::Add),
                    args: vec![
                        Node::new(Token::stub(TokenPayload::Int32(3))),
                        Node::new(Token::stub(TokenPayload::Int32(5))),
                    ],
                }],
            }],
        };
        let context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };
        let actual = export(&context, input);
        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let expected = vec![PushInt32(3), PushInt32(5), AddInt32, StdOut];

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_4_main() {
        let input = Ast {
            statements: vec![
                Node {
                    root: Token::stub(DefineLocal),
                    args: vec![
                        Node::new(Token::stub(Ident("a".to_string()))),
                        Node::new(Token::stub(Int32(3))),
                    ],
                },
                Node {
                    root: Token::stub(DefineLocal),
                    args: vec![
                        Node::new(Token::stub(Ident("b".to_string()))),
                        Node {
                            root: Token::stub(Add),
                            args: vec![
                                Node::new(Token::stub(Ident("a".to_string()))),
                                Node::new(Token::stub(Int32(5))),
                            ],
                        },
                    ],
                },
                Node {
                    root: Token::stub(DefineLocal),
                    args: vec![
                        Node::new(Token::stub(Ident("c".to_string()))),
                        Node::new(Token::stub(Int32(7))),
                    ],
                },
                Node {
                    root: Token::stub(Ident("stdout".to_string())),
                    args: vec![Node {
                        root: Token::stub(Ident("max".to_string())),
                        args: vec![
                            Node::new(Token::stub(Ident("b".to_string()))),
                            Node::new(Token::stub(Ident("c".to_string()))),
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

        let actual = export(&context, input);
        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let expected = vec![
            PushInt32(3),
            StoreInt32(0),
            LoadInt32(0),
            PushInt32(5),
            AddInt32,
            StoreInt32(1),
            PushInt32(7),
            StoreInt32(2),
            LoadInt32(1),
            LoadInt32(2),
            Max,
            StdOut,
        ];
        assert_eq!(actual, expected);
    }
}
