use crate::ast::{Ast, Node};
use crate::token::{Location, Token, TokenPayload};
use crate::CompilerError;
use crate::Context;
use crate::Type;

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
}

fn get_build_ins(ident: &str, location: &Location) -> Result<ByteCode, CompilerError> {
    match ident {
        "stdout" => Ok(ByteCode::StdOut),
        "min" => Ok(ByteCode::Min),
        "max" => Ok(ByteCode::Max),
        _ => Err(CompilerError {
            location: location.clone(),
            msg: format!("No build-in function {} was not defined.", ident),
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

fn unroll_node(
    context: &Context,
    node: &Node<Token>,
    bytecode: &mut Vec<ByteCode>,
) -> Result<Type, CompilerError> {
    let arg_types = node
        .args
        .iter()
        .map(|arg| unroll_node(context, arg, bytecode))
        .collect::<Result<Vec<_>, CompilerError>>()?;

    match node.root.token {
        TokenPayload::Add
        | TokenPayload::Subtract
        | TokenPayload::Multiply
        | TokenPayload::Divide
        | TokenPayload::Remainder => {
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
            check_types(ident, &node.root.begin, &declaration.post, &arg_types)?;
            // Get build-in functions
            let instruction = get_build_ins(&ident, &node.root.begin)?;
            bytecode.push(instruction);
            Ok(declaration.return_type.clone())
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
    for statement in ast.statements.iter() {
        unroll_node(context, statement, &mut bytecode)?;
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
}
