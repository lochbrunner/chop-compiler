use crate::ast::Ast;
use crate::token::TokenPayload;
use crate::CompilerError;

#[derive(PartialEq, Debug)]
pub enum ByteCode {
    StdOut, // For now hard-coded
    PushInt32(i32),
}

pub fn export(ast: Ast) -> Result<Vec<ByteCode>, CompilerError> {
    let mut bytecode = vec![];
    for mut statement in ast.statements.into_iter() {
        match statement.root.token {
            TokenPayload::Ident(ident) => match ident.as_ref() {
                "stdout" => match statement.args.pop() {
                    Some(arg) => {
                        if !statement.args.is_empty() {
                            return Err(CompilerError {
                                location: statement.root.begin.clone(),
                                msg: format!(
                                    "Exporter Error: Function {} has tow many arguments",
                                    ident
                                ),
                            });
                        }
                        match arg.root.token {
                            TokenPayload::Int32(v) => {
                                bytecode.push(ByteCode::PushInt32(v));
                            }
                            _ => {
                                return Err(CompilerError {
                                    location: statement.root.begin.clone(),
                                    msg: format!(
                                        "Exporter Error: Function {} expects an int as argument but got {:?}",
                                        ident, arg.root.token
                                    ),
                                })
                            }
                        }
                        bytecode.push(ByteCode::StdOut);
                    }
                    None => {
                        return Err(CompilerError {
                            location: statement.root.begin.clone(),
                            msg: format!("Exporter Error: Function {} has no argument", ident),
                        })
                    }
                },
                _ => {
                    return Err(CompilerError {
                        location: statement.root.begin.clone(),
                        msg: format!("Exporter Error: Unknown ident: {}", ident),
                    })
                }
            },
            _ => {
                return Err(CompilerError {
                    location: statement.root.begin.clone(),
                    msg: format!("Exporter Error: Unknown token {:?}", statement.root.token),
                })
            }
        }
    }
    Ok(bytecode)
}

#[cfg(test)]
mod specs {
    use super::*;
    use crate::ast::Node;
    use crate::token::{Location, Token, TokenPayload};

    #[test]
    fn milestone_1() {
        let input = Ast {
            statements: vec![Node {
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
            }],
        };
        let actual = export(input);
        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let expected = vec![ByteCode::PushInt32(42), ByteCode::StdOut];

        assert_eq!(actual, expected);
    }
}
