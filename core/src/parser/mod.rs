use crate::ast;
use crate::token::{Token, TokenPayload};
use crate::CompilerError;
use crate::Context;

#[derive(PartialEq, PartialOrd, Debug, Clone)]
pub enum Precedence {
    PCall,
    POpening,
    Pipe,
    PSum,
    PProduct,
}

struct Infix {
    token: Token,
    precedence: Precedence,
    req_args_count: usize,
    is_statement: bool,
}

#[derive(Debug)]
enum Symbol {
    Raw(Token),
    Finished(ast::Node<Token>),
}

struct ParseStack {
    pub symbol: Vec<Symbol>,
    pub infix: Vec<Infix>,
}
impl ParseStack {
    pub fn pop_symbol_as_node(&mut self) -> Option<ast::Node<Token>> {
        match self.symbol.pop() {
            None => None,
            Some(sym) => Some(match sym {
                Symbol::Raw(token) => ast::Node {
                    root: token,
                    args: vec![],
                },
                Symbol::Finished(node) => node,
            }),
        }
    }
}

impl ParseStack {
    /// Check if the last infix should be astified
    pub fn check_precedence(&self, precedence: &Precedence) -> bool {
        match self.infix.last() {
            None => false,
            Some(last) => last.precedence > *precedence,
        }
    }
}

fn astify(_context: &Context, till: Precedence, stack: &mut ParseStack) -> Result<(), String> {
    while let Some(op) = stack.infix.pop() {
        if op.precedence <= till {
            stack.infix.push(op);
            break;
        }
        if stack.symbol.len() < op.req_args_count {
            return Err(format!(
                "Operator {:?} consumes {} arguments. But only {} are available",
                op.token,
                op.req_args_count,
                stack.symbol.len()
            ));
        }

        let mut args = (0..op.req_args_count)
            .map(|_| stack.pop_symbol_as_node().unwrap())
            .collect::<Vec<_>>();
        args.reverse();
        stack.symbol.push(Symbol::Finished(ast::Node {
            root: op.token.clone(),
            args,
        }));
    }

    // println!(
    //     "\ninfix: {:#?}",
    //     stack
    //         .infix
    //         .iter()
    //         .map(|i| i.token.token.clone())
    //         .collect::<Vec<_>>()
    // );
    // println!("symbols: {:#?}", stack.symbol);
    Ok(())
}

/// Turns a slice of tokens into an ast.
/// Using [Shunting-yard algorithm](https://en.wikipedia.org/wiki/Shunting-yard_algorithm#/media/File:Shunting_yard.svg)
pub fn parse(context: &Context, tokens: &[Token]) -> Result<ast::Ast, CompilerError> {
    let mut stack = ParseStack {
        infix: Vec::new(),
        symbol: Vec::new(),
    };

    let mut expect_function_as_variable = false;

    for token in tokens.iter() {
        match &token.token {
            TokenPayload::ParenthesesL => stack.infix.push(Infix {
                token: token.clone(),
                precedence: Precedence::POpening,
                req_args_count: 0,
                is_statement: false,
            }),
            TokenPayload::Delimiter => {
                if let Err(msg) = astify(context, Precedence::POpening, &mut stack) {
                    return Err(CompilerError {
                        location: token.begin.clone(),
                        msg: format!("Error on astify: {}", msg),
                    });
                }
            }
            TokenPayload::ParenthesesR => {
                if let Err(msg) = astify(context, Precedence::POpening, &mut stack) {
                    return Err(CompilerError {
                        location: token.begin.clone(),
                        msg: format!("Error on astify: {}", msg),
                    });
                }
                stack.infix.pop();
            }
            TokenPayload::Ident(ident) => {
                if expect_function_as_variable {
                    stack.symbol.push(Symbol::Raw(token.clone()));
                } else {
                    let declaration = match context.declarations.get(ident) {
                        None => {
                            return Err(CompilerError {
                                location: token.begin.clone(),
                                msg: format!("Function {} was not defined.", ident),
                            })
                        }
                        Some(declaration) => declaration,
                    };
                    stack.infix.push(Infix {
                        token: token.clone(),
                        precedence: Precedence::PCall,
                        req_args_count: declaration.post.len(),
                        is_statement: declaration.is_statement,
                    });
                }
                expect_function_as_variable = false;
            }
            TokenPayload::Int32(_) => stack.symbol.push(Symbol::Raw(token.clone())),
            TokenPayload::DefineLocal => (), // TODO: use later
            TokenPayload::Pipe => {
                if stack.check_precedence(&Precedence::Pipe) {
                    if let Err(msg) = astify(context, Precedence::Pipe, &mut stack) {
                        return Err(CompilerError {
                            location: token.begin.clone(),
                            msg: format!("Error on astify: {}", msg),
                        });
                    }
                }
                stack.infix.push(Infix {
                    token: token.clone(),
                    precedence: Precedence::Pipe,
                    req_args_count: 2,
                    is_statement: true, // TODO: This is not completely correct
                });
                expect_function_as_variable = true;
            }
            TokenPayload::Add | TokenPayload::Subtract => {
                if stack.check_precedence(&Precedence::PSum) {
                    if let Err(msg) = astify(context, Precedence::PSum, &mut stack) {
                        return Err(CompilerError {
                            location: token.begin.clone(),
                            msg: format!("Error on astify: {}", msg),
                        });
                    }
                }
                stack.infix.push(Infix {
                    token: token.clone(),
                    precedence: Precedence::PSum,
                    req_args_count: 2,
                    is_statement: false,
                });
                expect_function_as_variable = false;
            }
            TokenPayload::Multiply | TokenPayload::Divide | TokenPayload::Remainder => {
                stack.infix.push(Infix {
                    token: token.clone(),
                    precedence: Precedence::PProduct,
                    req_args_count: 2,
                    is_statement: false,
                });
                expect_function_as_variable = false;
            } // _ => {
              //     return Err(CompilerError {
              //         location: token.begin.clone(),
              //         msg: format!("Unknown token: {:?}", token.token),
              //     })
              // }
        }
    }

    let mut statements = Vec::new();
    while let Some(op) = stack.infix.pop() {
        // How much args does the op need?
        if stack.symbol.len() < op.req_args_count {
            return Err(CompilerError {
                location: op.token.begin.clone(),
                msg: format!("Expecting at least {} arguments", op.req_args_count),
            });
        }

        let mut args = (0..op.req_args_count)
            .map(|_| stack.pop_symbol_as_node().unwrap())
            .collect::<Vec<_>>();
        args.reverse();
        let node = ast::Node {
            root: op.token,
            args,
        };
        if op.is_statement {
            statements.push(node);
        } else {
            stack.symbol.push(Symbol::Finished(node));
        }
    }

    if !stack.symbol.is_empty() {
        return Err(CompilerError::global(&format!(
            "Parser could not process all tokens. Remaining are {:?}",
            stack.symbol
        )));
    }

    statements.reverse();

    Ok(ast::Ast { statements })
}

#[cfg(test)]
mod specs {
    use super::*;
    use crate::{Declaration, Type};
    use ast::{DebugAst, Node};
    use TokenPayload::*;
    #[test]
    fn milestone_1() {
        let tokens = vec![
            Token::stub(Int32(42)),
            Token::stub(Pipe),
            Token::stub(Ident("stdout".to_string())),
        ];

        let context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let actual = parse(&context, &tokens);
        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = ast::Ast {
            statements: vec![ast::Node {
                root: Token::stub(Pipe),
                args: vec![
                    ast::Node::new(Token::stub(Int32(42))),
                    ast::Node::new(Token::stub(Ident("stdout".to_string()))),
                ],
            }],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn function_with_braces() {
        let tokens = vec![
            Token::stub(Ident("stdout".to_string())),
            Token::stub(ParenthesesL),
            Token::stub(Int32(42)),
            Token::stub(ParenthesesR),
        ];

        let context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let actual = parse(&context, &tokens);

        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = ast::Ast {
            statements: vec![ast::Node {
                root: Token::stub(Ident("stdout".to_string())),
                args: vec![ast::Node {
                    root: Token::stub(Int32(42)),
                    args: vec![],
                }],
            }],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn function_without_braces() {
        let tokens = vec![
            Token::stub(Ident("stdout".to_string())),
            Token::stub(Int32(42)),
        ];

        let context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let actual = parse(&context, &tokens);

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let expected = ast::Ast {
            statements: vec![ast::Node {
                root: Token::stub(Ident("stdout".to_string())),
                args: vec![ast::Node {
                    root: Token::stub(Int32(42)),
                    args: vec![],
                }],
            }],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_3_print_sum() {
        let tokens = vec![
            Token::stub(Ident("stdout".to_string())),
            Token::stub(Int32(3)),
            Token::stub(Add),
            Token::stub(Int32(5)),
        ];

        let context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let actual = parse(&context, &tokens);

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let actual = ast::DebugAst::from(actual);

        let expected = ast::DebugAst {
            statements: vec![ast::Node {
                root: Ident("stdout".to_string()),
                args: vec![ast::Node {
                    root: Add,
                    args: vec![
                        ast::Node {
                            root: Int32(3),
                            args: vec![],
                        },
                        ast::Node {
                            root: Int32(5),
                            args: vec![],
                        },
                    ],
                }],
            }],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_3_print_term() {
        let tokens = vec![
            Token::stub(Ident("stdout".to_string())),
            Token::stub(Int32(3)),
            Token::stub(Add),
            Token::stub(Int32(5)),
            Token::stub(Multiply),
            Token::stub(Int32(7)),
        ];

        let context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let actual = parse(&context, &tokens);

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let actual = ast::DebugAst::from(actual);

        let expected = ast::DebugAst {
            statements: vec![ast::Node {
                root: Ident("stdout".to_string()),
                args: vec![ast::Node {
                    root: Add,
                    args: vec![
                        ast::Node {
                            root: Int32(3),
                            args: vec![],
                        },
                        ast::Node {
                            root: Multiply,
                            args: vec![
                                ast::Node {
                                    root: Int32(5),
                                    args: vec![],
                                },
                                ast::Node {
                                    root: Int32(7),
                                    args: vec![],
                                },
                            ],
                        },
                    ],
                }],
            }],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_3_print_term_with_braces() {
        // stdout (3+5)*7
        let tokens = vec![
            Token::stub(Ident("stdout".to_string())),
            Token::stub(ParenthesesL),
            Token::stub(Int32(3)),
            Token::stub(Add),
            Token::stub(Int32(5)),
            Token::stub(ParenthesesR),
            Token::stub(Multiply),
            Token::stub(Int32(7)),
        ];

        let context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let actual = parse(&context, &tokens);

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let actual = ast::DebugAst::from(actual);

        let expected = ast::DebugAst {
            statements: vec![ast::Node {
                root: Ident("stdout".to_string()),
                args: vec![ast::Node {
                    root: Multiply,
                    args: vec![
                        ast::Node {
                            root: Add,
                            args: vec![
                                ast::Node {
                                    root: Int32(3),
                                    args: vec![],
                                },
                                ast::Node {
                                    root: Int32(5),
                                    args: vec![],
                                },
                            ],
                        },
                        ast::Node {
                            root: Int32(7),
                            args: vec![],
                        },
                    ],
                }],
            }],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_3_function_multi_args() {
        // stdout max(3,5)
        let tokens = vec![
            Ident("stdout".to_string()),
            Ident("max".to_string()),
            ParenthesesL,
            Int32(3),
            Delimiter,
            Int32(5),
            ParenthesesR,
        ];

        let context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::function(Type::Void, vec![Type::Int32], true),
                "max".to_string() => Declaration::function(Type::Void, vec![Type::Int32,Type::Int32], false)
            },
        };

        let actual = parse(
            &context,
            &tokens
                .into_iter()
                .map(|t| Token::stub(t))
                .collect::<Vec<_>>(),
        );

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let actual = ast::DebugAst::from(actual);

        let expected = ast::DebugAst {
            statements: vec![ast::Node {
                root: Ident("stdout".to_string()),
                args: vec![ast::Node {
                    root: Ident("max".to_string()),
                    args: vec![
                        ast::Node {
                            root: Int32(3),
                            args: vec![],
                        },
                        ast::Node {
                            root: Int32(5),
                            args: vec![],
                        },
                    ],
                }],
            }],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_3_mvp() {
        let tokens = vec![
            // stdout max(3+5*-7,11*13-15)
            Ident("stdout".to_string()),
            Ident("max".to_string()),
            ParenthesesL,
            Int32(3),
            Add,
            Int32(5),
            Multiply,
            Int32(-7),
            Delimiter,
            Int32(11),
            Multiply,
            Int32(13),
            Subtract,
            Int32(15),
            ParenthesesR,
        ];

        let context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true),
                "max".to_owned() => Declaration::function(Type::Void, vec![Type::Int32,Type::Int32], false)
            },
        };

        let actual = parse(
            &context,
            &tokens
                .into_iter()
                .map(|t| Token::stub(t))
                .collect::<Vec<_>>(),
        );

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let actual = ast::DebugAst::from(actual);

        let expected = DebugAst {
            statements: vec![Node {
                root: Ident("stdout".to_string()),
                args: vec![Node {
                    root: Ident("max".to_string()),
                    args: vec![
                        Node {
                            root: Add,
                            args: vec![
                                Node::new(Int32(3)),
                                Node {
                                    root: Multiply,
                                    args: vec![Node::new(Int32(5)), Node::new(Int32(-7))],
                                },
                            ],
                        },
                        Node {
                            root: Subtract,
                            args: vec![
                                Node {
                                    root: Multiply,
                                    args: vec![Node::new(Int32(11)), Node::new(Int32(13))],
                                },
                                Node::new(Int32(15)),
                            ],
                        },
                    ],
                }],
            }],
        };

        assert_eq!(actual, expected);
    }
}
