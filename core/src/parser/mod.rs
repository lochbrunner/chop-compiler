use crate::ast;
use crate::token::{Token, TokenPayload};
use crate::CompilerError;
use crate::Context;

#[derive(PartialEq, PartialOrd, Debug, Clone)]
pub enum Precedence {
    PCall,
    POpening,
    Pipe,
}

struct Infix {
    token: Token,
    precedence: Precedence,
    req_args_count: usize,
}

enum Symbol {
    Raw(Token),
    Finished(ast::Node),
}

struct ParseStack {
    pub symbol: Vec<Symbol>,
    pub infix: Vec<Infix>,
}
impl ParseStack {
    pub fn pop_symbol_as_node(&mut self) -> Option<ast::Node> {
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
            break;
        }
        match op.token.token {
            TokenPayload::Ident(ref ident) => match ident.as_ref() {
                "stdout" => {
                    if let Some(arg) = stack.pop_symbol_as_node() {
                        stack.symbol.push(Symbol::Finished(ast::Node {
                            root: op.token.clone(),
                            args: vec![arg],
                        }))
                    } else {
                        return Err(format!("Missing argument for function {}", ident));
                    }
                }
                _ => return Err(format!("Unknown function {}", ident)),
            },
            _ => return Err(format!("Unknown token {:?}", op.token.token)),
        }
    }
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
            }),
            TokenPayload::ParenthesesR => {
                if let Err(msg) = astify(context, Precedence::POpening, &mut stack) {
                    return Err(CompilerError {
                        location: token.begin.clone(),
                        msg: format!("Error on astify: {}", msg),
                    });
                }
            }
            TokenPayload::Ident(_) => {
                if expect_function_as_variable {
                    stack.symbol.push(Symbol::Raw(token.clone()));
                } else {
                    stack.infix.push(Infix {
                        token: token.clone(),
                        precedence: Precedence::PCall,
                        req_args_count: 1, // TODO: Remove hard-coded
                    });
                }
                expect_function_as_variable = false;
            }
            TokenPayload::Int32(_) => stack.symbol.push(Symbol::Raw(token.clone())),
            TokenPayload::DefineLocal => (),
            TokenPayload::Pipe => {
                if stack.check_precedence(&Precedence::Pipe) {}
                stack.infix.push(Infix {
                    token: token.clone(),
                    precedence: Precedence::Pipe,
                    req_args_count: 2,
                });
                expect_function_as_variable = true;
            }
        }
    }

    let mut statements: Vec<ast::Node> = Vec::new();
    while let Some(op) = stack.infix.pop() {
        // How much args does the op need?
        if stack.symbol.len() < op.req_args_count {
            return Err(CompilerError {
                location: op.token.begin.clone(),
                msg: "Expecting at least two arguments".to_string(),
            });
        }

        let mut args = (0..op.req_args_count)
            .map(|_| stack.pop_symbol_as_node().unwrap())
            .collect::<Vec<_>>();
        args.reverse();
        statements.push(ast::Node {
                root: op.token,
                args,
        });
    }

    statements.reverse();

    Ok(ast::Ast { statements })
}

#[cfg(test)]
mod specs {
    use super::*;
    use crate::{token::Location, Declaration, Type};
    #[test]
    fn milestone_1() {
        let tokens = vec![
            Token {
                token: TokenPayload::Int32(42),
                begin: Location {
                    line: 3,
                    offset: 28,
                },
                end: Location {
                    line: 3,
                    offset: 30,
                },
            },
            Token {
                token: TokenPayload::Pipe,
                begin: Location {
                    line: 3,
                    offset: 31,
                },
                end: Location {
                    line: 3,
                    offset: 32,
                },
            },
            Token {
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
        ];

        let context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32])
            },
        };

        let actual = parse(&context, &tokens);
        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = ast::Ast {
            statements: vec![ast::Node {
                    root: tokens[1].clone(),
                    args: vec![
                        ast::Node::new(tokens[0].clone()),
                        ast::Node::new(tokens[2].clone()),
                    ],
                }],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn function_with_braces() {
        let tokens = vec![
            Token {
                token: TokenPayload::Ident("stdout".to_string()),
                begin: Location { line: 1, offset: 0 },
                end: Location { line: 1, offset: 6 },
            },
            Token {
                token: TokenPayload::ParenthesesL,
                begin: Location { line: 1, offset: 6 },
                end: Location { line: 1, offset: 7 },
            },
            Token {
                token: TokenPayload::Int32(42),
                begin: Location { line: 1, offset: 7 },
                end: Location { line: 1, offset: 9 },
            },
            Token {
                token: TokenPayload::ParenthesesR,
                begin: Location { line: 1, offset: 9 },
                end: Location {
                    line: 1,
                    offset: 10,
                },
            },
        ];

        let context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32])
            },
        };

        let actual = parse(&context, &tokens);

        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = ast::Ast {
            statements: vec![ast::Node {
                    root: Token {
                        token: TokenPayload::Ident("stdout".to_string()),
                        begin: Location { line: 1, offset: 0 },
                        end: Location { line: 1, offset: 6 },
                    },
                    args: vec![ast::Node {
                        root: Token {
                            token: TokenPayload::Int32(42),
                            begin: Location { line: 1, offset: 7 },
                            end: Location { line: 1, offset: 9 },
                        },
                        args: vec![],
                    }],
                }],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn function_without_braces() {
        let tokens = vec![
            Token {
                token: TokenPayload::Ident("stdout".to_string()),
                begin: Location { line: 1, offset: 0 },
                end: Location { line: 1, offset: 6 },
            },
            Token {
                token: TokenPayload::Int32(42),
                begin: Location { line: 1, offset: 7 },
                end: Location { line: 1, offset: 9 },
            },
        ];

        let context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32])
            },
        };

        let actual = parse(&context, &tokens);

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let expected = ast::Ast {
            statements: vec![ast::Node {
                    root: Token {
                        token: TokenPayload::Ident("stdout".to_string()),
                        begin: Location { line: 1, offset: 0 },
                        end: Location { line: 1, offset: 6 },
                    },
                    args: vec![ast::Node {
                        root: Token {
                            token: TokenPayload::Int32(42),
                            begin: Location { line: 1, offset: 7 },
                            end: Location { line: 1, offset: 9 },
                        },
                        args: vec![],
                    }],
            }],
        };

        assert_eq!(actual, expected);
    }
}
