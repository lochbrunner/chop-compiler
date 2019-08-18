use crate::compiler::ast;
use crate::compiler::token::{Token, TokenPayload};
use crate::compiler::CompilerError;
use crate::compiler::Context;

#[derive(PartialEq, PartialOrd, Debug, Clone)]
pub enum Precedence {
    Pipe,
}

struct Infix {
    token: Token,
    precedence: Precedence,
}

struct ParseStack {
    pub symbol: Vec<Token>,
    pub infix: Vec<Infix>,
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

/// Turns a slice of tokens into an ast.
/// Using [Shunting-yard algorithm](https://en.wikipedia.org/wiki/Shunting-yard_algorithm#/media/File:Shunting_yard.svg)
pub fn parse(_context: &Context, tokens: &[Token]) -> Result<ast::Ast, CompilerError> {
    let mut stack = ParseStack {
        infix: Vec::new(),
        symbol: Vec::new(),
    };

    let mut statements: Vec<ast::Statement> = Vec::new();

    for token in tokens.iter() {
        match &token.token {
            TokenPayload::Ident(_) => stack.symbol.push(token.clone()),
            TokenPayload::Int32(_) => stack.symbol.push(token.clone()),
            TokenPayload::DefineLocal => (),
            TokenPayload::Pipe => {
                if stack.check_precedence(&Precedence::Pipe) {}
                stack.infix.push(Infix {
                    token: token.clone(),
                    precedence: Precedence::Pipe,
                });
            }
        }
    }

    while let Some(op) = stack.infix.pop() {
        if stack.symbol.len() < 2 {
            return Err(CompilerError {
                location: op.token.begin.clone(),
                msg: "Expecting ".to_owned(),
            });
        }
        let output = stack.symbol.pop().unwrap();
        let input = stack.symbol.pop().unwrap();
        statements.push(ast::Statement {
            root: ast::Node {
                root: op.token,
                args: vec![input, output],
            },
        })
    }

    Ok(ast::Ast { statements })
}

#[cfg(test)]
mod specs {
    use super::*;
    use crate::compiler::{token::Location, Declaration, Type};
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

        let expected = ast::Ast {
            statements: vec![ast::Statement {
                root: ast::Node {
                    root: tokens[1].clone(),
                    args: vec![tokens[0].clone(), tokens[2].clone()],
                },
            }],
        };

        assert_eq!(actual.unwrap(), expected);
    }
}
