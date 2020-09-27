use crate::ast;
use crate::ast::{AstTokenPayload, SparseAst, SparseToken};
use crate::declaration::{Context, Declaration, Type};
use crate::error::{CompilerError, ToCompilerError};
use crate::token::{Token, TokenPayload};
use std::rc::Rc;

#[derive(PartialEq, PartialOrd, Debug, Clone)]
pub enum Precedence {
    PCall,
    POpening,
    Pipe,
    PSum,
    PProduct,
    PCast,
}

#[derive(Debug)]
struct Infix {
    token: Token,
    precedence: Precedence,
    req_args_count: usize,
    optional_type: bool,
    is_statement: bool,
}

#[derive(Debug)]
enum Symbol {
    Raw(Token),
    Finished(ast::Node<SparseToken>),
}

#[derive(Debug)]
struct ParseStack {
    pub symbol: Vec<(Symbol, bool)>,
    pub infix: Vec<Infix>,
}

impl ParseStack {
    /// The lifetime corresponds to the lifetime of the closure given hold by the ParseStack or by this function
    pub fn pop_symbol_as_node(&mut self) -> Option<(ast::Node<SparseToken>, bool)> {
        match self.symbol.pop() {
            None => None,
            Some((sym, optional)) => Some(match sym {
                Symbol::Raw(token) => match AstTokenPayload::from(token.token) {
                    Err(_) => return None,
                    Ok(payload) => (
                        ast::Node {
                            root: SparseToken {
                                payload,
                                return_type: Rc::new(&|_| None),
                                loc: token.loc,
                            },
                            args: vec![],
                        },
                        optional,
                    ),
                },
                Symbol::Finished(node) => (node, optional),
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

    /// For instance a := b+c
    pub fn is_completable(&self) -> bool {
        if self.infix.is_empty() {
            return false;
        }
        let needed_symbols = self.infix.iter().fold(0, |acc, op| acc + op.req_args_count);
        let left_braces = self
            .infix
            .iter()
            .filter(|op| op.token.token == TokenPayload::ParenthesesL)
            .fold(0, |acc, _| acc + 1);
        let available_symbols = self.symbol.len() + self.infix.len();
        // Find types
        let optional_symbols = self
            .symbol
            .iter()
            .filter(|sym| !sym.1)
            .fold(0, |acc, _| acc + 1);
        available_symbols - left_braces - optional_symbols == needed_symbols + 1
    }

    pub fn last_symbol_is(&self, payload: &TokenPayload) -> bool {
        if let Some(symbol) = self.symbol.last() {
            match symbol {
                (Symbol::Raw(symbol), _) => &symbol.token == payload,
                _ => false,
            }
        } else {
            false
        }
    }

    pub fn last_operator_is(&self, payload: &TokenPayload) -> bool {
        if let Some(ref op) = self.infix.last() {
            &op.token.token == payload
        } else {
            false
        }
    }
}

fn astify<'a, 'b>(
    _context: &Context,
    till: Precedence,
    stack: &'b mut ParseStack,
) -> Result<(), String>
where
    'a: 'b,
{
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
        let mut args: Vec<ast::Node<ast::SparseToken>> = Vec::with_capacity(op.req_args_count);
        for _ in 0..op.req_args_count {
            let (node, _): (ast::Node<ast::SparseToken>, _) = stack.pop_symbol_as_node().unwrap();
            args.push(node)
        }
        // let mut args: Vec<ast::Node<ast::SparseToken<'a>>> = (0..op.req_args_count)
        //     .map(|_| stack.pop_symbol_as_node().unwrap().0)
        //     .collect::<Vec<_>>();
        args.reverse();
        stack.symbol.push((
            Symbol::Finished(ast::Node {
                root: SparseToken {
                    payload: AstTokenPayload::from(op.token.token)?,
                    loc: op.token.loc,
                    return_type: Rc::new(|_| None),
                },
                args,
            }),
            true,
        ));
    }

    Ok(())
}

fn create_statement<'a>(
    context: &mut Context,
    stack: &'a mut ParseStack,
) -> Result<ast::Node<SparseToken>, CompilerError> {
    while let Some(op) = stack.infix.pop() {
        // How much args does the op need?
        if stack.symbol.len() < op.req_args_count {
            return Err(CompilerError {
                location: op.token.loc.clone(),
                msg: format!("Expecting at least {} arguments", op.req_args_count),
            });
        }
        let mut args = vec![];
        let mut req_args_count = op.req_args_count;
        while req_args_count > 0 {
            if let Some((symbol, required)) = stack.pop_symbol_as_node() {
                args.push(symbol);
                if required {
                    req_args_count -= 1;
                }
            }
        }
        args.reverse();
        let node = ast::Node::<SparseToken> {
            root: SparseToken {
                payload: AstTokenPayload::from(op.token.token).convert(&op.token.loc)?,
                loc: op.token.loc,
                return_type: Rc::new(|_| None),
            },
            args,
        };
        if op.is_statement {
            if node.root.payload == AstTokenPayload::DefineLocal {
                // TODO: First attempt only
                // Get ident
                let first_token = &node.args.get(0).unwrap().root.payload;
                // Get Type if available, else use default type
                let type_token = if node.args.len() == 3 {
                    Type::from_sparse_token(&node.args.get(1).unwrap().root)
                } else {
                    Type::Int32
                };
                if let AstTokenPayload::Symbol(ref ident) = first_token {
                    context.declarations.insert(
                        ident.clone(),
                        Declaration::function(type_token, vec![], false),
                    );
                } else {
                    return Err(CompilerError::global(&format!(
                        "Left of definition must be an identifier, not {:?}",
                        node.args
                    )));
                }
            }
            return Ok(node);
        } else {
            stack.symbol.push((Symbol::Finished(node), true));
        }
    }
    Err(CompilerError::global(&format!(
        "Parser could not process all tokens. Remaining are {:?}",
        stack.symbol.iter().map(|i| &i.0).collect::<Vec<_>>()
    )))
}

pub fn is_known_type(_context: &Context, ident: &str) -> bool {
    match ident {
        "i8" | "i16" | "i32" | "i64" => true,
        "u8" | "u16" | "u32" | "u64" => true,
        "f8" | "f16" | "f32" | "f64" => true,
        _ => false,
    }
}

/// Turns a slice of tokens into an ast.
/// Using [Shunting-yard algorithm](https://en.wikipedia.org/wiki/Shunting-yard_algorithm#/media/File:Shunting_yard.svg)
pub fn parse(context: &mut Context, tokens: &[Token]) -> Result<SparseAst, CompilerError> {
    let mut stack = ParseStack {
        infix: Vec::new(),
        symbol: Vec::new(),
    };

    let mut expect_function_as_variable = false;
    let mut statements = Vec::new();

    for token in tokens.iter() {
        match &token.token {
            TokenPayload::ParenthesesL => stack.infix.push(Infix {
                token: token.clone(),
                precedence: Precedence::POpening,
                req_args_count: 0,
                is_statement: false,
                optional_type: false,
            }),
            TokenPayload::Delimiter => {
                if let Err(msg) = astify(context, Precedence::POpening, &mut stack) {
                    return Err(CompilerError::from_token::<Token>(
                        token,
                        format!("Error on astify: {}", msg),
                    ));
                }
            }
            TokenPayload::ParenthesesR => {
                if let Err(msg) = astify(context, Precedence::POpening, &mut stack) {
                    return Err(CompilerError::from_token::<Token>(
                        token,
                        format!("Error on astify: {}", msg),
                    ));
                }
                stack.infix.pop();
            }
            TokenPayload::Ident(ident) => {
                if expect_function_as_variable {
                    stack.symbol.push((Symbol::Raw(token.clone()), true));
                } else {
                    if stack.is_completable() {
                        statements.push(create_statement(context, &mut stack)?);
                    }
                    match context.declarations.get(ident) {
                        None => {
                            if !(stack.infix.is_empty() && stack.symbol.is_empty()) {
                                if stack.last_symbol_is(&TokenPayload::TypeDeclaration)
                                    || stack.last_operator_is(&TokenPayload::Cast)
                                {
                                    if is_known_type(&context, ident) {
                                        stack.symbol.push((
                                            Symbol::Raw(token.clone()),
                                            stack.last_operator_is(&TokenPayload::Cast),
                                        ));
                                    } else {
                                        return Err(CompilerError::from_token::<Token>(
                                            token,
                                            format!("Type {} was not defined.", ident),
                                        ));
                                    }
                                } else {
                                    return Err(CompilerError::from_token::<Token>(
                                        token,
                                        format!("Symbol {} was not defined.", ident),
                                    ));
                                }
                            } else {
                                // New declaration?
                                stack.symbol.push((Symbol::Raw(token.clone()), true));
                            }
                        }
                        Some(declaration) => {
                            if declaration.req_args_count() == 0 {
                                stack.symbol.push((Symbol::Raw(token.clone()), true));
                            } else {
                                stack.infix.push(Infix {
                                    token: token.clone(),
                                    precedence: Precedence::PCall,
                                    req_args_count: declaration.req_args_count(),
                                    is_statement: declaration.is_statement,
                                    optional_type: false,
                                });
                            }
                        }
                    };
                }
                expect_function_as_variable = false;
            }
            TokenPayload::Integer(_) => {
                if stack.is_completable() {
                    statements.push(create_statement(context, &mut stack)?);
                }
                stack.symbol.push((Symbol::Raw(token.clone()), true));
            }
            TokenPayload::DefineLocal => {
                if stack.symbol.is_empty() {
                    return Err(CompilerError {
                        location: token.loc.clone(),
                        msg: "No identifer for new definition found!".to_string(),
                    });
                } else {
                    stack.infix.push(Infix {
                        is_statement: true,
                        req_args_count: 2,
                        token: token.clone(),
                        precedence: Precedence::PCall,
                        optional_type: true,
                    });
                }
            }
            TokenPayload::TypeDeclaration => {
                stack.symbol.push((Symbol::Raw(token.clone()), false));
            }
            TokenPayload::Pipe => {
                if stack.check_precedence(&Precedence::Pipe) {
                    if let Err(msg) = astify(context, Precedence::Pipe, &mut stack) {
                        return Err(CompilerError {
                            location: token.loc.clone(),
                            msg: format!("Error on astify: {}", msg),
                        });
                    }
                }
                stack.infix.push(Infix {
                    token: token.clone(),
                    precedence: Precedence::Pipe,
                    req_args_count: 2,
                    is_statement: true, // TODO: This is not completely correct
                    optional_type: false,
                });
                expect_function_as_variable = true;
            }
            TokenPayload::Add | TokenPayload::Subtract => {
                if stack.check_precedence(&Precedence::PSum) {
                    if let Err(msg) = astify(context, Precedence::PSum, &mut stack) {
                        return Err(CompilerError {
                            location: token.loc.clone(),
                            msg: format!("Error on astify: {}", msg),
                        });
                    }
                }
                stack.infix.push(Infix {
                    token: token.clone(),
                    precedence: Precedence::PSum,
                    req_args_count: 2,
                    is_statement: false,
                    optional_type: false,
                });
                expect_function_as_variable = false;
            }
            TokenPayload::Multiply | TokenPayload::Divide | TokenPayload::Remainder => {
                stack.infix.push(Infix {
                    token: token.clone(),
                    precedence: Precedence::PProduct,
                    req_args_count: 2,
                    is_statement: false,
                    optional_type: false,
                });
                expect_function_as_variable = false;
            }
            TokenPayload::Cast => {
                if stack.check_precedence(&Precedence::PCast) {
                    if let Err(msg) = astify(context, Precedence::PCast, &mut stack) {
                        return Err(CompilerError {
                            location: token.loc.clone(),
                            msg: format!("Error on astify: {}", msg),
                        });
                    }
                }
                stack.infix.push(Infix {
                    token: token.clone(),
                    precedence: Precedence::PCast,
                    req_args_count: 2,
                    is_statement: false,
                    optional_type: false,
                });
            } // _ => {
              //     return Err(CompilerError {
              //         location: token.begin.clone(),
              //         msg: format!("Unknown token: {:?}", token.token),
              //     })
              // }
        }
    }

    if stack.is_completable() {
        statements.push(create_statement(context, &mut stack)?);
    }

    if !stack.symbol.is_empty() {
        return Err(CompilerError::global(&format!(
            "Parser could not process all tokens. Remaining are {:?}",
            stack.symbol
        )));
    }

    Ok(ast::Ast { statements })
}

#[cfg(test)]
mod specs {
    use super::*;
    use ast::Node;
    use TokenPayload::*;
    #[test]
    fn milestone_1() {
        let tokens = vec![
            Token::stub(Integer(42)),
            Token::stub(Pipe),
            Token::stub(Ident("stdout".to_string())),
        ];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let actual = parse(&mut context, &tokens);
        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = ast::Ast {
            statements: vec![ast::Node {
                root: SparseToken::stub(Pipe),
                args: vec![
                    ast::Node::leaf(SparseToken::stub(Integer(42))),
                    ast::Node::leaf(SparseToken::stub(Ident("stdout".to_string()))),
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
            Token::stub(Integer(42)),
            Token::stub(ParenthesesR),
        ];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let actual = parse(&mut context, &tokens);

        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = ast::Ast {
            statements: vec![ast::Node {
                root: SparseToken::stub(Ident("stdout".to_string())),
                args: vec![ast::Node {
                    root: SparseToken::stub(Integer(42)),
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
            Token::stub(Integer(42)),
        ];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let actual = parse(&mut context, &tokens);

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let expected = ast::Ast {
            statements: vec![ast::Node {
                root: SparseToken::stub(Ident("stdout".to_string())),
                args: vec![ast::Node {
                    root: SparseToken::stub(Integer(42)),
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
            Token::stub(Integer(3)),
            Token::stub(Add),
            Token::stub(Integer(5)),
        ];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let actual = parse(&mut context, &tokens);

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let actual = ast::DebugAst::from(actual);

        let expected = ast::DebugAst {
            statements: vec![Node {
                root: AstTokenPayload::from(Ident("stdout".to_string())).unwrap(),
                args: vec![Node {
                    root: AstTokenPayload::from(Add).unwrap(),
                    args: vec![
                        Node::leaf(AstTokenPayload::from(Integer(3)).unwrap()),
                        Node::leaf(AstTokenPayload::from(Integer(5)).unwrap()),
                    ],
                }],
            }],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_3_print_term() {
        // stdout 3 + 5*7
        let tokens = vec![
            Token::stub(Ident("stdout".to_string())),
            Token::stub(Integer(3)),
            Token::stub(Add),
            Token::stub(Integer(5)),
            Token::stub(Multiply),
            Token::stub(Integer(7)),
        ];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let actual = parse(&mut context, &tokens);

        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = ast::SparseAst {
            statements: vec![Node {
                root: SparseToken::stub(Ident("stdout".to_string())),
                args: vec![Node {
                    root: SparseToken::stub(Add),
                    args: vec![
                        Node::leaf(SparseToken::stub(Integer(3))),
                        Node {
                            root: SparseToken::stub(Multiply),
                            args: vec![
                                Node::leaf(SparseToken::stub(Integer(5))),
                                Node::leaf(SparseToken::stub(Integer(7))),
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
            Token::stub(Integer(3)),
            Token::stub(Add),
            Token::stub(Integer(5)),
            Token::stub(ParenthesesR),
            Token::stub(Multiply),
            Token::stub(Integer(7)),
        ];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let actual = parse(&mut context, &tokens);

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        // let actual = ast::DebugAst::from(actual);

        let expected = ast::SparseAst {
            statements: vec![Node {
                root: SparseToken::stub(Ident("stdout".to_string())),
                args: vec![Node {
                    root: SparseToken::stub(Multiply),
                    args: vec![
                        Node {
                            root: SparseToken::stub(Add),
                            args: vec![
                                Node::leaf(SparseToken::stub(Integer(3))),
                                Node::leaf(SparseToken::stub(Integer(5))),
                            ],
                        },
                        Node::leaf(SparseToken::stub(Integer(7))),
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
            Integer(3),
            Delimiter,
            Integer(5),
            ParenthesesR,
        ];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::function(Type::Void, vec![Type::Int32], true),
                "max".to_string() => Declaration::function(Type::Void, vec![Type::Int32,Type::Int32], false)
            },
        };

        let actual = parse(
            &mut context,
            &tokens
                .into_iter()
                .map(|t| Token::stub(t))
                .collect::<Vec<_>>(),
        );

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        // let actual = ast::DebugAst::from(actual);

        let expected = ast::SparseAst {
            statements: vec![Node {
                root: SparseToken::stub(Ident("stdout".to_string())),
                args: vec![Node {
                    root: SparseToken::stub(Ident("max".to_string())),
                    args: vec![
                        Node::leaf(SparseToken::stub(Integer(3))),
                        Node::leaf(SparseToken::stub(Integer(5))),
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
            Integer(3),
            Add,
            Integer(5),
            Multiply,
            Integer(-7),
            Delimiter,
            Integer(11),
            Multiply,
            Integer(13),
            Subtract,
            Integer(15),
            ParenthesesR,
        ];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true),
                "max".to_owned() => Declaration::function(Type::Void, vec![Type::Int32,Type::Int32], false)
            },
        };

        let actual = parse(
            &mut context,
            &tokens
                .into_iter()
                .map(|t| Token::stub(t))
                .collect::<Vec<_>>(),
        );

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        // let actual = ast::DebugAst::from(actual);

        let expected = SparseAst {
            statements: vec![Node {
                root: SparseToken::stub(Ident("stdout".to_string())),
                args: vec![Node {
                    root: SparseToken::stub(Ident("max".to_string())),
                    args: vec![
                        Node {
                            root: SparseToken::stub(Add),
                            args: vec![
                                Node::leaf(SparseToken::stub(Integer(3))),
                                Node {
                                    root: SparseToken::stub(Multiply),
                                    args: vec![
                                        Node::leaf(SparseToken::stub(Integer(5))),
                                        Node::leaf(SparseToken::stub(Integer(-7))),
                                    ],
                                },
                            ],
                        },
                        Node {
                            root: SparseToken::stub(Subtract),
                            args: vec![
                                Node {
                                    root: SparseToken::stub(Multiply),
                                    args: vec![
                                        Node::leaf(SparseToken::stub(Integer(11))),
                                        Node::leaf(SparseToken::stub(Integer(13))),
                                    ],
                                },
                                Node::leaf(SparseToken::stub(Integer(15))),
                            ],
                        },
                    ],
                }],
            }],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_4_definition_with_value() {
        let tokens = vec![
            // a := 3
            Ident("a".to_string()),
            DefineLocal,
            Integer(3),
        ];

        let mut context = Context {
            declarations: hashmap! {},
        };

        let actual = parse(
            &mut context,
            &tokens
                .into_iter()
                .map(|t| Token::stub(t))
                .collect::<Vec<_>>(),
        );

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        // let actual = ast::DebugAst::from(actual);
        let expected = SparseAst {
            statements: vec![Node {
                root: SparseToken::stub(DefineLocal),
                args: vec![
                    Node::leaf(SparseToken::stub(Ident("a".to_string()))),
                    Node::leaf(SparseToken::stub(Integer(3))),
                ],
            }],
        };
        assert_eq!(actual, expected);
        // Declaration
        assert!(context.declarations.get("a").is_some());
        let actual_declaration = context.declarations.get("a").unwrap();
        let expected_declaration = Declaration::function(Type::Int32, vec![], false);

        assert_eq!(actual_declaration, &expected_declaration);
    }

    #[test]
    fn milestone_4_definition_with_term() {
        let tokens = vec![
            // a := 3+5
            Ident("a".to_string()),
            DefineLocal,
            Integer(3),
            Add,
            Integer(5),
        ];

        let mut context = Context {
            declarations: hashmap! {},
        };

        let actual = parse(
            &mut context,
            &tokens
                .into_iter()
                .map(|t| Token::stub(t))
                .collect::<Vec<_>>(),
        );

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        // let actual = ast::DebugAst::from(actual);
        let expected = SparseAst {
            statements: vec![Node {
                root: SparseToken::stub(DefineLocal),
                args: vec![
                    Node::leaf(SparseToken::stub(Ident("a".to_string()))),
                    Node {
                        root: SparseToken::stub(Add),
                        args: vec![
                            Node::leaf(SparseToken::stub(Integer(3))),
                            Node::leaf(SparseToken::stub(Integer(5))),
                        ],
                    },
                ],
            }],
        };
        assert_eq!(actual, expected);
        // Declaration
        assert!(context.declarations.get("a").is_some());
        let actual_declaration = context.declarations.get("a").unwrap();
        let expected_declaration = Declaration::function(Type::Int32, vec![], false);

        assert_eq!(actual_declaration, &expected_declaration);
    }

    #[test]
    fn milestone_4_main() {
        let tokens = vec![
            // a := 3
            Ident("a".to_string()),
            DefineLocal,
            Integer(3),
            // b := a + 5
            Ident("b".to_string()),
            DefineLocal,
            Ident("a".to_string()),
            Add,
            Integer(5),
            // c := 7
            Ident("c".to_string()),
            DefineLocal,
            Integer(7),
            // stdout max(b,c)
            Ident("stdout".to_string()),
            Ident("max".to_string()),
            ParenthesesL,
            Ident("b".to_string()),
            Delimiter,
            Ident("c".to_string()),
            ParenthesesR,
        ];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::full_template_statement(1),
                "max".to_string() => Declaration::full_template_function(2),
            },
        };

        let actual = parse(
            &mut context,
            &tokens
                .into_iter()
                .map(|t| Token::stub(t))
                .collect::<Vec<_>>(),
        );

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        // let actual = ast::DebugAst::from(actual.unwrap());
        let expected = SparseAst {
            statements: vec![
                Node {
                    root: SparseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(SparseToken::stub(Ident("a".to_string()))),
                        Node::leaf(SparseToken::stub(Integer(3))),
                    ],
                },
                Node {
                    root: SparseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(SparseToken::stub(Ident("b".to_string()))),
                        Node {
                            root: SparseToken::stub(Add),
                            args: vec![
                                Node::leaf(SparseToken::stub(Ident("a".to_string()))),
                                Node::leaf(SparseToken::stub(Integer(5))),
                            ],
                        },
                    ],
                },
                Node {
                    root: SparseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(SparseToken::stub(Ident("c".to_string()))),
                        Node::leaf(SparseToken::stub(Integer(7))),
                    ],
                },
                Node {
                    root: SparseToken::stub(Ident("stdout".to_string())),
                    args: vec![Node {
                        root: SparseToken::stub(Ident("max".to_string())),
                        args: vec![
                            Node::leaf(SparseToken::stub(Ident("b".to_string()))),
                            Node::leaf(SparseToken::stub(Ident("c".to_string()))),
                        ],
                    }],
                },
            ],
        };

        assert_eq!(actual, expected);

        assert!(context.declarations.get("a").is_some());
        let actual = context.declarations.get("a").unwrap();
        let expected = Declaration::variable(Type::Int32);
        assert_eq!(actual, &expected);

        assert!(context.declarations.get("b").is_some());
        let actual = context.declarations.get("b").unwrap();
        let expected = Declaration::variable(Type::Int32);
        assert_eq!(actual, &expected);

        assert!(context.declarations.get("c").is_some());
        let actual = context.declarations.get("c").unwrap();
        let expected = Declaration::variable(Type::Int32);
        assert_eq!(actual, &expected);
    }

    #[test]
    fn milestone_5_mvp() {
        let tokens = vec![
            // a: i32 := 3
            Ident("a".to_string()),
            TypeDeclaration,
            Ident("i16".to_string()),
            DefineLocal,
            Integer(3),
            // stdout a
            Ident("stdout".to_string()),
            Ident("a".to_string()),
        ];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::full_template_statement(1),
            },
        };

        let actual = parse(
            &mut context,
            &tokens
                .into_iter()
                .map(|t| Token::stub(t))
                .collect::<Vec<_>>(),
        );

        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = ast::SparseAst {
            statements: vec![
                Node {
                    root: SparseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(SparseToken::stub(Ident("a".to_string()))),
                        Node::leaf(SparseToken::stub(Ident("i16".to_string()))),
                        Node::leaf(SparseToken::stub(Integer(3))),
                    ],
                },
                Node {
                    root: SparseToken::stub(Ident("stdout".to_string())),
                    args: vec![Node::leaf(SparseToken::stub(Ident("a".to_string())))],
                },
            ],
        };

        assert_eq!(actual, expected);

        assert!(context.declarations.get("a").is_some());
        let actual = context.declarations.get("a").unwrap();
        let expected = Declaration::variable(Type::Int16);
        assert_eq!(actual, &expected);
    }

    #[test]
    fn milestone_5_main() {
        let tokens = vec![
            // a: i32 := 3
            Ident("a".to_string()),
            TypeDeclaration,
            Ident("i32".to_string()),
            DefineLocal,
            Integer(3),
            // b: i8 := a as i8 + 5
            Ident("b".to_string()),
            TypeDeclaration,
            Ident("i8".to_string()),
            DefineLocal,
            Ident("a".to_string()),
            Cast,
            Ident("i8".to_string()),
            Add,
            Integer(5),
            // c: i8 := 7
            Ident("c".to_string()),
            TypeDeclaration,
            Ident("i8".to_string()),
            DefineLocal,
            Integer(7),
            // stdout max(b,c)
            Ident("stdout".to_string()),
            Ident("max".to_string()),
            ParenthesesL,
            Ident("b".to_string()),
            Delimiter,
            Ident("c".to_string()),
            ParenthesesR,
        ];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::full_template_statement(1),
                "max".to_string() => Declaration::full_template_function(2),
            },
        };

        let actual = parse(
            &mut context,
            &tokens
                .into_iter()
                .map(|t| Token::stub(t))
                .collect::<Vec<_>>(),
        );

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        // let actual = ast::DebugAst::from(actual.unwrap());

        let expected = ast::SparseAst {
            statements: vec![
                Node {
                    root: SparseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(SparseToken::stub(Ident("a".to_string()))),
                        Node::leaf(SparseToken::stub(Ident("i32".to_string()))),
                        Node::leaf(SparseToken::stub(Integer(3))),
                    ],
                },
                Node {
                    root: SparseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(SparseToken::stub(Ident("b".to_string()))),
                        Node::leaf(SparseToken::stub(Ident("i8".to_string()))),
                        Node {
                            root: SparseToken::stub(Add),
                            args: vec![
                                Node {
                                    root: SparseToken::stub(Cast),
                                    args: vec![
                                        Node::leaf(SparseToken::stub(Ident("a".to_string()))),
                                        Node::leaf(SparseToken::stub(Ident("i8".to_string()))),
                                    ],
                                },
                                Node::leaf(SparseToken::stub(Integer(5))),
                            ],
                        },
                    ],
                },
                Node {
                    root: SparseToken::stub(DefineLocal),
                    args: vec![
                        Node::leaf(SparseToken::stub(Ident("c".to_string()))),
                        Node::leaf(SparseToken::stub(Ident("i8".to_string()))),
                        Node::leaf(SparseToken::stub(Integer(7))),
                    ],
                },
                Node {
                    root: SparseToken::stub(Ident("stdout".to_string())),
                    args: vec![Node {
                        root: SparseToken::stub(Ident("max".to_string())),
                        args: vec![
                            Node::leaf(SparseToken::stub(Ident("b".to_string()))),
                            Node::leaf(SparseToken::stub(Ident("c".to_string()))),
                        ],
                    }],
                },
            ],
        };

        assert_eq!(actual, expected);
    }
}
