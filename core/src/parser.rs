use crate::ast;
use crate::ast::{AstTokenPayload, SparseToken};
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
    /// How to handle local declarations with 2 or 3 args?
    req_args_count: usize,
    optional_type: bool,
    is_statement: bool,
}

#[derive(Debug)]
enum Symbol {
    Raw(Token),
    Finished(ast::Node<SparseToken>),
}

impl Symbol {
    pub fn is_type_decl(&self) -> bool {
        if let Symbol::Raw(token) = self {
            token.token == TokenPayload::TypeDeclaration
        } else {
            false
        }
    }
}

#[derive(Debug)]
struct ParseStack {
    // (Symbol, is type)
    pub symbol: Vec<(Symbol, bool)>,
    pub infix: Vec<Infix>,
}

impl ParseStack {
    pub fn new() -> Self {
        Self {
            symbol: Vec::new(),
            infix: Vec::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.infix.is_empty() && self.symbol.is_empty()
    }

    /// The lifetime corresponds to the lifetime of the closure given hold by the ParseStack or by this function
    pub fn pop_symbol_as_node(&mut self) -> Option<(ast::Node<SparseToken>, bool)> {
        match self.symbol.pop() {
            None => None,
            Some((sym, optional)) => Some(match sym {
                Symbol::Raw(token) => match AstTokenPayload::from(token.token) {
                    Err(_) => return None, // TODO: find better solution
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
        // As each TypeDeclaration eats a type token
        let number_of_type_decls = self
            .symbol
            .iter()
            .filter(|(s, _)| s.is_type_decl())
            .fold(0, |acc, _| acc + 1);
        available_symbols - left_braces - number_of_type_decls * 2 == needed_symbols + 1
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
                msg: format!(
                    "[P1]: Expecting at least {} arguments for token {:?}. Got just {}!",
                    op.req_args_count,
                    op.token.token,
                    stack.symbol.len()
                ),
            });
        }
        // Define local can have an optional type argument
        let ignore_type = match op.token.token {
            TokenPayload::DefineLocal => true,
            _ => false,
        };

        let mut args = vec![];
        let mut req_args_count = op.req_args_count;
        while req_args_count > 0 {
            if stack.symbol.is_empty() {
                return Err(op.token.loc.to_error(format!(
                    "Internal Error [P1]: Wrong parsing of arguments for function: {:?}",
                    op.token
                )));
            }
            if let Some((symbol, required)) = stack.pop_symbol_as_node() {
                args.push(symbol);
                if required || !ignore_type {
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
            if node.root.payload == AstTokenPayload::DefineLocal(None) {
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

#[derive(Debug)]
pub struct ParserState {
    token_start: Option<usize>,
    stack: ParseStack,
}

impl ParserState {
    pub fn new() -> Self {
        Self {
            token_start: Some(0),
            stack: ParseStack::new(),
        }
    }
}

/// Returns a single statement using the state as for generator-like behavior.
/// Turns a slice of tokens into an statement.
/// Using [Shunting-yard algorithm](https://en.wikipedia.org/wiki/Shunting-yard_algorithm#/media/File:Shunting_yard.svg)
pub fn parse(
    state: ParserState,
    context: &mut Context,
    tokens: &[Token],
) -> Result<Option<(ast::Node<SparseToken>, ParserState)>, CompilerError> {
    let ParserState {
        mut stack,
        token_start,
    } = state;

    let token_start = if let Some(token_start) = token_start {
        token_start
    } else {
        return Ok(None);
    };
    let mut expect_function_as_variable = false;

    for (i, token) in tokens[token_start..].iter().enumerate() {
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
                        let statement = create_statement(context, &mut stack)?;
                        return Ok(Some((
                            statement,
                            ParserState {
                                token_start: Some(token_start + i),
                                stack,
                            },
                        )));
                    }
                    match context.declarations.get(ident) {
                        None => {
                            if !stack.is_empty() {
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
                                            format!("[P2] Type {} was not defined.", ident),
                                        ));
                                    }
                                } else {
                                    return Err(CompilerError::from_token::<Token>(
                                        token,
                                        format!(
                                            "[P3] Symbol {} was not defined. Stack.symbol: {:?}",
                                            ident, stack.symbol
                                        ),
                                    ));
                                }
                            } else {
                                // New declaration?
                                stack.symbol.push((Symbol::Raw(token.clone()), true));
                            }
                        }
                        Some(declaration) => {
                            if declaration.req_args_count() == 0 {
                                stack
                                    .symbol
                                    .push((Symbol::Raw(token.clone()), !declaration.is_type()));
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
            TokenPayload::Integer(_) | TokenPayload::Float(_) => {
                if stack.is_completable() {
                    let statement = create_statement(context, &mut stack)?;
                    stack.symbol.push((Symbol::Raw(token.clone()), true));

                    return Ok(Some((
                        statement,
                        ParserState {
                            token_start: Some(token_start + i + 1),
                            stack,
                        },
                    )));
                } else {
                    stack.symbol.push((Symbol::Raw(token.clone()), true));
                }
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
        let statement = create_statement(context, &mut stack)?;
        return Ok(Some((
            statement,
            ParserState {
                token_start: None,
                stack,
            },
        )));
    }

    let tokens = stack.symbol.iter().map(|(s, _)| s).collect::<Vec<_>>();
    Err(CompilerError::global(&format!(
        "Parser could not process all tokens. Remaining are {:?}",
        tokens
    )))
}

#[cfg(test)]
mod specs {
    use super::*;
    use ast::{IntegerStub, LexerTokenPayloadStub, Node, StringStub};
    use TokenPayload::*;
    type SparseNode = Node<SparseToken>;

    #[test]
    fn stack_is_completed_milestone_5_mvp() {
        use Precedence::*;
        use Symbol::Raw;
        use TokenPayload::*;
        let stack = ParseStack {
            symbol: vec![
                (Raw(Token::stub(Ident("a".to_owned()))), true),
                (Raw(Token::stub(TypeDeclaration)), false),
                (Raw(Token::stub(Ident("i16".to_owned()))), false),
                (Raw(Token::stub(Integer(3))), true),
            ],
            infix: vec![Infix {
                token: Token::stub(DefineLocal),
                precedence: PCall,
                req_args_count: 2,
                optional_type: true,
                is_statement: true,
            }],
        };

        assert!(stack.is_completable());
    }

    #[test]
    fn stack_is_completed_milestone_5_main() {
        use Precedence::*;
        use Symbol::Raw;
        use TokenPayload::*;
        let stack = ParseStack {
            symbol: vec![
                (Raw(Token::stub(Ident("a".to_owned()))), true),
                (Raw(Token::stub(TypeDeclaration)), false),
                (Raw(Token::stub(Ident("i32".to_owned()))), false),
            ],
            infix: vec![Infix {
                token: Token::stub(DefineLocal),
                precedence: PCall,
                req_args_count: 2,
                optional_type: true,
                is_statement: true,
            }],
        };

        assert!(!stack.is_completable());
    }

    #[test]
    fn stack_is_completed_milestone_5_main_complete() {
        use Precedence::*;
        use Symbol::Raw;
        use TokenPayload::*;
        let stack = ParseStack {
            symbol: vec![
                (Raw(Token::stub(Ident("a".to_owned()))), true),
                (Raw(Token::stub(TypeDeclaration)), false),
                (Raw(Token::stub(Ident("i32".to_owned()))), false),
                (Raw(Token::stub(Integer(3))), true),
            ],
            infix: vec![Infix {
                token: Token::stub(DefineLocal),
                precedence: PCall,
                req_args_count: 2,
                optional_type: true,
                is_statement: true,
            }],
        };

        assert!(stack.is_completable());
    }

    #[test]
    fn stack_is_completed_milestone_5_explicit_complete() {
        use Precedence::*;
        use Symbol::{Finished, Raw};
        use TokenPayload::*;
        let stack = ParseStack {
            symbol: vec![
                (Raw(Token::stub(Ident("b".to_owned()))), true),
                (Raw(Token::stub(TypeDeclaration)), false),
                (Raw(Token::stub(Ident("i8".to_owned()))), false),
                (
                    Finished(Node {
                        root: LexerTokenPayloadStub::stub(Cast),
                        args: vec![
                            Node::leaf(StringStub::stub("a")),
                            Node::leaf(StringStub::stub("i8")),
                        ],
                    }),
                    true,
                ),
                (Raw(Token::stub(Integer(5))), true),
                (Raw(Token::stub(Ident("i8".to_owned()))), false),
            ],
            infix: vec![
                Infix {
                    token: Token::stub(DefineLocal),
                    precedence: PCall,
                    req_args_count: 2,
                    optional_type: true,
                    is_statement: true,
                },
                Infix {
                    token: Token::stub(Add),
                    precedence: PSum,
                    req_args_count: 2,
                    optional_type: false,
                    is_statement: false,
                },
                Infix {
                    token: Token::stub(Cast),
                    precedence: PCast,
                    req_args_count: 2,
                    optional_type: false,
                    is_statement: false,
                },
            ],
        };

        assert!(stack.is_completable());
    }

    fn create_stub(tokens: &[TokenPayload]) -> Vec<Token> {
        tokens
            .into_iter()
            .map(|t| Token::stub(t.clone()))
            .collect::<Vec<_>>()
    }

    fn check_statement(
        state: ParserState,
        context: &mut Context,
        tokens: &[TokenPayload],
        is_final: bool,
    ) -> (SparseNode, ParserState) {
        let statement = parse(state, context, &create_stub(tokens));
        assert_ok!(statement);
        let statement = statement.unwrap();
        assert!(statement.is_some());
        let (statement, state) = statement.unwrap();
        if is_final {
            assert!(state.token_start.is_none());
            assert!(state.stack.infix.is_empty());
            assert!(state.stack.symbol.is_empty());
            assert!(state.stack.is_empty());
        } else {
            assert!(state.token_start.is_some());
        }
        (statement, state)
    }

    #[test]
    fn milestone_1() {
        let tokens = vec![Integer(42), Pipe, Ident("stdout".to_string())];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let (actual, _) = check_statement(ParserState::new(), &mut context, &tokens, true);

        let expected = ast::Node {
            root: LexerTokenPayloadStub::stub(Pipe),
            args: vec![
                ast::Node::leaf(IntegerStub::stub(42)),
                ast::Node::leaf(StringStub::stub("stdout")),
            ],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn function_with_braces() {
        let tokens = vec![
            Ident("stdout".to_string()),
            ParenthesesL,
            Integer(42),
            ParenthesesR,
        ];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let (actual, _) = check_statement(ParserState::new(), &mut context, &tokens, true);

        let expected = ast::Node {
            root: StringStub::stub("stdout"),
            args: vec![ast::Node {
                root: IntegerStub::stub(42),
                args: vec![],
            }],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn function_without_braces() {
        let tokens = vec![Ident("stdout".to_string()), Integer(42)];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };
        let (actual, _) = check_statement(ParserState::new(), &mut context, &tokens, true);

        let expected = ast::Node {
            root: StringStub::stub("stdout"),
            args: vec![ast::Node {
                root: IntegerStub::stub(42),
                args: vec![],
            }],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_3_print_sum() {
        let tokens = vec![Ident("stdout".to_string()), Integer(3), Add, Integer(5)];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let (actual, _) = check_statement(ParserState::new(), &mut context, &tokens, true);

        let actual = ast::DebugNode::from(actual);

        let expected = ast::DebugNode {
            root: AstTokenPayload::from(Ident("stdout".to_string())).unwrap(),
            args: vec![Node {
                root: AstTokenPayload::from(Add).unwrap(),
                args: vec![
                    Node::leaf(AstTokenPayload::from(Integer(3)).unwrap()),
                    Node::leaf(AstTokenPayload::from(Integer(5)).unwrap()),
                ],
            }],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_3_print_term() {
        // stdout 3 + 5*7
        let tokens = vec![
            Ident("stdout".to_string()),
            Integer(3),
            Add,
            Integer(5),
            Multiply,
            Integer(7),
        ];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let (actual, _) = check_statement(ParserState::new(), &mut context, &tokens, true);

        let expected = SparseNode {
            root: StringStub::stub("stdout"),
            args: vec![Node {
                root: LexerTokenPayloadStub::stub(Add),
                args: vec![
                    Node::leaf(IntegerStub::stub(3)),
                    Node {
                        root: LexerTokenPayloadStub::stub(Multiply),
                        args: vec![
                            Node::leaf(IntegerStub::stub(5)),
                            Node::leaf(IntegerStub::stub(7)),
                        ],
                    },
                ],
            }],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_3_print_term_with_braces() {
        // stdout (3+5)*7
        let tokens = vec![
            Ident("stdout".to_string()),
            ParenthesesL,
            Integer(3),
            Add,
            Integer(5),
            ParenthesesR,
            Multiply,
            Integer(7),
        ];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let (actual, _) = check_statement(ParserState::new(), &mut context, &tokens, true);

        let expected = SparseNode {
            root: StringStub::stub("stdout"),
            args: vec![Node {
                root: LexerTokenPayloadStub::stub(Multiply),
                args: vec![
                    Node {
                        root: LexerTokenPayloadStub::stub(Add),
                        args: vec![
                            Node::leaf(IntegerStub::stub(3)),
                            Node::leaf(IntegerStub::stub(5)),
                        ],
                    },
                    Node::leaf(IntegerStub::stub(7)),
                ],
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

        let (actual, _) = check_statement(ParserState::new(), &mut context, &tokens, true);

        let expected = SparseNode {
            root: StringStub::stub("stdout"),
            args: vec![Node {
                root: StringStub::stub("max"),
                args: vec![
                    Node::leaf(IntegerStub::stub(3)),
                    Node::leaf(IntegerStub::stub(5)),
                ],
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

        let (actual, _) = check_statement(ParserState::new(), &mut context, &tokens, true);

        let expected = SparseNode {
            root: StringStub::stub("stdout"),
            args: vec![Node {
                root: StringStub::stub("max"),
                args: vec![
                    Node {
                        root: LexerTokenPayloadStub::stub(Add),
                        args: vec![
                            Node::leaf(IntegerStub::stub(3)),
                            Node {
                                root: LexerTokenPayloadStub::stub(Multiply),
                                args: vec![
                                    Node::leaf(IntegerStub::stub(5)),
                                    Node::leaf(IntegerStub::stub(-7)),
                                ],
                            },
                        ],
                    },
                    Node {
                        root: LexerTokenPayloadStub::stub(Subtract),
                        args: vec![
                            Node {
                                root: LexerTokenPayloadStub::stub(Multiply),
                                args: vec![
                                    Node::leaf(IntegerStub::stub(11)),
                                    Node::leaf(IntegerStub::stub(13)),
                                ],
                            },
                            Node::leaf(IntegerStub::stub(15)),
                        ],
                    },
                ],
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

        let mut context = Context::new();

        let (actual, _) = check_statement(ParserState::new(), &mut context, &tokens, true);

        let expected = SparseNode {
            root: LexerTokenPayloadStub::stub(DefineLocal),
            args: vec![
                Node::leaf(StringStub::stub("a")),
                Node::leaf(IntegerStub::stub(3)),
            ],
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

        let mut context = Context::new();
        let (actual, _) = check_statement(ParserState::new(), &mut context, &tokens, true);

        let expected = SparseNode {
            root: LexerTokenPayloadStub::stub(DefineLocal),
            args: vec![
                Node::leaf(StringStub::stub("a")),
                Node {
                    root: LexerTokenPayloadStub::stub(Add),
                    args: vec![
                        Node::leaf(IntegerStub::stub(3)),
                        Node::leaf(IntegerStub::stub(5)),
                    ],
                },
            ],
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

        let mut actual = Vec::new();
        // a := 3
        let (statement, state) = check_statement(ParserState::new(), &mut context, &tokens, false);
        actual.push(statement);
        // b := a + 5
        let (statement, state) = check_statement(state, &mut context, &tokens, false);
        actual.push(statement);
        // c := 7
        let (statement, state) = check_statement(state, &mut context, &tokens, false);
        actual.push(statement);
        // stdout max(b,c)
        let (statement, _) = check_statement(state, &mut context, &tokens, true);
        actual.push(statement);

        let expected = vec![
            Node {
                root: LexerTokenPayloadStub::stub(DefineLocal),
                args: vec![
                    Node::leaf(StringStub::stub("a")),
                    Node::leaf(IntegerStub::stub(3)),
                ],
            },
            Node {
                root: LexerTokenPayloadStub::stub(DefineLocal),
                args: vec![
                    Node::leaf(StringStub::stub("b")),
                    Node {
                        root: LexerTokenPayloadStub::stub(Add),
                        args: vec![
                            Node::leaf(StringStub::stub("a")),
                            Node::leaf(IntegerStub::stub(5)),
                        ],
                    },
                ],
            },
            Node {
                root: LexerTokenPayloadStub::stub(DefineLocal),
                args: vec![
                    Node::leaf(StringStub::stub("c")),
                    Node::leaf(IntegerStub::stub(7)),
                ],
            },
            Node {
                root: StringStub::stub("stdout"),
                args: vec![Node {
                    root: StringStub::stub("max"),
                    args: vec![
                        Node::leaf(StringStub::stub("b")),
                        Node::leaf(StringStub::stub("c")),
                    ],
                }],
            },
        ];

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

        let mut actual = Vec::new();
        // a: i32 := 3
        let (statement, state) = check_statement(ParserState::new(), &mut context, &tokens, false);
        actual.push(statement);
        // stdout a
        let (statement, _) = check_statement(state, &mut context, &tokens, true);
        actual.push(statement);

        let expected = [
            Node {
                root: LexerTokenPayloadStub::stub(DefineLocal),
                args: vec![
                    Node::leaf(StringStub::stub("a")),
                    Node::leaf(StringStub::stub("i16")),
                    Node::leaf(IntegerStub::stub(3)),
                ],
            },
            Node {
                root: StringStub::stub("stdout"),
                args: vec![Node::leaf(StringStub::stub("a"))],
            },
        ];

        assert_eq!(&actual, &expected);

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

        let mut actual = Vec::new();
        // a: i32 := 3
        let (statement, state) = check_statement(ParserState::new(), &mut context, &tokens, false);
        actual.push(statement);
        // b: i8 := a as i8 + 5
        let (statement, state) = check_statement(state, &mut context, &tokens, false);
        actual.push(statement);
        // c: i8 := 7
        let (statement, state) = check_statement(state, &mut context, &tokens, false);
        actual.push(statement);
        // stdout max(b,c)
        let (statement, _) = check_statement(state, &mut context, &tokens, true);
        actual.push(statement);

        let expected = [
            Node {
                root: LexerTokenPayloadStub::stub(DefineLocal),
                args: vec![
                    Node::leaf(StringStub::stub("a")),
                    Node::leaf(StringStub::stub("i32")),
                    Node::leaf(IntegerStub::stub(3)),
                ],
            },
            Node {
                root: LexerTokenPayloadStub::stub(DefineLocal),
                args: vec![
                    Node::leaf(StringStub::stub("b")),
                    Node::leaf(StringStub::stub("i8")),
                    Node {
                        root: LexerTokenPayloadStub::stub(Add),
                        args: vec![
                            Node {
                                root: LexerTokenPayloadStub::stub(Cast),
                                args: vec![
                                    Node::leaf(StringStub::stub("a")),
                                    Node::leaf(StringStub::stub("i8")),
                                ],
                            },
                            Node::leaf(IntegerStub::stub(5)),
                        ],
                    },
                ],
            },
            Node {
                root: LexerTokenPayloadStub::stub(DefineLocal),
                args: vec![
                    Node::leaf(StringStub::stub("c")),
                    Node::leaf(StringStub::stub("i8")),
                    Node::leaf(IntegerStub::stub(7)),
                ],
            },
            Node {
                root: StringStub::stub("stdout"),
                args: vec![Node {
                    root: StringStub::stub("max"),
                    args: vec![
                        Node::leaf(StringStub::stub("b")),
                        Node::leaf(StringStub::stub("c")),
                    ],
                }],
            },
        ];

        assert_eq!(&actual, &expected);
    }

    #[test]
    fn milestone_5_explicit() {
        let tokens = vec![
            // b: i8 := 3 as i8 + 5 as i8
            Ident("b".to_string()),
            TypeDeclaration,
            Ident("i8".to_string()),
            DefineLocal,
            Integer(3),
            Cast,
            Ident("i8".to_string()),
            Add,
            Integer(5),
            Cast,
            Ident("i8".to_string()),
        ];

        let mut context = Context {
            declarations: hashmap! {},
        };

        let (statement, _) = check_statement(ParserState::new(), &mut context, &tokens, true);

        let expected: Node<SparseToken> = Node {
            root: LexerTokenPayloadStub::stub(DefineLocal),
            args: vec![
                Node::leaf(StringStub::stub("b")),
                Node::leaf(StringStub::stub("i8")),
                Node {
                    root: LexerTokenPayloadStub::stub(Add),
                    args: vec![
                        Node {
                            root: LexerTokenPayloadStub::stub(Cast),
                            args: vec![
                                Node::leaf(IntegerStub::stub(3)),
                                Node::leaf(StringStub::stub("i8")),
                            ],
                        },
                        Node {
                            root: LexerTokenPayloadStub::stub(Cast),
                            args: vec![
                                Node::leaf(IntegerStub::stub(5)),
                                Node::leaf(StringStub::stub("i8")),
                            ],
                        },
                    ],
                },
            ],
        };

        assert_eq!(statement, expected);
    }

    #[test]
    fn create_statement_milestone_5_explicit() {
        use Precedence::*;
        use Symbol::{Finished, Raw};
        use TokenPayload::*;
        let mut stack = ParseStack {
            symbol: vec![
                (Raw(Token::stub(Ident("b".to_owned()))), true),
                (Raw(Token::stub(TypeDeclaration)), false),
                (Raw(Token::stub(Ident("i8".to_owned()))), false),
                (
                    Finished(Node {
                        root: LexerTokenPayloadStub::stub(Cast),
                        args: vec![
                            Node::leaf(StringStub::stub("a")),
                            Node::leaf(StringStub::stub("i8")),
                        ],
                    }),
                    true,
                ),
                (Raw(Token::stub(Integer(5))), true),
                (Raw(Token::stub(Ident("i8".to_owned()))), false),
            ],
            infix: vec![
                Infix {
                    token: Token::stub(DefineLocal),
                    precedence: PCall,
                    req_args_count: 2,
                    optional_type: true,
                    is_statement: true,
                },
                Infix {
                    token: Token::stub(Add),
                    precedence: PSum,
                    req_args_count: 2,
                    optional_type: false,
                    is_statement: false,
                },
                Infix {
                    token: Token::stub(Cast),
                    precedence: PCast,
                    req_args_count: 2,
                    optional_type: false,
                    is_statement: false,
                },
            ],
        };

        let mut context = Context::default();

        let statement = create_statement(&mut context, &mut stack);
        assert_ok!(statement);
        let actual = statement.unwrap();

        let expected: Node<SparseToken> = Node {
            root: LexerTokenPayloadStub::stub(DefineLocal),
            args: vec![
                Node::leaf(StringStub::stub("b")),
                Node::leaf(StringStub::stub("i8")),
                Node {
                    root: LexerTokenPayloadStub::stub(Add),
                    args: vec![
                        Node {
                            root: LexerTokenPayloadStub::stub(Cast),
                            args: vec![
                                Node::leaf(StringStub::stub("a")),
                                Node::leaf(StringStub::stub("i8")),
                            ],
                        },
                        Node {
                            root: LexerTokenPayloadStub::stub(Cast),
                            args: vec![
                                Node::leaf(IntegerStub::stub(5)),
                                Node::leaf(StringStub::stub("i8")),
                            ],
                        },
                    ],
                },
            ],
        };

        assert_eq!(actual, expected);
    }
}
