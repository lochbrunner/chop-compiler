use crate::ast;
use crate::ast::{AstTokenPayload, SparseToken};
use crate::declaration::{Context, Declaration, Type};
use crate::error::{CompilerError, Location, ToCompilerError};
use crate::token::{Token, TokenPayload};
use std::env;
use std::rc::Rc;

#[derive(PartialEq, PartialOrd, Debug, Clone)]
pub enum Precedence {
    POpening,
    PCall,
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
    optional_type: bool, // ?
    // If it returns void.
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

    pub fn location(&self) -> &Location {
        match self {
            Self::Raw(token) => &token.loc,
            Self::Finished(node) => &node.root.loc,
        }
    }
}

#[derive(Debug)]
struct ParseStack {
    pub symbol: Vec<Symbol>,
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
    pub fn pop_symbol_as_node(&mut self) -> Option<ast::Node<SparseToken>> {
        match self.symbol.pop() {
            None => None,
            Some(sym) => Some(match sym {
                Symbol::Raw(token) => match AstTokenPayload::from(token.token) {
                    Err(_) => return None, // TODO: find better solution
                    Ok(payload) => ast::Node {
                        root: SparseToken {
                            payload,
                            return_type: Rc::new(&|_| None),
                            loc: token.loc,
                        },
                        args: vec![],
                    },
                },
                Symbol::Finished(node) => node,
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
        if self.infix.last().unwrap().token.token == TokenPayload::ParenthesesL {
            return false;
        }
        let needed_symbols = self.infix.iter().fold(0, |acc, op| acc + op.req_args_count);
        let left_braces = self
            .infix
            .iter()
            .filter(|op| {
                op.token.token == TokenPayload::ParenthesesL
                    || op.token.token == TokenPayload::BraceL
            })
            .fold(0, |acc, _| acc + 1);
        let available_symbols = self.symbol.len() + self.infix.len();
        // Find types
        // As each TypeDeclaration eats a type token
        let number_of_type_decls = self
            .symbol
            .iter()
            .filter(|s| s.is_type_decl())
            .fold(0, |acc, _| acc + 1);
        available_symbols - left_braces - number_of_type_decls * 2 == needed_symbols + 1
    }

    pub fn last_symbol_is(&self, payload: &TokenPayload) -> bool {
        if let Some(symbol) = self.symbol.last() {
            match symbol {
                Symbol::Raw(symbol) => &symbol.token == payload,
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
            let node: ast::Node<ast::SparseToken> = stack.pop_symbol_as_node().unwrap();
            args.push(node)
        }
        args.reverse();
        stack.symbol.push(Symbol::Finished(ast::Node {
            root: SparseToken {
                payload: AstTokenPayload::from(op.token.token)?,
                loc: op.token.loc,
                return_type: Rc::new(|_| None),
            },
            args,
        }));
    }

    Ok(())
}

fn is_astifyable(stack: &ParseStack) -> bool {
    if let Some(op) = stack.infix.last() {
        if op.token.is_operator() {
            stack.symbol.len() >= op.req_args_count
        } else {
            stack
                .symbol
                .iter()
                .filter(|t| t.location() > &op.token.loc)
                .count()
                >= op.req_args_count
        }
    } else {
        false
    }
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
            let is_decl_or_type = if let Some(e) = stack.symbol.last() {
                if let Symbol::Raw(s) = e {
                    match s.token {
                        TokenPayload::Ident(ref arg_ident) => {
                            if let Some(arg_decl) = context.declarations.get(arg_ident) {
                                arg_decl.is_type()
                            } else {
                                false
                            }
                        }
                        TokenPayload::TypeDeclaration => true,
                        _ => false,
                    }
                } else {
                    false
                }
            } else {
                false
            };
            if let Some(symbol) = stack.pop_symbol_as_node() {
                args.push(symbol);
                if !is_decl_or_type || !ignore_type {
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
            stack.symbol.push(Symbol::Finished(node));
        }
    }
    Err(CompilerError::global(&format!(
        "[P6] Parser could not process all tokens. Remaining are {:?}",
        stack.symbol
    )))
}

#[derive(Debug)]
pub struct ExportItem {
    pub name: String,
}

#[derive(Debug)]
pub struct ParserState {
    token_start: usize,
    stack: ParseStack,
    // For more than 15 items a Vec is faster than a HashMap.
    // https://gist.github.com/daboross/976978d8200caf86e02acb6805961195
    // exported: Vec<ExportItem>,
}

impl ParserState {
    pub fn new() -> Self {
        Self {
            token_start: 0,
            stack: ParseStack::new(),
            // exported: Vec::new(),
        }
    }
}

/// Returns a single statement using the state as for generator-like behavior.
/// Turns a slice of tokens into an statement.
/// Using [Shunting-yard algorithm](https://en.wikipedia.org/wiki/Shunting-yard_algorithm#/media/File:Shunting_yard.svg)
fn parse_impl(
    state: ParserState,
    context: &mut Context,
    tokens: &[Token],
) -> Result<(ast::Scope<SparseToken>, usize), CompilerError> {
    let ParserState {
        mut stack,
        token_start,
        // exported: _,
    } = state;

    let mut scope: ast::Scope<SparseToken> = Default::default();
    let mut expect_function_as_variable = false;
    let mut i = token_start;
    while i < tokens.len() {
        let token = &tokens[i];
        i += 1;
        match &token.token {
            TokenPayload::ParenthesesL => stack.infix.push(Infix {
                token: token.clone(),
                precedence: Precedence::POpening,
                req_args_count: 0,
                is_statement: false,
                optional_type: false,
            }),
            TokenPayload::Delimiter => {
                if is_astifyable(&stack) {
                    if let Err(msg) = astify(context, Precedence::POpening, &mut stack) {
                        return Err(CompilerError::from_token::<Token>(
                            token,
                            format!("[P3] Error on astify: {}", msg),
                        ));
                    }
                }
            }
            TokenPayload::Dot => {
                unimplemented!();
            }
            TokenPayload::ParenthesesR => {
                if let Err(msg) = astify(context, Precedence::POpening, &mut stack) {
                    return Err(CompilerError::from_token::<Token>(
                        token,
                        format!("[P4] Error on astify: {}", msg),
                    ));
                }
                stack.infix.pop();
            }
            TokenPayload::BraceL => {
                if stack.is_completable() {
                    let statement = create_statement(context, &mut stack)?;
                    scope.statements.push(ast::Statement::InScope(statement));
                }
                let (inner_scope, new_i) = parse_impl(
                    ParserState {
                        token_start: i,
                        stack: ParseStack::new(),
                        // exported: Vec::new(),
                    },
                    context,
                    tokens,
                )?;
                i = new_i;
                scope.statements.push(ast::Statement::Nested(inner_scope));
            }
            TokenPayload::BraceR => {
                if stack.is_completable() {
                    let statement = create_statement(context, &mut stack)?;
                    scope.statements.push(ast::Statement::InScope(statement));
                }
                return Ok((scope, i + 1));
            }
            TokenPayload::Ident(ident) => {
                if expect_function_as_variable {
                    stack.symbol.push(Symbol::Raw(token.clone()));
                } else {
                    if stack.is_completable() {
                        let statement = create_statement(context, &mut stack)?;
                        scope.statements.push(ast::Statement::InScope(statement));
                    }
                    match context.declarations.get(ident) {
                        None => {
                            if !stack.is_empty() {
                                // Expecting a type?
                                let expect_type = stack
                                    .last_symbol_is(&TokenPayload::TypeDeclaration)
                                    || stack.last_operator_is(&TokenPayload::Cast);
                                let msg = if expect_type { "Type" } else { "Symbol" };
                                let available = context
                                    .declarations
                                    .keys()
                                    .cloned()
                                    .collect::<Vec<_>>()
                                    .join(", ");

                                return Err(CompilerError::from_token::<Token>(
                                    token,
                                    format!(
                                        "[P2] {} \"{}\" was not defined. Stack.symbol: {:?}.\n\tAvailable are: {}",
                                        msg, ident, stack.symbol, available
                                    ),
                                ));
                            } else {
                                // New declaration?
                                stack.symbol.push(Symbol::Raw(token.clone()));
                            }
                        }
                        Some(declaration) => {
                            if declaration.req_args_count() == 0 {
                                stack.symbol.push(Symbol::Raw(token.clone()));
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
                    stack.symbol.push(Symbol::Raw(token.clone()));
                    scope.statements.push(ast::Statement::InScope(statement));
                } else {
                    stack.symbol.push(Symbol::Raw(token.clone()));
                }
            }
            TokenPayload::DefineLocal => {
                if stack.symbol.is_empty() {
                    return Err(CompilerError {
                        location: token.loc.clone(),
                        msg: "[P5] No identifier for new definition found!".to_string(),
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
            TokenPayload::DefinePublic => {}
            TokenPayload::TypeDeclaration => {
                stack.symbol.push(Symbol::Raw(token.clone()));
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
            }
        }
    }
    if stack.infix.is_empty() && stack.symbol.is_empty() {
        return Ok((scope, i));
    } else if stack.is_completable() {
        let statement = create_statement(context, &mut stack)?;
        scope.statements.push(ast::Statement::InScope(statement));
        return Ok((scope, i));
    } else {
        Err(CompilerError::global(&format!(
            "[P7] Parser could not process all tokens. Remaining are",
        )))
    }
}

pub fn parse(
    context: &mut Context,
    tokens: &[Token],
) -> Result<ast::Scope<SparseToken>, CompilerError> {
    match env::var("DEBUG_SHOW_IR") {
        Ok(_) => parse_impl(ParserState::new(), context, &tokens)
            .map_err(|e| CompilerError {
                location: e.location,
                msg: format!(
                    "{}\n Input: {}",
                    e.msg,
                    tokens
                        .iter()
                        .map(|t| format!("{:?}", t.token))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
            })
            .map(|(s, _)| s),
        Err(_) => parse_impl(ParserState::new(), context, &tokens).map(|(s, _)| s),
    }
}

#[cfg(test)]
mod specs {
    use crate::ast::Statement;

    use super::*;
    use ast::{IntegerStub, LexerTokenPayloadStub, Node, Scope, StringStub};
    use TokenPayload::*;
    type SparseNode = Node<SparseToken>;

    #[test]
    fn stack_is_completed_milestone_5_mvp() {
        use Precedence::*;
        use Symbol::Raw;
        use TokenPayload::*;
        let stack = ParseStack {
            symbol: vec![
                Raw(Token::stub(Ident("a".to_owned()))),
                Raw(Token::stub(TypeDeclaration)),
                Raw(Token::stub(Ident("i16".to_owned()))),
                Raw(Token::stub(Integer(3))),
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
                Raw(Token::stub(Ident("a".to_owned()))),
                Raw(Token::stub(TypeDeclaration)),
                Raw(Token::stub(Ident("i32".to_owned()))),
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
                Raw(Token::stub(Ident("a".to_owned()))),
                Raw(Token::stub(TypeDeclaration)),
                Raw(Token::stub(Ident("i32".to_owned()))),
                Raw(Token::stub(Integer(3))),
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
                Raw(Token::stub(Ident("b".to_owned()))),
                Raw(Token::stub(TypeDeclaration)),
                Raw(Token::stub(Ident("i8".to_owned()))),
                Finished(Node {
                    root: LexerTokenPayloadStub::stub(Cast),
                    args: vec![
                        Node::leaf(StringStub::stub("a")),
                        Node::leaf(StringStub::stub("i8")),
                    ],
                }),
                Raw(Token::stub(Integer(5))),
                Raw(Token::stub(Ident("i8".to_owned()))),
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

    #[test]
    fn milestone_1() {
        let tokens = vec![Integer(42), Pipe, Ident("stdout".to_string())];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };
        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();
        assert!(actual.statements.len() == 1);

        let expected = ast::Node {
            root: LexerTokenPayloadStub::stub(Pipe),
            args: vec![
                ast::Node::leaf(IntegerStub::stub(42)),
                ast::Node::leaf(StringStub::stub("stdout")),
            ],
        };

        assert_eq!(actual.statements[0], Statement::InScope(expected));
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

        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();
        assert!(actual.statements.len() == 1);

        let expected = ast::Node {
            root: StringStub::stub("stdout"),
            args: vec![ast::Node {
                root: IntegerStub::stub(42),
                args: vec![],
            }],
        };

        assert_eq!(actual.statements[0], Statement::InScope(expected));
    }

    #[test]
    fn function_without_braces() {
        let tokens = vec![Ident("stdout".to_string()), Integer(42)];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };
        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();
        assert!(actual.statements.len() == 1);

        let expected = ast::Node {
            root: StringStub::stub("stdout"),
            args: vec![ast::Node {
                root: IntegerStub::stub(42),
                args: vec![],
            }],
        };

        assert_eq!(actual.statements[0], Statement::InScope(expected));
    }

    #[test]
    fn milestone_3_print_sum() {
        let tokens = vec![Ident("stdout".to_string()), Integer(3), Add, Integer(5)];

        let mut context = Context {
            declarations: hashmap! {
                "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32], true)
            },
        };

        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();
        assert!(actual.statements.len() == 1);

        let expected = SparseNode {
            root: StringStub::stub("stdout"),
            args: vec![Node {
                root: LexerTokenPayloadStub::stub(Add),
                args: vec![
                    Node::leaf(IntegerStub::stub(3)),
                    Node::leaf(IntegerStub::stub(5)),
                ],
            }],
        };

        assert_eq!(actual.statements[0], Statement::InScope(expected));
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

        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();
        assert!(actual.statements.len() == 1);

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

        assert_eq!(actual.statements[0], Statement::InScope(expected));
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

        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();
        assert!(actual.statements.len() == 1);

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

        assert_eq!(actual.statements[0], Statement::InScope(expected));
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

        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();
        assert!(actual.statements.len() == 1);

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

        assert_eq!(actual.statements[0], Statement::InScope(expected));
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

        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();
        assert!(actual.statements.len() == 1);

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

        assert_eq!(actual.statements[0], Statement::InScope(expected));
    }

    #[test]
    fn milestone_3_hard() {
        // stdout min 0 , max -3,-4
        let tokens = vec![
            Ident("stdout".to_owned()),
            Ident("min".to_owned()),
            Integer(0),
            Delimiter,
            Ident("max".to_owned()),
            Integer(-3),
            Delimiter,
            Integer(-4),
        ];

        let mut context = Context::default();

        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();
        assert!(actual.statements.len() == 1);

        let expected: Node<SparseToken> = Node {
            root: StringStub::stub("stdout"),
            args: vec![Node {
                root: StringStub::stub("min"),
                args: vec![
                    Node::leaf(IntegerStub::stub(0)),
                    Node {
                        root: StringStub::stub("max"),
                        args: vec![
                            Node::leaf(IntegerStub::stub(-3)),
                            Node::leaf(IntegerStub::stub(-4)),
                        ],
                    },
                ],
            }],
        };

        assert_eq!(actual.statements[0], Statement::InScope(expected));
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

        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();
        assert!(actual.statements.len() == 1);

        let expected = SparseNode {
            root: LexerTokenPayloadStub::stub(DefineLocal),
            args: vec![
                Node::leaf(StringStub::stub("a")),
                Node::leaf(IntegerStub::stub(3)),
            ],
        };
        assert_eq!(actual.statements[0], Statement::InScope(expected));
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
        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();
        assert!(actual.statements.len() == 1);

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
        assert_eq!(actual.statements[0], Statement::InScope(expected));
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

        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();

        let expected = vec![
            Statement::InScope(Node {
                root: LexerTokenPayloadStub::stub(DefineLocal),
                args: vec![
                    Node::leaf(StringStub::stub("a")),
                    Node::leaf(IntegerStub::stub(3)),
                ],
            }),
            Statement::InScope(Node {
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
            }),
            Statement::InScope(Node {
                root: LexerTokenPayloadStub::stub(DefineLocal),
                args: vec![
                    Node::leaf(StringStub::stub("c")),
                    Node::leaf(IntegerStub::stub(7)),
                ],
            }),
            Statement::InScope(Node {
                root: StringStub::stub("stdout"),
                args: vec![Node {
                    root: StringStub::stub("max"),
                    args: vec![
                        Node::leaf(StringStub::stub("b")),
                        Node::leaf(StringStub::stub("c")),
                    ],
                }],
            }),
        ];

        assert_eq!(actual.statements, expected);

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
                "i16".to_string() => Declaration::variable(Type::Type),
            },
        };

        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();

        let expected = [
            Statement::InScope(Node {
                root: LexerTokenPayloadStub::stub(DefineLocal),
                args: vec![
                    Node::leaf(StringStub::stub("a")),
                    Node::leaf(StringStub::stub("i16")),
                    Node::leaf(IntegerStub::stub(3)),
                ],
            }),
            Statement::InScope(Node {
                root: StringStub::stub("stdout"),
                args: vec![Node::leaf(StringStub::stub("a"))],
            }),
        ];

        assert_eq!(&actual.statements, &expected);

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
                "i8".to_string() => Declaration::variable(Type::Type),
                "i32".to_string() => Declaration::variable(Type::Type),
            },
        };

        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();

        let expected: Vec<_> = vec![
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
        ]
        .into_iter()
        .map(Statement::InScope)
        .collect();

        assert_eq!(&actual.statements, &expected);
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
            declarations: hashmap! {
                "i8".to_string() => Declaration::variable(Type::Type),
            },
        };

        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();

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

        assert_eq!(actual.statements[0], Statement::InScope(expected));
    }

    #[test]
    fn create_statement_milestone_5_explicit() {
        use Precedence::*;
        use Symbol::{Finished, Raw};
        use TokenPayload::*;
        let mut stack = ParseStack {
            symbol: vec![
                Raw(Token::stub(Ident("b".to_owned()))),
                Raw(Token::stub(TypeDeclaration)),
                Raw(Token::stub(Ident("i8".to_owned()))),
                Finished(Node {
                    root: LexerTokenPayloadStub::stub(Cast),
                    args: vec![
                        Node::leaf(StringStub::stub("a")),
                        Node::leaf(StringStub::stub("i8")),
                    ],
                }),
                Raw(Token::stub(Integer(5))),
                Raw(Token::stub(Ident("i8".to_owned()))),
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

    #[test]
    fn is_completable_5_hard() {
        // stdout (
        use Precedence::*;
        use Symbol::Raw;
        use TokenPayload::*;
        let stack = ParseStack {
            symbol: vec![Raw(Token::stub(Ident("stdout".to_owned())))],
            infix: vec![Infix {
                token: Token::stub(ParenthesesL),
                precedence: POpening,
                req_args_count: 0,
                optional_type: false,
                is_statement: false,
            }],
        };
        assert!(!stack.is_completable());
    }

    #[test]
    fn parse_milestone_5_hard() {
        // stdout (max (max 1,2),3) + 1
        let tokens = [
            Ident("stdout".to_owned()),
            ParenthesesL,
            Ident("max".to_owned()),
            ParenthesesL,
            Ident("max".to_owned()),
            Integer(1),
            Delimiter,
            Integer(2),
            ParenthesesR,
            Delimiter,
            Integer(3),
            ParenthesesR,
            Add,
            Integer(1),
        ];

        let mut context = Context::default();

        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();
        assert!(actual.statements.len() == 1);

        let expected: Node<SparseToken> = Node {
            root: StringStub::stub("stdout"),
            args: vec![Node {
                root: LexerTokenPayloadStub::stub(Add),
                args: vec![
                    Node {
                        root: StringStub::stub("max"),
                        args: vec![
                            Node {
                                root: StringStub::stub("max"),
                                args: vec![
                                    Node::leaf(IntegerStub::stub(1)),
                                    Node::leaf(IntegerStub::stub(2)),
                                ],
                            },
                            Node::leaf(IntegerStub::stub(3)),
                        ],
                    },
                    Node::leaf(IntegerStub::stub(1)),
                ],
            }],
        };

        assert_eq!(actual.statements[0], Statement::InScope(expected));
    }

    #[test]
    fn milestone_6_scope() {
        // a := 12
        // {
        //     b := a * 3
        //     stdout a + b
        // }
        let tokens = vec![
            Ident("a".to_owned()),
            DefineLocal,
            Integer(12),
            BraceL,
            Ident("b".to_owned()),
            DefineLocal,
            Ident("a".to_owned()),
            Multiply,
            Integer(3),
            Ident("stdout".to_owned()),
            Ident("a".to_owned()),
            Add,
            Ident("b".to_owned()),
            BraceR,
        ];

        let mut context = Context::default();

        let actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
        assert_ok!(actual);
        let (actual, _) = actual.unwrap();

        let expected: ast::Scope<SparseToken> = Scope {
            statements: vec![
                Statement::InScope(Node {
                    root: LexerTokenPayloadStub::stub(DefineLocal),
                    args: vec![
                        Node::leaf(StringStub::stub("a")),
                        Node::leaf(IntegerStub::stub(12)),
                    ],
                }),
                Statement::Nested(Scope {
                    statements: vec![
                        Statement::InScope(Node {
                            root: LexerTokenPayloadStub::stub(DefineLocal),
                            args: vec![
                                Node::leaf(StringStub::stub("b")),
                                Node {
                                    root: LexerTokenPayloadStub::stub(Multiply),
                                    args: vec![
                                        Node::leaf(StringStub::stub("a")),
                                        Node::leaf(IntegerStub::stub(3)),
                                    ],
                                },
                            ],
                        }),
                        Statement::InScope(Node {
                            root: StringStub::stub("stdout"),
                            args: vec![Node {
                                root: LexerTokenPayloadStub::stub(Add),
                                args: vec![
                                    Node::leaf(StringStub::stub("a")),
                                    Node::leaf(StringStub::stub("b")),
                                ],
                            }],
                        }),
                    ],
                }),
            ],
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_6() {
        // obj := {
        //    a :+ 12
        //    b :+ a * 3
        //}
        //stdout obj.a + obj.b

        let tokens = vec![
            Ident("obj".to_owned()),
            DefineLocal,
            BraceL,
            Ident("a".to_owned()),
            TypeDeclaration,
            Add,
            Integer(12),
            Ident("b".to_owned()),
            TypeDeclaration,
            Add,
            Ident("a".to_owned()),
            Multiply,
            Integer(3),
            BraceR,
            Ident("stdout".to_owned()),
            Ident("obj".to_owned()),
            Dot,
            Ident("a".to_owned()),
            Add,
            Ident("obj".to_owned()),
            Dot,
            Ident("b".to_owned()),
        ];

        let mut context = Context::default();

        let _actual = parse_impl(ParserState::new(), &mut context, &create_stub(&tokens));
    }
}
