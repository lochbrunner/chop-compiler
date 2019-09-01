#[cfg(test)]
use std::cmp::PartialEq;
use std::collections::HashMap;
use std::fmt;
pub mod ast;
mod exporter;
mod generator;
mod lexer;
mod parser;
mod simplifier;
pub mod token;
pub use exporter::{bytecode, llvm};

use crate::exporter::bytecode::ByteCode;

#[macro_use]
extern crate maplit;

#[derive(PartialEq, Debug, Clone)]
pub enum Type {
    Int8,
    Int16,
    Int32,
    Int64,
    Void,
}

impl Type {
    pub fn from_token(token: &token::Token) -> Type {
        match token.token {
            token::TokenPayload::Ident(ref ident) => match ident as &str {
                "i8" => Type::Int8,
                "i16" => Type::Int16,
                "i32" => Type::Int32,
                "i64" => Type::Int64,
                _ => Type::Int32,
            },
            _ => Type::Int32,
        }
    }
}

pub struct Signature<T> {
    return_type: T,
    args: Vec<T>,
}
impl<T> fmt::Debug for Signature<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}({:?})", self.return_type, self.args)
    }
}

pub struct Declaration {
    // Later will be vector
    // pre: Vec<Type>,
    #[deprecated(note = "Use signature instead")]
    post: Vec<Type>,
    #[deprecated(note = "Use signature instead")]
    return_type: Type,
    // signature: Signature<Option<Type>>,
    deduce_complete:
        fn(&Declaration, partial: Signature<Option<Type>>) -> Result<Signature<Type>, String>,
    #[deprecated(note = "This is equal with return type being Void")]
    is_statement: bool,
}

impl fmt::Debug for Declaration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}({:?})", self.return_type, self.post)
    }
}

#[cfg(test)]
impl PartialEq for Declaration {
    fn eq(&self, other: &Self) -> bool {
        self.is_statement == other.is_statement
            && self.post == other.post
            && self.return_type == other.return_type
    }
}

impl Declaration {
    fn check(partial: &Option<Type>, full: &Type) -> Result<(), String> {
        if let Some(return_type) = partial {
            if return_type != full {
                return Err(format!(
                    "Type {:?} and {:?} do not match",
                    return_type, full
                ));
            }
        }
        Ok(())
    }

    /// Ignores all types are the same
    /// TODO: Check for number of arguments
    pub fn full_template_statement(num_args: usize) -> Declaration {
        Declaration {
            return_type: Type::Int32,
            post: vec![Type::Int32; num_args],
            is_statement: true,
            deduce_complete: |_, partial| {
                fn get_type(args: &[Option<Type>]) -> Option<Type> {
                    for arg in args.iter() {
                        if let Some(t) = arg {
                            return Some(t.clone());
                        }
                    }
                    None
                }
                // Get at least one type
                let tp = if let Some(tp) = get_type(&partial.args) {
                    tp
                } else {
                    return Err(format!("No types found in {:?}", partial));
                };
                let args_count = partial.args.len();
                Ok(Signature {
                    return_type: Type::Void,
                    args: vec![tp.clone(); args_count],
                })
            },
        }
    }
    /// Ignores all types are the same
    /// TODO: Check for number of arguments
    pub fn full_template_function(num_args: usize) -> Declaration {
        Declaration {
            return_type: Type::Int32,
            post: vec![Type::Int32; num_args],
            is_statement: false,
            deduce_complete: |_, partial| {
                fn get_type(args: &[Option<Type>]) -> Option<Type> {
                    for arg in args.iter() {
                        if let Some(t) = arg {
                            return Some(t.clone());
                        }
                    }
                    None
                }
                // Get at least one type
                let tp = if let Some(tp) = partial.return_type {
                    tp
                } else {
                    if let Some(tp) = get_type(&partial.args) {
                        tp
                    } else {
                        return Err(format!("No types found in {:?}", partial));
                    }
                };
                let args_count = partial.args.len();
                Ok(Signature {
                    return_type: tp.clone(),
                    args: vec![tp.clone(); args_count],
                })
            },
        }
    }
    /// Use this if all types are constant.
    pub fn function(return_type: Type, args: Vec<Type>, is_statement: bool) -> Declaration {
        Declaration {
            return_type,
            // pre: Vec::new(),
            post: args,
            is_statement,
            deduce_complete: |decl, partial| {
                Declaration::check(&partial.return_type, &decl.return_type)?;
                if partial.args.len() != decl.post.len() {
                    return Err(format!(
                        "Expected {} arguments but got {}",
                        decl.post.len(),
                        partial.args.len()
                    ));
                }
                // Check arg types
                for (decl_arg, partial_arg) in decl.post.iter().zip(partial.args.iter()) {
                    Declaration::check(partial_arg, decl_arg)?;
                }
                Ok(Signature {
                    return_type: decl.return_type.clone(),
                    args: decl.post.clone(),
                })
            },
        }
    }
    /// Use this if all types are constant.
    pub fn variable(return_type: Type) -> Declaration {
        Declaration {
            return_type,
            // pre: Vec::new(),
            post: vec![],
            is_statement: false,
            deduce_complete: |decl, partial| {
                Declaration::check(&partial.return_type, &decl.return_type)?;
                Ok(Signature {
                    return_type: decl.return_type.clone(),
                    args: vec![],
                })
            },
        }
    }
}

#[derive(Debug)]
pub struct Context {
    pub declarations: HashMap<String, Declaration>,
}

impl Context {
    pub fn get_declaration(
        &self,
        ident: &str,
        location: token::Location,
    ) -> Result<&Declaration, CompilerError> {
        match self.declarations.get(ident) {
            None => Err(CompilerError {
                location,
                msg: format!("Symbol {} was not defined.", ident),
            }),
            Some(dec) => Ok(dec),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct CompilerError {
    pub location: token::Location,
    msg: String,
}

impl CompilerError {
    pub fn print(&self, filename: &str) {
        eprintln!(
            "{}:{}:{}",
            filename, self.location.line, self.location.offset
        );
        eprintln!("{}", self.msg);
    }

    pub fn global(msg: &str) -> CompilerError {
        CompilerError {
            location: token::Location { offset: 0, line: 0 },
            msg: msg.to_string(),
        }
    }

    pub fn from_token(token: &token::Token, msg: String) -> CompilerError {
        CompilerError {
            location: token.begin.clone(),
            msg,
        }
    }
}

pub fn compile(code: &str) -> Result<Vec<ByteCode>, CompilerError> {
    // Milestone 1 context
    let mut context = Context {
        declarations: hashmap! {
            "stdout".to_string() => Declaration::full_template_statement(1),
            "max".to_string() => Declaration::full_template_function(2),
            "min".to_string() => Declaration::full_template_function(2),
        },
    };

    let tokens = lexer::lex(code)?;
    let raw_ast = parser::parse(&mut context, &tokens)?;
    let ast = generator::generate(raw_ast)?;
    let simple = simplifier::simplify(ast)?;
    exporter::bytecode::export(&context, simple)
}

#[cfg(test)]
mod e2e {
    use super::*;
    use ByteCode::*;

    static HEADER: [ByteCode; 3] = [Alloca(Type::Int32), PushInt32(0), Store(Type::Int32, 0)];

    #[test]
    fn milestone_1() {
        let actual = compile(
            &"#!/usr/bin/env ichop

            42 | stdout",
        );
        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let expected = vec![PushInt32(42), StdOut];
        let expected = [&HEADER[..], &expected].concat();

        assert_eq!(actual, expected);
    }

    #[test]
    fn multiple_statements() {
        let actual = compile(
            &"#!/usr/bin/env ichop

            42 | stdout
            35 | stdout",
        );

        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = vec![PushInt32(42), StdOut, PushInt32(35), StdOut];
        let expected = [&HEADER[..], &expected].concat();

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_1_advanced() {
        let actual = compile(
            &"#!/usr/bin/env ichop
        42 | stdout
        stdout(35)
        stdout 28",
        );

        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = vec![
            PushInt32(42),
            StdOut,
            PushInt32(35),
            StdOut,
            PushInt32(28),
            StdOut,
        ];
        let expected = [&HEADER[..], &expected].concat();

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_3_function() {
        let actual = compile(
            &"#!/usr/bin/env ichop

            stdout max(3,5)",
        );

        assert!(actual.is_ok());
        let actual = actual.unwrap();
        let expected = vec![
            PushInt32(3),
            PushInt32(5),
            Call2("max".to_string(), Type::Int32, Type::Int32, Type::Int32),
            StdOut,
        ];
        let expected = [&HEADER[..], &expected].concat();

        assert_eq!(actual, expected);
    }
}
