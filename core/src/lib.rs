use std::collections::HashMap;
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
    Int32,
    Void,
}

#[derive(PartialEq, Debug)]
pub struct Declaration {
    // Later will be vector
    // pre: Vec<Type>,
    post: Vec<Type>,
    return_type: Type,
    is_statement: bool,
}

impl Declaration {
    pub fn function(return_type: Type, args: Vec<Type>, is_statement: bool) -> Declaration {
        Declaration {
            return_type,
            // pre: Vec::new(),
            post: args,
            is_statement,
        }
    }
    pub fn variable(return_type: Type) -> Declaration {
        Declaration {
            return_type,
            // pre: Vec::new(),
            post: vec![],
            is_statement: false,
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
                msg: format!("Function {} was not defined.", ident),
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
            "stdout".to_string() => Declaration::function(Type::Void, vec![Type::Int32], true),
            "max".to_string() => Declaration::function(Type::Int32, vec![Type::Int32,Type::Int32], false),
            "min".to_string() => Declaration::function(Type::Int32, vec![Type::Int32,Type::Int32], false)
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

    #[test]
    fn milestone_1() {
        let actual = compile(
            &"#!/usr/bin/env ichop

            42 | stdout",
        );
        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = vec![PushInt32(42), StdOut];

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
        let expected = vec![PushInt32(3), PushInt32(5), Max, StdOut];

        assert_eq!(actual, expected);
    }
}
