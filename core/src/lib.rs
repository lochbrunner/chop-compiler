use std::collections::HashMap;
pub mod ast;
mod exporter;
mod generator;
mod lexer;
mod parser;
pub mod token;
pub use exporter::{bytecode, llvm};

use crate::exporter::bytecode::ByteCode;

#[macro_use]
extern crate maplit;

pub enum Type {
    Int32,
    Void,
}

pub struct Declaration {
    // Later will be vector
// pre: Vec<Type>,
// post: Vec<Type>,
// return_type: Type,
}

impl Declaration {
    pub fn function(_return_type: Type, _args: Vec<Type>) -> Declaration {
        Declaration {
            // return_type,
            // pre: Vec::new(),
            // post: args,
        }
    }
}

pub struct Context {
    pub declarations: HashMap<String, Declaration>,
}

#[derive(Debug, PartialEq)]
pub struct CompilerError {
    location: token::Location,
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
}

pub fn compile(code: &str, filename: &str) -> Result<Vec<ByteCode>, CompilerError> {
    // Milestone 1 context
    let context = Context {
        declarations: hashmap! {
            "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32])
        },
    };

    let tokens = lexer::lex(code, filename)?;
    let raw_ast = parser::parse(&context, &tokens)?;
    let ast = generator::generate(raw_ast)?;
    exporter::bytecode::export(ast)
}

#[cfg(test)]
mod specs {
    use super::*;

    #[test]
    fn milestone_1() {
        let actual = compile(
            &"#!/usr/bin/env ichop

            42 | stdout",
            &"test.ch",
        );
        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = vec![ByteCode::PushInt32(42), ByteCode::StdOut];

        assert_eq!(actual, expected);
    }

    #[test]
    fn multiple_statements() {
        let actual = compile(
            &"#!/usr/bin/env ichop

            42 | stdout
            35 | stdout",
            &"test.ch",
        );

        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = vec![
            ByteCode::PushInt32(42),
            ByteCode::StdOut,
            ByteCode::PushInt32(35),
            ByteCode::StdOut,
        ];

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_1_advanced() {
        let actual = compile(
            &"#!/usr/bin/env ichop
        42 | stdout
        stdout(35)
        stdout 28",
            &"test.ch",
        );

        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = vec![
            ByteCode::PushInt32(42),
            ByteCode::StdOut,
            ByteCode::PushInt32(35),
            ByteCode::StdOut,
            ByteCode::PushInt32(28),
            ByteCode::StdOut,
        ];

        assert_eq!(actual, expected);
    }
}
