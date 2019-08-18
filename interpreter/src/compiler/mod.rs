use crate::evaluation::bytecode::ByteCode;
use std::collections::HashMap;
pub mod ast;
mod exporter;
mod generator;
mod lexer;
mod parser;
pub mod token;

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
    pub fn print(&self) {
        println!(
            "<unknown file>:{}:{}",
            self.location.line, self.location.offset
        );
        println!("{}", self.msg);
    }
}

pub fn compile(code: &str) -> Result<Vec<ByteCode>, CompilerError> {
    // Milestone 1 context
    let context = Context {
        declarations: hashmap! {
            "stdout".to_owned() => Declaration::function(Type::Void, vec![Type::Int32])
        },
    };

    let tokens = lexer::lex(code)?;
    let raw_ast = parser::parse(&context, &tokens)?;
    let ast = generator::generate(raw_ast)?;
    exporter::export(ast)
}

#[cfg(test)]
mod specs {
    use super::*;
    #[test]
    fn milestone_1() {
        let actual = compile(
            &"#!/usr/bin/env ichop

            42 | stdout",
        );
        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = vec![ByteCode::PushInt32(42), ByteCode::StdOut];

        assert_eq!(actual, expected);
    }
}
