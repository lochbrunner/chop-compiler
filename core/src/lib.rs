// #[cfg(test)]
// use std::cmp::PartialEq;
pub mod ast;
pub mod bytecode;
pub mod declaration;
mod error;
mod generator;
mod lexer;
mod parser;
mod simplifier;
mod specializer;
pub mod token;
use declaration::{Context, Declaration};
pub use error::CompilerError;

pub use bytecode::ByteCode;

#[macro_use]
extern crate maplit;

pub fn build(code: &str) -> Result<Vec<ByteCode>, CompilerError> {
    // Milestone 5 context
    let mut context = Context {
        declarations: hashmap! {
            "stdout".to_string() => Declaration::full_template_statement(1),
            "max".to_string() => Declaration::full_template_function(2),
            "min".to_string() => Declaration::full_template_function(2),
        },
    };

    let tokens = lexer::lex(code)?;
    let ast = parser::parse(&mut context, &tokens)?;
    let ast = generator::generate_sparse(ast)?;
    let ast = specializer::specialize(ast)?;
    let ast = simplifier::simplify(ast)?;
    // TODO: cache
    bytecode::compile(&context, ast)
}

#[cfg(test)]
mod e2e {
    use super::*;
    use declaration::Type;
    use ByteCode::*;

    static HEADER: [ByteCode; 3] = [Alloca(Type::Int32), PushInt32(0), Store(Type::Int32, 0)];

    #[test]
    fn milestone_1() {
        let actual = build(
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
        let actual = build(
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
        let actual = build(
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
        let actual = build(
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
