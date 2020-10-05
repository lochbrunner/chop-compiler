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
use declaration::{Context, Declaration, Type};
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
            "i8".to_string() => Declaration::variable(Type::Type),
            "i16".to_string() => Declaration::variable(Type::Type),
            "i32".to_string() => Declaration::variable(Type::Type),
            "i64".to_string() => Declaration::variable(Type::Type),
        },
    };

    let tokens = lexer::lex(code)?;
    let ast = parser::parse(&mut context, &tokens)?;
    let ast = generator::generate_sparse(ast)?;
    let ast = specializer::specialize(ast, &mut context)?;
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
            Call2("max".to_owned(), Type::Int32, Type::Int32, Type::Int32),
            StdOut,
        ];
        let expected = [&HEADER[..], &expected].concat();

        assert_eq!(actual, expected);
    }

    #[test]
    fn print_addition_of_variables() {
        let code = &"#!/usr/bin/env ichop

            a := 3
            b := 5
            stdout a+b";

        let actual = build(code);

        assert!(actual.is_ok());
        let actual = actual.unwrap();

        let expected = vec![
            // head
            Alloca(Type::Int32),
            PushInt32(0),
            Store(Type::Int32, 0),
            // a := 3
            PushInt32(3),
            Alloca(Type::Int32),
            Store(Type::Int32, 1),
            // b := 5
            PushInt32(5),
            Alloca(Type::Int32),
            Store(Type::Int32, 2),
            // stdout a+b"
            Load(Type::Int32, 1),
            Load(Type::Int32, 2),
            Add(Type::Int32),
            StdOut,
        ];
    }

    // #[test]
    // fn milestone_5_main() {
    //     let code = "#!/usr/bin/env ichop

    //         a: i32 := 3
    //         b:= a as i8 + 5
    //         c: i8 := 7
    //         stdout max(b,c)";

    //     let mut context = Context {
    //         declarations: hashmap! {
    //             "stdout".to_string() => Declaration::full_template_statement(1),
    //             "max".to_string() => Declaration::full_template_function(2),
    //             "min".to_string() => Declaration::full_template_function(2),
    //             "i8".to_string() => Declaration::variable(Type::Type),
    //             "i32".to_string() => Declaration::variable(Type::Type),
    //         },
    //     };
    //     let tokens = lexer::lex(code).unwrap();

    //     parser::parse(&mut context, &tokens).unwrap().statements.iter()
    //     .map()
    //     .collect();

    //     let ast = parser::parse(&mut context, &tokens).unwrap();
    //     let ast = generator::generate_sparse(ast).unwrap();
    //     // dbg!(&ast);
    //     let ast = specializer::specialize(ast, &mut context).unwrap();
    //     let ast = simplifier::simplify(ast).unwrap();
    //     let actual = bytecode::compile(&context, ast);

    //     // dbg!(&actual);
    //     assert!(actual.is_ok());
    //     let actual = actual.unwrap();

    //     let expected = vec![
    //         // a: i32 := 3
    //         Alloca(Type::Int32),
    //         PushInt32(0),
    //         Store(Type::Int32, 0),
    //         Alloca(Type::Int32),
    //         Store(Type::Int32, 1),
    //         Alloca(Type::Int8),
    //         Store(Type::Int8, 2),
    //         Alloca(Type::Int8),
    //         Store(Type::Int8, 3),
    //         // stdout max(b,c)
    //         Load(Type::Int8, 2),
    //         Load(Type::Int8, 3),
    //         Call2("max".to_owned(), Type::Int8, Type::Int8, Type::Int8),
    //         StdOut,
    //     ];
    // }
}
