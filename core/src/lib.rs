#[cfg(test)]
pub mod macros;
//
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
pub use ast::DenseAst;
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
    let mut state = parser::ParserState::new();
    let mut ast = DenseAst::new();
    while let Some((statement, new_state)) = parser::parse(state, &mut context, &tokens)? {
        state = new_state;
        let statement = generator::generate_sparse(statement)?;
        let statement = specializer::specialize(statement, &mut context)?;
        ast.statements.push(statement);
    }
    let ast = simplifier::simplify(ast)?;
    // TODO: cache
    bytecode::compile(&context, ast)
}

#[cfg(test)]
mod e2e {
    use super::*;
    use crate::ast::DenseAst;
    use declaration::Type;
    use ByteCode::*;

    static HEADER: [ByteCode; 3] = [Alloca(Type::Int32), PushInt32(0), Store(Type::Int32, 0)];

    #[test]
    fn milestone_1() {
        let actual = build(
            &"#!/usr/bin/env ichop

            42 | stdout",
        );
        assert_ok!(actual);
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

        assert_ok!(actual);
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

        assert_ok!(actual);
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
        assert_ok!(actual);
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

        assert_ok!(actual);
        let actual = actual.unwrap();

        let expected = [
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

        assert_eq!(actual, expected);
    }

    #[test]
    fn milestone_5_main() {
        use self::Type::*;
        let code = "#!/usr/bin/env ichop

            a: i32 := 3
            b:= a as i8 + 5
            c: i8 := 7
            stdout max(b,c)";

        let mut context = Context {
            declarations: hashmap! {
                // "stdout".to_string() => Declaration::full_template_statement(1),
                "stdout".to_string() => Declaration::function(Void, vec![Int8], true),
                "max".to_string() => Declaration::full_template_function(2),
                "min".to_string() => Declaration::full_template_function(2),
                "i8".to_string() => Declaration::variable(Type),
                "i32".to_string() => Declaration::variable(Type),
            },
        };
        let tokens = lexer::lex(code).unwrap();
        let mut state = parser::ParserState::new();
        let mut ast = DenseAst::new();
        while let Some((statement, new_state)) =
            parser::parse(state, &mut context, &tokens).unwrap()
        {
            state = new_state;
            let statement = generator::generate_sparse(statement).unwrap();
            let statement = specializer::specialize(statement, &mut context).unwrap();
            ast.statements.push(statement);
        }
        let ast = simplifier::simplify(ast).unwrap();
        let actual = bytecode::compile(&context, ast);

        assert_ok!(actual);
        let actual = actual.unwrap();

        let expected = [
            Alloca(Int32),
            PushInt32(0),
            Store(Int32, 0),
            // a: i32 := 3
            PushInt32(3),
            Alloca(Int32),
            Store(Int32, 1),
            // b:= a as i8 + 5
            Load(Int32, 1),
            CastInt(Int32, Int8),
            PushInt8(5),
            Add(Int8),
            Alloca(Int8),
            Store(Int8, 2),
            // c: i8 := 7
            PushInt8(7),
            Alloca(Int8),
            Store(Int8, 3),
            // stdout max(b,c)
            Load(Int8, 2),
            Load(Int8, 3),
            Call2("max".to_owned(), Int8, Int8, Int8),
            StdOut,
        ];

        assert_eq!(actual, expected);
    }
}
