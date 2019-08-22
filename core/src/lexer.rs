use crate::token::{Location, Token, TokenPayload};
use crate::CompilerError;
use nom::{
  branch::alt,
  bytes::complete::{tag, take_until, take_while},
  combinator::{complete, map, opt},
  error::{ErrorKind, ParseError},
  multi::{many0, many1},
  sequence::{preceded, terminated},
  IResult,
};
use nom_locate::{position, LocatedSpanEx};

// See: https://github.com/fflorent/nom_locate/issues/20

#[derive(Clone, PartialEq, Debug)]
struct LexState {
  pub accept_literal: bool,
}

impl LexState {
  pub fn new() -> LexState {
    LexState {
      accept_literal: false,
    }
  }
}

type Span<'a> = LocatedSpanEx<&'a str, LexState>;

fn sp<'a, E: ParseError<Span<'a>>>(i: Span<'a>) -> IResult<Span<'a>, Span<'a>, E> {
  let chars = " \t\r\n";
  take_while(move |c| chars.contains(c))(i)
}

impl Token {
  fn new(begin: Span, end: Span, payload: TokenPayload) -> Token {
    Token {
      begin: Location {
        offset: begin.offset,
        line: begin.line,
      },
      end: Location {
        offset: end.offset,
        line: end.line,
      },
      // filename: begin.extra
      token: payload,
    }
  }
}

fn set_accept_literal(
  value: bool,
  span: IResult<Span, TokenPayload>,
) -> IResult<Span, TokenPayload> {
  match span {
    Ok(mut span) => {
      span.0.extra.accept_literal = value;
      Ok(span)
    }
    _ => span,
  }
}

fn mathematical_operators(code: Span) -> IResult<Span, TokenPayload> {
  set_accept_literal(
    true,
    alt((
      map(tag("*"), |_| TokenPayload::Multiply),
      map(tag("/"), |_| TokenPayload::Divide),
      map(tag("+"), |_| TokenPayload::Add),
      map(tag("-"), |_| TokenPayload::Subtract),
      map(tag("%"), |_| TokenPayload::Remainder),
    ))(code),
  )
}

fn operators(code: Span) -> IResult<Span, TokenPayload> {
  alt((
    map(tag("|"), |_| TokenPayload::Pipe),
    map(tag(":="), |_| TokenPayload::DefineLocal),
  ))(code)
}

fn shebang(code: Span) -> IResult<Span, ()> {
  let (code, _) = tag("#!")(code)?;
  let (code, _) = take_until("\n")(code)?;
  Ok((code, ()))
}

// Literals
fn parse_integer(code: Span) -> IResult<Span, TokenPayload> {
  let chars = "1234567890";
  // Sign ?
  let (code, sign) = opt(tag("-"))(code)?;
  let sign = sign.is_some();
  if sign && !code.extra.accept_literal {
    return Err(nom::Err::Error((code, ErrorKind::IsNot)));
  }
  let (code, slice) = take_while(move |c| chars.contains(c))(code)?;
  match slice.fragment.parse::<i32>() {
    Ok(value) => set_accept_literal(
      false,
      Ok((code, TokenPayload::Int32(if sign { -value } else { value }))),
    ),
    Err(_) => Err(nom::Err::Error((code, ErrorKind::Tag))),
  }
}

fn parse_ident(code: Span) -> IResult<Span, TokenPayload> {
  let chars = "_";
  let (code, ident) =
    take_while(move |c: char| c.is_ascii_alphabetic() || chars.contains(c))(code)?;
  if ident.fragment.is_empty() {
    Err(nom::Err::Error((code, ErrorKind::Tag)))
  } else {
    Ok((code, TokenPayload::Ident(ident.fragment.to_owned())))
  }
}

fn parse_punctuation(code: Span) -> IResult<Span, TokenPayload> {
  set_accept_literal(
    true,
    alt((
      map(tag("("), |_| TokenPayload::ParenthesesL),
      map(tag(")"), |_| TokenPayload::ParenthesesR),
      map(tag(","), |_| TokenPayload::Delimiter),
    ))(code),
  )
}

fn lex_token(code: Span) -> IResult<Span, Token> {
  let (code, begin) = position(code)?;
  let (code, payload) = alt((
    operators,
    parse_integer,
    parse_ident,
    mathematical_operators,
    parse_punctuation,
  ))(code)?;
  let (code, end) = position(code)?;
  Ok((code, Token::new(begin, end, payload)))
}

pub fn lex(code: &str) -> Result<Vec<Token>, CompilerError> {
  let (code, _) = many0(shebang)(Span {
    fragment: code,
    extra: LexState::new(),
    offset: 0,
    line: 1,
  })
  .unwrap();
  let a = complete(many1(preceded(sp, terminated(lex_token, sp))))(code);

  match a {
    Ok((remaining, tokens)) => {
      if remaining.fragment.is_empty() {
        Ok(tokens)
      } else {
        Err(CompilerError {
          msg: format!("Incomplete Error: {:?}", remaining.fragment),
          location: Location {
            line: remaining.line,
            offset: remaining.offset,
          },
        })
      }
    }
    Err(error) => match error {
      nom::Err::Incomplete(_) => Err(CompilerError {
        msg: "Incomplete".to_string(),
        location: Location { line: 0, offset: 0 },
      }),
      nom::Err::Error(error) => Err(CompilerError {
        msg: format!("{:?} Error: {:?}", error.1, error.0.fragment),
        location: Location {
          line: error.0.line,
          offset: error.0.offset,
        },
      }),
      nom::Err::Failure(error) => Err(CompilerError {
        msg: format!("{:?} Failure: {:?}", error.1, error.0.fragment),
        location: Location {
          line: error.0.line,
          offset: error.0.offset,
        },
      }),
    },
  }
}

#[cfg(test)]
mod specs {
  use super::*;

  use TokenPayload::*;

  #[test]
  fn single_op() {
    let actual = lex(&":= ").unwrap();
    let expected = vec![Token {
      token: TokenPayload::DefineLocal,
      begin: Location { line: 1, offset: 0 },
      end: Location { line: 1, offset: 2 },
    }];

    assert_eq!(actual, expected);
  }

  #[test]
  fn multiple_ops_and_ws() {
    let actual = lex(&" := \t |\n :=").unwrap();
    let expected = vec![
      Token {
        token: TokenPayload::DefineLocal,
        begin: Location { line: 1, offset: 1 },
        end: Location { line: 1, offset: 3 },
      },
      Token {
        token: TokenPayload::Pipe,
        begin: Location { line: 1, offset: 6 },
        end: Location { line: 1, offset: 7 },
      },
      Token {
        token: TokenPayload::DefineLocal,
        begin: Location { line: 2, offset: 9 },
        end: Location {
          line: 2,
          offset: 11,
        },
      },
    ];

    assert_eq!(actual, expected);
  }

  #[test]
  fn error_unknown_op() {
    let actual = lex(&"~");
    let expected = Err(CompilerError {
      location: Location { line: 1, offset: 0 },
      msg: "Tag Error: \"~\"".to_owned(),
    });

    assert!(actual.is_err());
    assert_eq!(actual, expected);
  }

  #[test]
  fn error_incomplete_parse() {
    let actual = lex(&"| := ~ |");
    let expected = Err(CompilerError {
      location: Location { line: 1, offset: 5 },
      msg: "Incomplete Error: \"~ |\"".to_owned(),
    });

    assert!(actual.is_err());
    assert_eq!(actual, expected);
  }

  #[test]
  fn milestone_1() {
    let actual = lex(
      &"#!/usr/bin/env ichop

      42 | stdout",
    )
    .unwrap();

    let expected = vec![
      Token {
        token: TokenPayload::Int32(42),
        begin: Location {
          line: 3,
          offset: 28,
        },
        end: Location {
          line: 3,
          offset: 30,
        },
      },
      Token {
        token: TokenPayload::Pipe,
        begin: Location {
          line: 3,
          offset: 31,
        },
        end: Location {
          line: 3,
          offset: 32,
        },
      },
      Token {
        token: TokenPayload::Ident("stdout".to_owned()),
        begin: Location {
          line: 3,
          offset: 33,
        },
        end: Location {
          line: 3,
          offset: 39,
        },
      },
    ];
    assert_eq!(actual, expected);
  }

  #[test]
  fn function_with_braces() {
    let actual = lex("stdout(42)");
    assert!(actual.is_ok());
    let actual = actual.unwrap();

    let expected = vec![
      Token {
        token: TokenPayload::Ident("stdout".to_string()),
        begin: Location { line: 1, offset: 0 },
        end: Location { line: 1, offset: 6 },
      },
      Token {
        token: TokenPayload::ParenthesesL,
        begin: Location { line: 1, offset: 6 },
        end: Location { line: 1, offset: 7 },
      },
      Token {
        token: TokenPayload::Int32(42),
        begin: Location { line: 1, offset: 7 },
        end: Location { line: 1, offset: 9 },
      },
      Token {
        token: TokenPayload::ParenthesesR,
        begin: Location { line: 1, offset: 9 },
        end: Location {
          line: 1,
          offset: 10,
        },
      },
    ];

    assert_eq!(actual, expected);
  }

  #[test]
  fn function_without_braces() {
    let actual = lex("stdout 42");
    assert!(actual.is_ok());
    let actual = actual.unwrap();

    let expected = vec![
      Token {
        token: TokenPayload::Ident("stdout".to_string()),
        begin: Location { line: 1, offset: 0 },
        end: Location { line: 1, offset: 6 },
      },
      Token {
        token: TokenPayload::Int32(42),
        begin: Location { line: 1, offset: 7 },
        end: Location { line: 1, offset: 9 },
      },
    ];
    assert_eq!(actual, expected);
  }

  #[test]
  fn milestone_3_function_multi_args() {
    let actual = lex(
      &"#!/usr/bin/env ichop

        stdout max(3,5)",
    );

    assert!(actual.is_ok());
    let actual = actual.unwrap();
    let actual = actual.into_iter().map(|t| t.token).collect::<Vec<_>>();

    let expected = vec![
      Ident("stdout".to_string()),
      Ident("max".to_string()),
      ParenthesesL,
      Int32(3),
      Delimiter,
      Int32(5),
      ParenthesesR,
    ];

    assert_eq!(actual, expected);
  }

  #[test]
  fn milestone_3() {
    let actual = lex(
      &"#!/usr/bin/env ichop

      stdout max(3+5*-7, 11*13-15)",
    );

    assert!(actual.is_ok());
    let actual = actual.unwrap();

    let expected = vec![
      Token {
        token: Ident("stdout".to_string()),
        begin: Location {
          line: 3,
          offset: 28,
        },
        end: Location {
          line: 3,
          offset: 34,
        },
      },
      Token {
        token: Ident("max".to_string()),
        begin: Location {
          line: 3,
          offset: 35,
        },
        end: Location {
          line: 3,
          offset: 38,
        },
      },
      Token {
        token: ParenthesesL,
        begin: Location {
          line: 3,
          offset: 38,
        },
        end: Location {
          line: 3,
          offset: 39,
        },
      },
      Token {
        token: Int32(3),
        begin: Location {
          line: 3,
          offset: 39,
        },
        end: Location {
          line: 3,
          offset: 40,
        },
      },
      Token {
        token: Add,
        begin: Location {
          line: 3,
          offset: 40,
        },
        end: Location {
          line: 3,
          offset: 41,
        },
      },
      Token {
        token: Int32(5),
        begin: Location {
          line: 3,
          offset: 41,
        },
        end: Location {
          line: 3,
          offset: 42,
        },
      },
      Token {
        token: Multiply,
        begin: Location {
          line: 3,
          offset: 42,
        },
        end: Location {
          line: 3,
          offset: 43,
        },
      },
      Token {
        token: Int32(-7),
        begin: Location {
          line: 3,
          offset: 43,
        },
        end: Location {
          line: 3,
          offset: 45,
        },
      },
      Token {
        token: Delimiter,
        begin: Location {
          line: 3,
          offset: 45,
        },
        end: Location {
          line: 3,
          offset: 46,
        },
      },
      Token {
        token: Int32(11),
        begin: Location {
          line: 3,
          offset: 47,
        },
        end: Location {
          line: 3,
          offset: 49,
        },
      },
      Token {
        token: Multiply,
        begin: Location {
          line: 3,
          offset: 49,
        },
        end: Location {
          line: 3,
          offset: 50,
        },
      },
      Token {
        token: Int32(13),
        begin: Location {
          line: 3,
          offset: 50,
        },
        end: Location {
          line: 3,
          offset: 52,
        },
      },
      Token {
        token: Subtract,
        begin: Location {
          line: 3,
          offset: 52,
        },
        end: Location {
          line: 3,
          offset: 53,
        },
      },
      Token {
        token: Int32(15),
        begin: Location {
          line: 3,
          offset: 53,
        },
        end: Location {
          line: 3,
          offset: 55,
        },
      },
      Token {
        token: ParenthesesR,
        begin: Location {
          line: 3,
          offset: 55,
        },
        end: Location {
          line: 3,
          offset: 56,
        },
      },
    ];

    assert_eq!(actual, expected);
  }

  #[test]
  fn milestone_4() {
    let actual = lex(
      &"#!/usr/bin/env ichop

        a := 3
        b := a + 5
        c := 7

        stdout max(b*c)",
    );

    assert!(actual.is_ok());
    let actual = actual.unwrap();
    let actual = actual.into_iter().map(|t| t.token).collect::<Vec<_>>();

    let expected = vec![
      Ident("a".to_string()),
      DefineLocal,
      Int32(3),
      Ident("b".to_string()),
      DefineLocal,
      Ident("a".to_string()),
      Add,
      Int32(5),
      Ident("c".to_string()),
      DefineLocal,
      Int32(7),
      Ident("stdout".to_string()),
      Ident("max".to_string()),
      ParenthesesL,
      Ident("b".to_string()),
      Multiply,
      Ident("c".to_string()),
      ParenthesesR,
    ];

    assert_eq!(actual, expected);
  }

}
