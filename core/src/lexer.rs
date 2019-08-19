use crate::token::{Token,Location, TokenPayload};
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

type Span<'a> = LocatedSpanEx<&'a str, &'a str>;

fn sp<'a, E: ParseError<Span<'a>>>(i: Span<'a>) -> IResult<Span<'a>, Span<'a>, E> {
  let chars = " \t\r\n";
  take_while(move |c| chars.contains(c))(i)
}

impl Token {
  pub fn new(
    begin: LocatedSpanEx<&str, &str>,
    end: LocatedSpanEx<&str, &str>,
    payload: TokenPayload,
  ) -> Token {
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
  let (code, slice) = take_while(move |c| chars.contains(c))(code)?;
  match slice.fragment.parse::<i32>() {
    Ok(value) => Ok((code, TokenPayload::Int32(if sign { -value } else { value }))),
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
  alt((
    map(tag("("), |_| TokenPayload::ParenthesesL),
    map(tag(")"), |_| TokenPayload::ParenthesesR),
  ))(code)
}

fn lex_token(code: Span) -> IResult<Span, Token> {
  let (code, begin) = position(code)?;
  let (code, payload) = alt((operators, parse_integer, parse_ident, parse_punctuation))(code)?;
  let (code, end) = position(code)?;
  Ok((code, Token::new(begin, end, payload)))
}

pub fn lex(code: &str, filename: &str) -> Result<Vec<Token>, CompilerError> {
  let (code, _) = many0(shebang)(Span{fragment: code, extra: filename, offset: 0, line: 1}).unwrap();
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

  #[test]
  fn single_op() {
    let actual = lex(&":= ", &"test").unwrap();
    let expected = vec![Token {
      token: TokenPayload::DefineLocal,
      begin: Location { line: 1, offset: 0 },
      end: Location { line: 1, offset: 2 },
    }];

    assert_eq!(actual, expected);
  }

  #[test]
  fn multiple_ops_and_ws() {
    let actual = lex(&" := \t |\n :=", &"test").unwrap();
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
    let actual = lex(&"~", &"test");
    let expected = Err(CompilerError {
      location: Location { line: 1, offset: 0 },
      msg: "Tag Error: \"~\"".to_owned(),
    });

    assert!(actual.is_err());
    assert_eq!(actual, expected);
  }

  #[test]
  fn error_incomplete_parse() {
    let actual = lex(&"| := ~ |", &"test");
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
      &"test"
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
    let actual = lex("stdout(42)", &"test");
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
    let actual = lex("stdout 42", &"test");
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

}
