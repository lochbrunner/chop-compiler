use super::token::Token;
use crate::compiler::token::{Location, TokenPayload};
use nom::{
  branch::alt,
  bytes::complete::{tag, take_until, take_while},
  character::complete::{alpha1 as alpha, alphanumeric1},
  combinator::{complete, opt},
  error::{ErrorKind, ParseError},
  multi::{many0, many1},
  sequence::{preceded, terminated},
  IResult,
};
use nom_locate::{position, LocatedSpan, LocatedSpanEx};

// See: https://github.com/fflorent/nom_locate/issues/20

type Span<'a> = LocatedSpan<&'a str>;

fn sp<'a, E: ParseError<Span<'a>>>(i: Span<'a>) -> IResult<Span<'a>, Span<'a>, E> {
  let chars = " \t\r\n";
  take_while(move |c| chars.contains(c))(i)
}

impl Token {
  pub fn new(
    begin: LocatedSpanEx<&str, ()>,
    end: LocatedSpanEx<&str, ()>,
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
      token: payload,
    }
  }
}

fn pipe(code: Span) -> IResult<Span, Token> {
  let (code, begin) = position(code)?;
  let (code, _) = tag("|")(code)?;
  let (code, end) = position(code)?;
  Ok((code, Token::new(begin, end, TokenPayload::Pipe)))
}

fn define_local(code: Span) -> IResult<Span, Token> {
  let (code, begin) = position(code)?;
  let (code, _) = tag(":=")(code)?;
  let (code, end) = position(code)?;
  Ok((code, Token::new(begin, end, TokenPayload::DefineLocal)))
}

fn operators(code: Span) -> IResult<Span, Token> {
  alt((pipe, define_local))(code)
}

fn shebang(code: Span) -> IResult<Span, ()> {
  let (code, begin) = position(code)?;
  let (code, _) = tag("#!")(code)?;
  let (code, _) = take_until("\n")(code)?;
  let (code, end) = position(code)?;
  Ok((code, ()))
}

// Literals
fn parse_integer(code: Span) -> IResult<Span, Token> {
  let chars = "1234567890";
  let (code, begin) = position(code)?;
  // Sign ?
  let (code, sign) = opt(tag("-"))(code)?;
  let sign = match sign {
    Some(_) => true,
    None => false,
  };
  let (code, slice) = take_while(move |c| chars.contains(c))(code)?;
  let (code, end) = position(code)?;
  match slice.fragment.parse::<i32>() {
    Ok(value) => Ok((
      code,
      Token::new(
        begin,
        end,
        TokenPayload::Int32(if sign { -value } else { value }),
      ),
    )),
    Err(_) => Err(nom::Err::Error((code, ErrorKind::Tag))),
  }
}

fn parse_ident(code: Span) -> IResult<Span, Token> {
  let chars = "_";
  let (code, begin) = position(code)?;
  let (code, ident) =
    take_while(move |c: char| c.is_ascii_alphabetic() || chars.contains(c))(code)?;
  let (code, end) = position(code)?;
  if ident.fragment.len() == 0 {
    Err(nom::Err::Error((code, ErrorKind::Tag)))
  } else {
    Ok((
      code,
      Token::new(begin, end, TokenPayload::Ident(ident.fragment.to_owned())),
    ))
  }
}

fn lex_all(code: Span) -> IResult<Span, Token> {
  alt((operators, parse_integer, parse_ident))(code)
}

#[derive(Debug, PartialEq)]
pub struct LexerError {
  location: Location,
  msg: String,
}

pub fn lex(code: &str) -> Result<Vec<Token>, LexerError> {
  let (code, _) = many0(shebang)(Span::new(code)).unwrap();
  let a = complete(many1(preceded(sp, terminated(lex_all, sp))))(code);

  match a {
    Ok((remaining, tokens)) => {
      if remaining.fragment.len() == 0 {
        Ok(tokens)
      } else {
        Err(LexerError {
          msg: format!("Incomplete Error: {:?}", remaining.fragment),
          location: Location {
            line: remaining.line,
            offset: remaining.offset,
          },
        })
      }
    }
    Err(error) => match error {
      nom::Err::Incomplete(_) => Err(LexerError {
        msg: format!("Incomplete"),
        location: Location { line: 0, offset: 0 },
      }),
      nom::Err::Error(error) => Err(LexerError {
        msg: format!("{:?} Error: {:?}", error.1, error.0.fragment),
        location: Location {
          line: error.0.line,
          offset: error.0.offset,
        },
      }),
      nom::Err::Failure(error) => Err(LexerError {
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
    let expected = Err(LexerError {
      location: Location { line: 1, offset: 0 },
      msg: "Tag Error: \"~\"".to_owned(),
    });

    assert!(actual.is_err());
    assert_eq!(actual, expected);
  }

  #[test]
  fn error_incomplete_parse() {
    let actual = lex(&"| := ~ |");
    let expected = Err(LexerError {
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

}
