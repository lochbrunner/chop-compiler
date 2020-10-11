use crate::error::Location;
use crate::token::{Token, TokenPayload};
use crate::CompilerError;
use nom::{
  branch::alt,
  bytes::complete::{tag, take_until, take_while},
  character::complete::{alpha0, alphanumeric0},
  combinator::{complete, map, opt},
  error::{ErrorKind, ParseError},
  multi::{many0, many1},
  sequence::{pair, preceded, terminated},
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
      loc: Location {
        line: begin.line,
        begin: begin.offset,
        end: end.offset,
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
    map(tag(":"), |_| TokenPayload::TypeDeclaration),
    map(tag("as"), |_| TokenPayload::Cast),
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
  match slice.fragment.parse::<i64>() {
    Ok(value) => set_accept_literal(
      false,
      Ok((
        code,
        TokenPayload::Integer(if sign { -value } else { value }),
      )),
    ),
    Err(_) => Err(nom::Err::Error((code, ErrorKind::Tag))),
  }
}

fn parse_ident(code: Span) -> IResult<Span, TokenPayload> {
  let (code, (first, second)) = pair(alpha0, alphanumeric0)(code)?;
  let ident = format!("{}{}", first.fragment, second.fragment);
  if ident.is_empty() {
    Err(nom::Err::Error((code, ErrorKind::Tag)))
  } else {
    Ok((code, TokenPayload::Ident(ident)))
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
            begin: remaining.offset,
            end: remaining.offset,
          },
        })
      }
    }
    Err(error) => match error {
      nom::Err::Incomplete(_) => Err(CompilerError {
        msg: "Incomplete".to_string(),
        location: Default::default(),
      }),
      nom::Err::Error(error) => Err(CompilerError {
        msg: format!("{:?} Error: {:?}", error.1, error.0.fragment),
        location: Location {
          line: error.0.line,
          begin: error.0.offset,
          end: error.0.offset,
        },
      }),
      nom::Err::Failure(error) => Err(CompilerError {
        msg: format!("{:?} Failure: {:?}", error.1, error.0.fragment),
        location: Location {
          line: error.0.line,
          begin: error.0.offset,
          end: error.0.offset,
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
      loc: Location {
        line: 1,
        begin: 0,
        end: 2,
      },
    }];

    assert_eq!(actual, expected);
  }

  #[test]
  fn multiple_ops_and_ws() {
    let actual = lex(&" := \t |\n :=").unwrap();
    let expected = vec![
      Token {
        token: TokenPayload::DefineLocal,
        loc: Location {
          line: 1,
          begin: 1,
          end: 3,
        },
      },
      Token {
        token: TokenPayload::Pipe,
        loc: Location {
          line: 1,
          begin: 6,
          end: 7,
        },
      },
      Token {
        token: TokenPayload::DefineLocal,
        loc: Location {
          line: 2,
          begin: 9,
          end: 11,
        },
      },
    ];

    assert_eq!(actual, expected);
  }

  #[test]
  fn error_unknown_op() {
    let actual = lex(&"~");
    let expected = Err(CompilerError {
      location: Location {
        line: 1,
        begin: 0,
        end: 0,
      },
      msg: "Tag Error: \"~\"".to_owned(),
    });

    assert!(actual.is_err());
    assert_eq!(actual, expected);
  }

  #[test]
  fn error_incomplete_parse() {
    let actual = lex(&"| := ~ |");
    let expected = Err(CompilerError {
      location: Location {
        line: 1,
        begin: 5,
        end: 5,
      },
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
        token: TokenPayload::Integer(42),
        loc: Location {
          line: 3,
          begin: 28,
          end: 30,
        },
      },
      Token {
        token: TokenPayload::Pipe,
        loc: Location {
          line: 3,
          begin: 31,
          end: 32,
        },
      },
      Token {
        token: TokenPayload::Ident("stdout".to_owned()),
        loc: Location {
          line: 3,
          begin: 33,
          end: 39,
        },
      },
    ];
    assert_eq!(actual, expected);
  }

  #[test]
  fn function_with_braces() {
    let actual = lex("stdout(42)");
    assert_ok!(actual);
    let actual = actual.unwrap();

    let expected = vec![
      Token {
        token: TokenPayload::Ident("stdout".to_string()),
        loc: Location {
          line: 1,
          begin: 0,
          end: 6,
        },
      },
      Token {
        token: TokenPayload::ParenthesesL,
        loc: Location {
          line: 1,
          begin: 6,
          end: 7,
        },
      },
      Token {
        token: TokenPayload::Integer(42),
        loc: Location {
          line: 1,
          begin: 7,
          end: 9,
        },
      },
      Token {
        token: TokenPayload::ParenthesesR,
        loc: Location {
          line: 1,
          begin: 9,
          end: 10,
        },
      },
    ];

    assert_eq!(actual, expected);
  }

  #[test]
  fn function_without_braces() {
    let actual = lex("stdout 42");
    assert_ok!(actual);
    let actual = actual.unwrap();

    let expected = vec![
      Token {
        token: TokenPayload::Ident("stdout".to_string()),
        loc: Location {
          line: 1,
          begin: 0,
          end: 6,
        },
      },
      Token {
        token: TokenPayload::Integer(42),
        loc: Location {
          line: 1,
          begin: 7,
          end: 9,
        },
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

    assert_ok!(actual);
    let actual = actual.unwrap();
    let actual = actual.into_iter().map(|t| t.token).collect::<Vec<_>>();

    let expected = vec![
      Ident("stdout".to_string()),
      Ident("max".to_string()),
      ParenthesesL,
      Integer(3),
      Delimiter,
      Integer(5),
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

    assert_ok!(actual);
    let actual = actual.unwrap();

    let expected = vec![
      Token {
        token: Ident("stdout".to_string()),
        loc: Location {
          line: 3,
          begin: 28,
          end: 34,
        },
      },
      Token {
        token: Ident("max".to_string()),
        loc: Location {
          line: 3,
          begin: 35,
          end: 38,
        },
      },
      Token {
        token: ParenthesesL,
        loc: Location {
          line: 3,
          begin: 38,
          end: 39,
        },
      },
      Token {
        token: Integer(3),
        loc: Location {
          line: 3,
          begin: 39,
          end: 40,
        },
      },
      Token {
        token: Add,
        loc: Location {
          line: 3,
          begin: 40,
          end: 41,
        },
      },
      Token {
        token: Integer(5),
        loc: Location {
          line: 3,
          begin: 41,
          end: 42,
        },
      },
      Token {
        token: Multiply,
        loc: Location {
          line: 3,
          begin: 42,
          end: 43,
        },
      },
      Token {
        token: Integer(-7),
        loc: Location {
          line: 3,
          begin: 43,
          end: 45,
        },
      },
      Token {
        token: Delimiter,
        loc: Location {
          line: 3,
          begin: 45,
          end: 46,
        },
      },
      Token {
        token: Integer(11),
        loc: Location {
          line: 3,
          begin: 47,
          end: 49,
        },
      },
      Token {
        token: Multiply,
        loc: Location {
          line: 3,
          begin: 49,
          end: 50,
        },
      },
      Token {
        token: Integer(13),
        loc: Location {
          line: 3,
          begin: 50,
          end: 52,
        },
      },
      Token {
        token: Subtract,
        loc: Location {
          line: 3,
          begin: 52,
          end: 53,
        },
      },
      Token {
        token: Integer(15),
        loc: Location {
          line: 3,
          begin: 53,
          end: 55,
        },
      },
      Token {
        token: ParenthesesR,
        loc: Location {
          line: 3,
          begin: 55,
          end: 56,
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

    assert_ok!(actual);
    let actual = actual.unwrap();
    let actual = actual.into_iter().map(|t| t.token).collect::<Vec<_>>();

    let expected = vec![
      Ident("a".to_string()),
      DefineLocal,
      Integer(3),
      Ident("b".to_string()),
      DefineLocal,
      Ident("a".to_string()),
      Add,
      Integer(5),
      Ident("c".to_string()),
      DefineLocal,
      Integer(7),
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

  #[test]
  fn milestone_5() {
    let actual = lex(
      &"#!/usr/bin/env ichop

        a: i32 := 3
        b: i8 := a as i8 + 5
        c: i8 := 7

        stdout max(b,c)",
    );

    assert_ok!(actual);
    let actual = actual.unwrap();
    let actual = actual.into_iter().map(|t| t.token).collect::<Vec<_>>();

    let expected = [
      Ident("a".to_string()),
      TypeDeclaration,
      Ident("i32".to_string()),
      DefineLocal,
      Integer(3),
      Ident("b".to_string()),
      TypeDeclaration,
      Ident("i8".to_string()),
      DefineLocal,
      Ident("a".to_string()),
      Cast,
      Ident("i8".to_string()),
      Add,
      Integer(5),
      Ident("c".to_string()),
      TypeDeclaration,
      Ident("i8".to_string()),
      DefineLocal,
      Integer(7),
      Ident("stdout".to_string()),
      Ident("max".to_string()),
      ParenthesesL,
      Ident("b".to_string()),
      Delimiter,
      Ident("c".to_string()),
      ParenthesesR,
    ];

    assert_eq!(actual, expected);
  }
}
