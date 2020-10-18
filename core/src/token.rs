use crate::error::{Locatable, Location};
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum TokenPayload {
    // Comment,
    Ident(String),
    // Literals
    Integer(i64),
    Float(f64),
    // TODO: more literals

    // Statements
    DefineLocal, // :=
    // DefinePublic, // :+
    // Declare,      // :
    Cast, // as
    // Operators
    Pipe, // |
    // Modifiers
    // Mutable, // mut,
    // Mathematical
    Multiply,  // *
    Divide,    // /
    Add,       // +
    Subtract,  // -
    Remainder, // %
    // Punctuation
    Delimiter, // ,
    // Dot,
    ParenthesesL,
    ParenthesesR,
    TypeDeclaration, //
                     // BraceL,
                     // BraceR,
}

impl fmt::Display for TokenPayload {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TokenPayload::*;
        let string = match self {
            Ident(ident) => ident.to_owned(),
            Integer(value) => format!("{}", value),
            Float(value) => format!("{}", value),
            DefineLocal => ":=".to_owned(),
            Cast => "as".to_owned(),
            Pipe => "|".to_owned(),
            Multiply => "*".to_owned(),
            Divide => "/".to_owned(),
            Add => "+".to_owned(),
            Subtract => "-".to_owned(),
            Remainder => "%".to_owned(),
            Delimiter => ", ".to_owned(),
            ParenthesesL => "(".to_owned(),
            ParenthesesR => ")".to_owned(),
            TypeDeclaration => ": ".to_owned(),
        };
        write!(f, "{:?}", string)
    }
}

impl TokenPayload {
    pub fn get_ident(&self) -> Option<&str> {
        if let TokenPayload::Ident(ref ident) = self {
            Some(ident)
        } else {
            None
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub token: TokenPayload,
    pub loc: Location,
    // pub filename: &str,
}

#[cfg(test)]
impl Token {
    pub fn stub(token: TokenPayload) -> Token {
        Token {
            token,
            loc: Location {
                line: 0,
                begin: 0,
                end: 0,
            },
        }
    }
}

impl Locatable for Token {
    fn get_loc(&self) -> &Location {
        &self.loc
    }
}
