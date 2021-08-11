use crate::error::{Locatable, Location};
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum TokenPayload {
    // Comment,
    Ident(String),
    // Literals
    Integer(i64),
    // Float32(f32),
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
    TypeDeclaration,
    // BraceL,
    // BraceR,
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

#[derive(Clone, PartialEq)]
pub struct Token {
    pub token: TokenPayload,
    pub loc: Location,
    // pub filename: &str,
}

impl fmt::Debug for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.token)
    }
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
    fn get_loc<'a>(&'a self) -> &'a Location {
        &self.loc
    }
}
