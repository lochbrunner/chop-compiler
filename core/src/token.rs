use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub struct Location {
    pub line: u32,
    pub offset: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenPayload {
    // Comment,
    Ident(String),
    // Literals
    Int32(i32),
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
    pub begin: Location,
    pub end: Location,
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
            begin: Location { line: 0, offset: 0 },
            end: Location { line: 0, offset: 0 },
        }
    }
}
