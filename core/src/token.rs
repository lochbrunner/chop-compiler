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
    // Operators
    Pipe, // |
    // Modifiers
    // Mutable, // mut,

    // Delimiters
    // Dot,
    ParenthesesL,
    ParenthesesR,
    // BraceL,
    // BraceR,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub token: TokenPayload,
    pub begin: Location,
    pub end: Location,
    // pub filename: &str,
}
