pub enum Token {
    Eof,
    /// TODO: return slice of code (or slice info)
    Ident(String),

    // Literals
    Int32(i32),
    // TODO: more literals

    // Statements
    DefineLocal,  // :=
    DefinePublic, // :+
    Declare,      // :
    // Modifiers
    Mutable, // mut,

    // Delimiters
    Dot,
    ParenthesesL,
    ParenthesesR,
    BraceL,
    BraceR,
}