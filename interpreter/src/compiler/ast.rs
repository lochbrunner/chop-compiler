use crate::compiler::token::Token;

#[derive(Debug, PartialEq)]
pub struct Node {
    pub root: Token,
    pub args: Vec<Token>,
}
#[derive(Debug, PartialEq)]
pub struct Statement {
    pub root: Node,
}

#[derive(Debug, PartialEq)]
pub struct Ast {
    pub statements: Vec<Statement>,
}
