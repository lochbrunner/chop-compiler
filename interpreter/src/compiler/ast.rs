use crate::compiler::token::Token;

#[derive(Debug, Clone, PartialEq)]
pub struct Node {
    pub root: Token,
    pub args: Vec<Node>,
}

#[cfg(test)]
impl Node {
    pub fn new(token: Token) -> Node {
        Node {
            root: token,
            args: vec![],
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Statement {
    pub root: Node,
}

#[derive(Debug, PartialEq)]
pub struct Ast {
    pub statements: Vec<Statement>,
}
