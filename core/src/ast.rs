use crate::token::Token;

#[derive(Debug, Clone, PartialEq)]
pub struct Node<T> {
    pub root: T,
    pub args: Vec<Node<T>>,
}

impl<T> Node<T> {
    pub fn new(token: T) -> Node<T> {
        Node {
            root: token,
            args: vec![],
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Ast {
    pub statements: Vec<Node<Token>>,
}

#[cfg(test)]
use crate::token::TokenPayload;

#[cfg(test)]
#[derive(Debug, PartialEq)]
/// For Debugging only
pub struct DebugAst {
    pub statements: Vec<Node<TokenPayload>>,
}

#[cfg(test)]
impl DebugAst {
    fn clone_nodes(nodes: &[Node<Token>]) -> Vec<Node<TokenPayload>> {
        nodes
            .iter()
            .map(|node| Node {
                root: node.root.token.clone(),
                args: DebugAst::clone_nodes(&node.args),
            })
            .collect()
    }

    pub fn new(ast: &Ast) -> DebugAst {
        DebugAst {
            statements: DebugAst::clone_nodes(&ast.statements),
        }
    }

    fn move_nodes(nodes: Vec<Node<Token>>) -> Vec<Node<TokenPayload>> {
        nodes
            .into_iter()
            .map(|node| Node {
                root: node.root.token,
                args: DebugAst::move_nodes(node.args),
            })
            .collect()
    }

    pub fn from(ast: Ast) -> DebugAst {
        DebugAst {
            statements: DebugAst::move_nodes(ast.statements),
        }
    }
}
