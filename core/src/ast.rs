use crate::declaration::Type;
use crate::error::{Locatable, Location};
use std::fmt;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq)]
pub struct Node<T> {
    pub root: T,
    pub args: Vec<Node<T>>,
}

impl<T> Node<T> {
    pub fn leaf(token: T) -> Node<T> {
        Node {
            root: token,
            args: vec![],
        }
    }
}

/// Should we split language specific AST and User defined (=dynamic) AST?
// pub struct DefinitionNode<T> {
//     pub ident: String,
//     pub type_string: Option<String>,
//     pub value: Node<T>,
//     pub begin: Location,
//     pub end: Location,
// }

// pub enum AstNode {
//     Dynamic(Node<Token>),
//     Definition(DefinitionNode<Token>),
// }
use crate::token::TokenPayload;

#[derive(Debug, Clone, PartialEq)]
pub struct IntegerProvider {
    pub content: i64,
}

// pub trait Convert {
//     type Underlying;
//     fn convert(self) -> Result<Self::Underlying, String>;
// }

// impl<T> Convert for Result<T, std::num::ParseIntError> {
//     type Underlying = T;

//     fn convert(self) -> Result<T, String> {
//         match self {
//             Ok(t) => Ok(t),
//             Err(err) => Err(format!("{:?}", err)),
//         }
//     }
// }

impl IntegerProvider {
    // pub fn get_i8(&self) -> Result<i8, String> {
    //     self.content.parse().map_err(|e| format!("{:?}", e))
    // }
    // pub fn get_i16(&self) -> Result<i16, String> {
    //     self.content.parse().map_err(|e| format!("{:?}", e))
    // }
    // pub fn get_i32(&self) -> Result<i32, String> {
    //     self.content.parse().map_err(|e| format!("{:?}", e))
    // }
    // pub fn get_i64(&self) -> Result<i64, String> {
    //     self.content.parse().map_err(|e| format!("{:?}", e))
    // }
}

#[derive(Debug, Clone, PartialEq)]
pub enum AstTokenPayload {
    // Comment,
    Symbol(String),
    // Literals
    Integer(IntegerProvider),
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
}

impl AstTokenPayload {
    pub fn from(prev: TokenPayload) -> Result<AstTokenPayload, String> {
        match prev {
            TokenPayload::Ident(ident) => Ok(AstTokenPayload::Symbol(ident)),
            TokenPayload::Integer(content) => {
                Ok(AstTokenPayload::Integer(IntegerProvider { content }))
            }
            TokenPayload::DefineLocal => Ok(AstTokenPayload::DefineLocal),
            TokenPayload::Cast => Ok(AstTokenPayload::Cast),
            TokenPayload::Pipe => Ok(AstTokenPayload::Pipe),
            TokenPayload::Multiply => Ok(AstTokenPayload::Multiply),
            TokenPayload::Divide => Ok(AstTokenPayload::Divide),
            TokenPayload::Add => Ok(AstTokenPayload::Add),
            TokenPayload::Subtract => Ok(AstTokenPayload::Subtract),
            TokenPayload::Remainder => Ok(AstTokenPayload::Remainder),
            _ => Err(format!("{:?} is not a valid type for Ast.", prev)),
        }
    }

    pub fn get_ident(&self) -> Option<&str> {
        if let AstTokenPayload::Symbol(ref ident) = self {
            Some(ident)
        } else {
            None
        }
    }
}

#[derive(Clone)]
pub struct SparseToken {
    pub payload: AstTokenPayload,
    // pub return_type: &'a dyn Fn(Option<Type>) -> Option<Type>,
    pub return_type: Rc<dyn Fn(Option<Type>) -> Option<Type>>,
    // pub static_value: fn() -> Option<>,
    pub loc: Location,
}

impl fmt::Debug for SparseToken {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.payload)
    }
}

impl PartialEq for SparseToken {
    fn eq(&self, other: &Self) -> bool {
        self.payload == other.payload
    }
}

impl SparseToken {
    pub fn stub(payload: TokenPayload) -> SparseToken {
        SparseToken {
            payload: AstTokenPayload::from(payload).unwrap(),
            return_type: Rc::new(&|_| None),
            loc: Default::default(),
        }
    }
}

impl Locatable for SparseToken {
    fn get_loc(&self) -> &Location {
        &self.loc
    }
}

pub enum Literal {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
}

#[derive(Debug, Clone, PartialEq)]
pub struct DenseToken {
    pub payload: AstTokenPayload,
    pub return_type: Type,
    pub loc: Location,
}

pub trait LexerTokenPayloadStub {
    fn stub_typed(payload: TokenPayload, return_type: Type) -> DenseToken;
    fn stub(payload: TokenPayload) -> DenseToken;
}

pub trait AstTokenPayloadStub {
    fn stub_typed(payload: AstTokenPayload, return_type: Type) -> DenseToken;
    fn stub(payload: AstTokenPayload) -> DenseToken;
}

impl LexerTokenPayloadStub for DenseToken {
    fn stub_typed(payload: TokenPayload, return_type: Type) -> DenseToken {
        DenseToken {
            payload: AstTokenPayload::from(payload).unwrap(),
            return_type,
            loc: Default::default(),
        }
    }
    fn stub(payload: TokenPayload) -> DenseToken {
        DenseToken {
            payload: AstTokenPayload::from(payload).unwrap(),
            return_type: Type::Void,
            loc: Default::default(),
        }
    }
}

impl AstTokenPayloadStub for DenseToken {
    fn stub_typed(payload: AstTokenPayload, return_type: Type) -> DenseToken {
        DenseToken {
            payload,
            return_type,
            loc: Default::default(),
        }
    }
    fn stub(payload: AstTokenPayload) -> DenseToken {
        DenseToken {
            payload,
            return_type: Type::Void,
            loc: Default::default(),
        }
    }
}

impl Locatable for DenseToken {
    fn get_loc(&self) -> &Location {
        &self.loc
    }
}

#[derive(Debug, PartialEq)]
pub struct Ast<T> {
    pub statements: Vec<Node<T>>,
}

pub type SparseAst = Ast<SparseToken>;
pub type DenseAst = Ast<DenseToken>;

#[cfg(test)]
pub type DebugAst = Ast<AstTokenPayload>;

#[cfg(test)]
impl DebugAst {
    fn clone_nodes(nodes: &[Node<SparseToken>]) -> Vec<Node<AstTokenPayload>> {
        nodes
            .iter()
            .map(|node| Node {
                root: node.root.payload.clone(),
                args: DebugAst::clone_nodes(&node.args),
            })
            .collect()
    }

    pub fn new(ast: &SparseAst) -> DebugAst {
        DebugAst {
            statements: DebugAst::clone_nodes(&ast.statements),
        }
    }

    fn move_nodes(nodes: Vec<Node<SparseToken>>) -> Vec<Node<AstTokenPayload>> {
        nodes
            .into_iter()
            .map(|node| Node {
                root: node.root.payload,
                args: DebugAst::move_nodes(node.args),
            })
            .collect()
    }

    pub fn from(ast: SparseAst) -> DebugAst {
        DebugAst {
            statements: DebugAst::move_nodes(ast.statements),
        }
    }
}
