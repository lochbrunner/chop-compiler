use crate::ast::{DenseAst, DenseToken, Node, SparseAst, SparseToken};
use crate::declaration::Type;
// use crate::token::{Token, TokenPayload};
use crate::CompilerError;

type SparseNode = Node<SparseToken>;
type DenseNode = Node<DenseToken>;

// #[derive(Debug, PartialEq)]
// pub struct TypedNode {
//     node: Node,
//     return_type: Type,
// }

// #[derive(Debug, PartialEq)]
// pub struct SpecialAst {
//     pub statements: Vec<TypedNode>,
// }

fn specialize_node(
    expected: Option<Type>,
) -> impl FnMut(SparseNode) -> Result<DenseNode, CompilerError> {
    |node| {
        let SparseNode {
            root:
                SparseToken {
                    payload,
                    loc,
                    return_type,
                },
            args,
        } = node;
        let args = args
            .into_iter()
            .map(specialize_node(None))
            .collect::<Result<Vec<_>, CompilerError>>()?;

        // Find type child from parent

        Ok(DenseNode {
            root: DenseToken {
                payload,
                loc,
                return_type: return_type(None).unwrap(),
            },
            args,
        })
    }
}

pub fn specialize(ast: SparseAst) -> Result<DenseAst, CompilerError> {
    Ok(DenseAst {
        statements: ast
            .statements
            .into_iter()
            .map(specialize_node(None))
            .collect::<Result<Vec<_>, CompilerError>>()?,
    })
}

#[cfg(test)]
mod specs {
    use super::*;
    use crate::ast::{AstTokenPayload::*, AstTokenPayloadStub, IntegerProvider};

    fn filter(possibilities: &'static [Type]) -> impl FnOnce(Option<Type>) -> Option<Type> {
        move |incoming| match incoming {
            None => None,
            Some(t) => {
                if possibilities.contains(&t) {
                    Some(t)
                } else {
                    None
                }
            }
        }
    }

    #[test]
    fn milestone_1() {
        let sparse = SparseAst {
            statements: vec![Node {
                root: SparseToken {
                    payload: Symbol("stdout".to_owned()),
                    return_type: &|_| Some(Type::Void),
                    loc: Default::default(),
                },
                args: vec![Node::leaf(SparseToken {
                    payload: Integer(IntegerProvider { content: 42 }),
                    return_type: &filter(&vec![Type::Int32]),
                    loc: Default::default(),
                })],
            }],
        };

        let expected = DenseAst {
            statements: vec![Node {
                root: DenseToken::stub(Symbol("stdout".to_owned())),
                args: vec![Node::leaf(DenseToken::stub(Integer(IntegerProvider {
                    content: 42,
                })))],
            }],
        };

        let dense = specialize(sparse);
        assert!(dense.is_ok());
    }
}
