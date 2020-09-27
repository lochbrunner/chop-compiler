use crate::ast::{DenseAst, DenseToken, Node, SparseAst, SparseToken};
use crate::declaration::Type;
use crate::CompilerError;

type SparseNode<'a> = Node<SparseToken>;
type DenseNode = Node<DenseToken>;

fn specialize_node<'a>(
    expected: Option<Type>,
) -> impl FnMut(SparseNode<'a>) -> Result<DenseNode, CompilerError> {
    let expected = expected.unwrap_or(Type::Int32);
    move |node| {
        let SparseNode {
            root:
                SparseToken {
                    payload,
                    loc,
                    return_type,
                },
            args,
        } = node;
        // What are the expected types
        // For now assume each is a Int32
        let args = args
            .into_iter()
            .map(specialize_node(Some(Type::Int32)))
            .collect::<Result<Vec<_>, CompilerError>>()?;

        // Find type child from parent
        let r_type = return_type(None).unwrap_or(expected.clone());

        Ok(DenseNode {
            root: DenseToken {
                payload,
                loc,
                return_type: r_type,
            },
            args,
        })
    }
}

/// THis function tries to find out the actual concrete types in for each node in the AST
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
    use std::rc::Rc;

    fn filter(possibilities: &'static [Type]) -> impl Fn(Option<Type>) -> Option<Type> {
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
                    return_type: Rc::new(|_| Some(Type::Void)),
                    loc: Default::default(),
                },
                args: vec![Node::leaf(SparseToken {
                    payload: Integer(IntegerProvider { content: 42 }),
                    return_type: Rc::new(filter(&[Type::Int32])),
                    loc: Default::default(),
                })],
            }],
        };

        let expected = DenseAst {
            statements: vec![Node {
                root: DenseToken::stub(Symbol("stdout".to_owned())),
                args: vec![Node::leaf(DenseToken::stub_typed(
                    Integer(IntegerProvider { content: 42 }),
                    Type::Int32,
                ))],
            }],
        };

        let dense = specialize(sparse);
        assert!(dense.is_ok());
        assert_eq!(dense.unwrap(), expected);
    }
}
