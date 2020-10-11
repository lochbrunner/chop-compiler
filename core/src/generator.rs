use crate::ast::{AstTokenPayload, DenseAst, Node, SparseAst, SparseToken};
use crate::CompilerError;

pub fn generate_sparse(statement: Node<SparseToken>) -> Result<Node<SparseToken>, CompilerError> {
    match statement.root.payload {
        AstTokenPayload::Pipe => Ok(Node {
            root: statement.args[1].root.clone(),
            args: vec![statement.args[0].clone()],
        }),
        AstTokenPayload::Symbol(_) => Ok(statement), // Function Call
        AstTokenPayload::DefineLocal(_) => Ok(statement),
        _ => Err(CompilerError {
            location: statement.root.loc.clone(),
            msg: format!(
                "Generator Error: Token {:?} is not implemented yet!",
                statement.root.payload
            ),
        }),
    }
}

pub fn generate_sparse_multiple(ast: SparseAst) -> Result<SparseAst, CompilerError> {
    let statements = ast
        .statements
        .into_iter()
        .map(|statement| generate_sparse(statement))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SparseAst { statements })
}

/// Fills out the macros and runs all the custom compiler stuff.
pub fn generate(ast: DenseAst) -> Result<DenseAst, CompilerError> {
    let statements = ast
        .statements
        .into_iter()
        .map(|statement| match statement.root.payload {
            AstTokenPayload::Pipe => Ok(Node {
                root: statement.args[1].root.clone(),
                args: vec![statement.args[0].clone()],
            }),
            AstTokenPayload::Symbol(_) => Ok(statement), // Function Call
            AstTokenPayload::DefineLocal(_) => Ok(statement),
            _ => Err(CompilerError {
                location: statement.root.loc.clone(),
                msg: format!(
                    "Generator Error: Token {:?} is not implemented yet!",
                    statement.root.payload
                ),
            }),
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(DenseAst { statements })
}

#[cfg(test)]
mod specs {
    use super::*;
    use crate::ast::{DenseToken, IntegerProvider};
    use crate::declaration::Type;
    use crate::error::Location;

    #[test]
    fn milestone_1() {
        let input = DenseAst {
            statements: vec![Node {
                root: DenseToken {
                    payload: AstTokenPayload::Pipe,
                    return_type: Type::Int32,
                    loc: Location {
                        line: 3,
                        begin: 31,
                        end: 32,
                    },
                },
                args: vec![
                    Node::leaf(DenseToken {
                        payload: AstTokenPayload::Integer(IntegerProvider { content: 42 }),
                        return_type: Type::Int32,
                        loc: Location {
                            line: 3,
                            begin: 28,
                            end: 30,
                        },
                    }),
                    Node::leaf(DenseToken {
                        payload: AstTokenPayload::Symbol("stdout".to_owned()),
                        return_type: Type::Int32,
                        loc: Location {
                            line: 3,
                            begin: 33,
                            end: 39,
                        },
                    }),
                ],
            }],
        };

        let actual = generate(input);
        assert_ok!(actual);
        let actual = actual.unwrap();
        let expected = DenseAst {
            statements: vec![Node {
                root: DenseToken {
                    payload: AstTokenPayload::Symbol("stdout".to_owned()),
                    return_type: Type::Int32,
                    loc: Location {
                        line: 3,
                        begin: 33,
                        end: 39,
                    },
                },
                args: vec![Node::leaf(DenseToken {
                    payload: AstTokenPayload::Integer(IntegerProvider { content: 42 }),
                    return_type: Type::Int32,
                    loc: Location {
                        line: 3,
                        begin: 28,
                        end: 30,
                    },
                })],
            }],
        };
        assert_eq!(actual, expected);
    }
}
