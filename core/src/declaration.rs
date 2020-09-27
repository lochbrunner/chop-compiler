use std::collections::HashMap;
use std::fmt;

use crate::ast;
use crate::error::{CompilerError, Location};
use crate::token;

#[derive(PartialEq, Debug, Clone)]
pub enum Type {
    Int8,
    Int16,
    Int32,
    Int64,
    Void,
}

impl Type {
    pub fn from_token(token: &token::Token) -> Type {
        match token.token {
            token::TokenPayload::Ident(ref ident) => match ident as &str {
                "i8" => Type::Int8,
                "i16" => Type::Int16,
                "i32" => Type::Int32,
                "i64" => Type::Int64,
                _ => Type::Int32,
            },
            _ => Type::Int32,
        }
    }

    pub fn from_sparse_token(token: &ast::SparseToken) -> Type {
        match token.payload {
            ast::AstTokenPayload::Symbol(ref ident) => match ident as &str {
                "i8" => Type::Int8,
                "i16" => Type::Int16,
                "i32" => Type::Int32,
                "i64" => Type::Int64,
                _ => Type::Int32,
            },
            _ => Type::Int32,
        }
    }

    pub fn from_dense_token(token: &ast::DenseToken) -> Type {
        match token.payload {
            ast::AstTokenPayload::Symbol(ref ident) => match ident as &str {
                "i8" => Type::Int8,
                "i16" => Type::Int16,
                "i32" => Type::Int32,
                "i64" => Type::Int64,
                _ => Type::Int32,
            },
            _ => Type::Int32,
        }
    }
}

#[derive(PartialEq, Clone)]
pub struct Signature<T> {
    pub return_type: T,
    pub args: Vec<T>,
}
impl<T> fmt::Debug for Signature<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}({:?})", self.return_type, self.args)
    }
}

type LazySignature = fn(
    &Signature<Option<Type>>,
    partial: &Signature<Option<Type>>,
) -> Result<Signature<Type>, String>;

pub struct Declaration {
    pub signature: Signature<Option<Type>>,
    pub deduce_complete: LazySignature,
    // #[deprecated(note = "This is equal with return type being Void")]
    pub is_statement: bool,
}

impl fmt::Debug for Declaration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.signature)
    }
}

#[cfg(test)]
impl PartialEq for Declaration {
    fn eq(&self, other: &Self) -> bool {
        self.signature == other.signature
    }
}

impl Declaration {
    fn merge(a: &Option<Type>, b: &Option<Type>) -> Result<Type, String> {
        if let Some(a_type) = a {
            if let Some(b_type) = b {
                if b_type != a_type {
                    Err(format!("Type {:?} and {:?} do not match", a_type, b_type))
                } else {
                    Ok(a_type.clone())
                }
            } else {
                Ok(a_type.clone())
            }
        } else if let Some(b_type) = b {
            Ok(b_type.clone())
        } else {
            Err("None of the signatures has any type".to_string())
        }
    }

    /// Ignores all types are the same
    pub fn full_template_statement(num_args: usize) -> Declaration {
        Declaration {
            is_statement: true,
            signature: Signature {
                return_type: Some(Type::Void),
                args: vec![None; num_args],
            },
            deduce_complete: |_, partial| {
                fn get_type(args: &[Option<Type>]) -> Option<Type> {
                    for arg in args.iter() {
                        if let Some(t) = arg {
                            return Some(t.clone());
                        }
                    }
                    None
                }
                // Get at least one type
                let tp = if let Some(tp) = get_type(&partial.args) {
                    tp
                } else {
                    return Err(format!("No types found in {:?}", partial));
                };
                let args_count = partial.args.len();
                Ok(Signature {
                    return_type: Type::Void,
                    args: vec![tp; args_count],
                })
            },
        }
    }
    /// Ignores all types are the same
    pub fn full_template_function(num_args: usize) -> Declaration {
        Declaration {
            is_statement: false,
            signature: Signature {
                return_type: None,
                args: vec![None; num_args],
            },
            deduce_complete: |_, partial| {
                fn get_type(args: &[Option<Type>]) -> Option<Type> {
                    for arg in args.iter() {
                        if let Some(t) = arg {
                            return Some(t.clone());
                        }
                    }
                    None
                }
                // Get at least one type
                let Signature { return_type, args } = partial;
                let tp = if let Some(tp) = return_type {
                    tp.clone()
                } else if let Some(tp) = get_type(&args) {
                    tp
                } else {
                    return Err(format!("No types found in {:?}({:?})", return_type, args));
                };
                let args_count = partial.args.len();
                Ok(Signature {
                    return_type: tp.clone(),
                    args: vec![tp; args_count],
                })
            },
        }
    }
    /// Use this if all types are constant.
    pub fn function(return_type: Type, args: Vec<Type>, is_statement: bool) -> Declaration {
        Declaration {
            is_statement,
            signature: Signature {
                return_type: Some(return_type),
                args: args.iter().cloned().map(Some).collect(),
            },
            deduce_complete: |decl, partial| {
                let return_type = Declaration::merge(&partial.return_type, &decl.return_type)?;
                if partial.args.len() != decl.args.len() {
                    return Err(format!(
                        "Expected {} arguments but got {}",
                        decl.args.len(),
                        partial.args.len()
                    ));
                }

                let args = decl
                    .args
                    .iter()
                    .zip(partial.args.iter())
                    .map(|(d, p)| Declaration::merge(&d, &p))
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(Signature { return_type, args })
            },
        }
    }
    /// Use this if all types are constant.
    pub fn variable(return_type: Type) -> Declaration {
        Declaration {
            is_statement: false,
            signature: Signature {
                return_type: Some(return_type),
                args: vec![],
            },
            deduce_complete: |decl, partial| {
                let return_type = Declaration::merge(&partial.return_type, &decl.return_type)?;
                Ok(Signature {
                    return_type,
                    args: vec![],
                })
            },
        }
    }

    pub fn req_args_count(&self) -> usize {
        self.signature.args.len()
    }
}

#[derive(Debug)]
pub struct Context {
    pub declarations: HashMap<String, Declaration>,
}

impl Context {
    pub fn get_declaration(
        &self,
        ident: &str,
        location: &Location,
    ) -> Result<&Declaration, CompilerError> {
        match self.declarations.get(ident) {
            None => Err(CompilerError {
                location: location.clone(),
                msg: format!("Symbol {} was not defined.", ident),
            }),
            Some(dec) => Ok(dec),
        }
    }
}
