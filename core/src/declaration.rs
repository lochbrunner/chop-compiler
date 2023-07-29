use std::collections::HashMap;
use std::fmt;
use std::str::FromStr;

use crate::ast;
use crate::error::{CompilerError, Location};
use crate::token;

#[derive(PartialEq, Debug, Clone)]
pub enum Type {
    Int8,
    Int16,
    Int32,
    Int64,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    USize,
    Float32,
    Float64,
    Void,
    Type,
    Struct(ast::Struct),
}

impl FromStr for Type {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "i8" => Ok(Type::Int8),
            "i16" => Ok(Type::Int16),
            "i32" => Ok(Type::Int32),
            "i64" => Ok(Type::Int64),
            "u8" => Ok(Type::UInt8),
            "u16" => Ok(Type::UInt16),
            "u32" => Ok(Type::UInt32),
            "u64" => Ok(Type::UInt64),
            "usize" => Ok(Type::USize),
            "f32" => Ok(Type::Float32),
            "f64" => Ok(Type::Float64),
            _ => Err(()),
        }
    }
}

impl Type {
    pub fn from_token(token: &token::Token) -> Type {
        match token.token {
            token::TokenPayload::Ident(ref ident) => Type::from_str(ident).unwrap_or(Type::Int32),
            _ => Type::Int32,
        }
    }

    pub fn from_sparse_token(token: &ast::SparseToken) -> Type {
        match token.payload {
            ast::AstTokenPayload::Symbol(ref ident) => Type::from_str(ident).unwrap_or(Type::Int32),
            _ => Type::Int32,
        }
    }

    pub fn from_dense_token(token: &ast::DenseToken) -> Type {
        match token.payload {
            ast::AstTokenPayload::Symbol(ref ident) => Type::from_str(ident).unwrap_or(Type::Int32),
            _ => Type::Int32,
        }
    }

    pub fn merge(a: &Option<Self>, b: &Option<Self>) -> Result<Option<Self>, ()> {
        if let Some(a) = a {
            if let Some(b) = b {
                if b != a {
                    Err(())
                } else {
                    Ok(Some(a.clone()))
                }
            } else {
                Ok(Some(a.clone()))
            }
        } else {
            Ok(b.clone())
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Type::Int8 => "int8",
            Type::Int16 => "int16",
            Type::Int32 => "int32",
            Type::Int64 => "int64",
            Type::UInt8 => "uint8",
            Type::UInt16 => "uint16",
            Type::UInt32 => "uint32",
            Type::UInt64 => "uint64",
            Type::USize => "usize",
            Type::Float32 => "float32",
            Type::Float64 => "float64",
            Type::Void => "void",
            Type::Type => "type",
            Type::Struct(_) => "struct",
        };
        write!(f, "{}", s)
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

#[derive(Debug, Clone, PartialEq)]
pub enum Visibility {
    Local,  // :=
    Public, // :+
}

pub struct Declaration {
    pub signature: Signature<Option<Type>>,
    pub deduce_complete: LazySignature,
    // #[deprecated(note = "This is equal with return type being Void")]
    pub is_statement: bool,
    pub visibility: Visibility,
}

impl fmt::Debug for Declaration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} {:?}", self.signature, self.visibility)
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
                } else if let Some(ref return_type) = partial.return_type {
                    return_type.clone()
                } else {
                    return Err(format!("[D1]: No types found in {:?}", partial));
                };
                let args_count = partial.args.len();
                Ok(Signature {
                    return_type: Type::Void,
                    args: vec![tp; args_count],
                })
            },
            visibility: Visibility::Local,
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
            visibility: Visibility::Local,
        }
    }
    /// Use this if all types are constant.
    pub fn function(
        return_type: Type,
        args: Vec<Type>,
        is_statement: bool,
        visibility: Visibility,
    ) -> Declaration {
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
            visibility,
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
            visibility: Visibility::Local,
        }
    }

    pub fn req_args_count(&self) -> usize {
        self.signature.args.len()
    }

    pub fn is_type(&self) -> bool {
        // TODO: use deduce_complete here later
        if let Some(dtype) = &self.signature.return_type {
            dtype == &Type::Type
        } else {
            false
        }
    }
}

#[derive(Debug)]
pub struct Context<'a> {
    pub declarations: HashMap<String, Declaration>,
    pub lower: Option<&'a Context<'a>>,
}

impl<'a> Context<'a> {
    pub fn gen_struct(&self) -> ast::Struct {
        ast::Struct {
            fields: self
                .declarations
                .iter()
                .filter(|(_, d)| d.visibility == Visibility::Public)
                .map(|(n, d)| (n.clone(), d.signature.clone()))
                .collect(),
            local_fields: self
            .declarations
            .iter()
            .filter(|(_, d)| d.visibility == Visibility::Local)
            .map(|(n, d)| (n.clone(), d.signature.clone()))
            .collect(),
        }
    }
    pub fn try_get_declaration(&self, ident: &str) -> Option<&Declaration> {
        match self.declarations.get(ident) {
            None => match self.lower {
                Some(lower) => lower.try_get_declaration(ident),
                None => None,
            },
            Some(dec) => Some(dec),
        }
    }
    pub fn get_declaration(
        &self,
        ident: &str,
        location: &Location,
    ) -> Result<&Declaration, CompilerError> {
        self.try_get_declaration(ident).ok_or(CompilerError {
            location: location.clone(),
            msg: format!("[C1] Symbol {} was not defined.", ident),
        })
    }

    pub fn new() -> Self {
        Self {
            declarations: HashMap::new(),
            lower: None,
        }
    }

    pub fn up<'b>(&'b self) -> Self
    where
        'b: 'a,
    {
        Self {
            declarations: HashMap::new(),
            lower: Some(self),
        }
    }

    pub fn from_struct(structs: &ast::Struct) -> Self {
        Self {
            declarations: structs
                .fields
                .iter()
                .map(|(n, s)| {
                    (
                        n.clone(),
                        Declaration {
                            deduce_complete: |_, _| Err("".to_owned()),
                            signature: s.clone(),
                            visibility: Visibility::Public,
                            is_statement: false,
                        },
                    )
                })
                .collect(),
            lower: None,
        }
    }
}

impl<'a> Default for Context<'a> {
    /// Milestone 5 context
    fn default() -> Self {
        Self {
            declarations: hashmap! {
                "stdout".to_string() => Declaration::full_template_statement(1),
                "max".to_string() => Declaration::full_template_function(2),
                "min".to_string() => Declaration::full_template_function(2),
                "i8".to_string() => Declaration::variable(Type::Type),
                "i16".to_string() => Declaration::variable(Type::Type),
                "i32".to_string() => Declaration::variable(Type::Type),
                "i64".to_string() => Declaration::variable(Type::Type),
                "u8".to_string() => Declaration::variable(Type::Type),
                "u16".to_string() => Declaration::variable(Type::Type),
                "u32".to_string() => Declaration::variable(Type::Type),
                "u64".to_string() => Declaration::variable(Type::Type),
                "usize".to_string() => Declaration::variable(Type::Type),
                "f32".to_string() => Declaration::variable(Type::Type),
                "f64".to_string() => Declaration::variable(Type::Type),
            },
            lower: None,
        }
    }
}
