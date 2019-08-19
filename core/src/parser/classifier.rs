use crate::compiler::token::Token;
use crate::compiler::Context;
use std::slice::Iter;

#[derive(Debug, PartialEq)]
pub enum OperationType {
    Infix,
    Prefix,
    Postfix,
    Function,
    Dummy,
}

#[derive(PartialEq, PartialOrd, Debug, Clone)]
pub enum Precedence {
    PLowest,
    PSeparator,
    PCall,
    POpening,
    // PClosing,
    PEquals,
    PLessGreater,
    PSum,
    PProduct,
    PPower,
    PFaculty,
    // PHighest,
}

#[derive(Debug, PartialEq)]
pub enum BracketDirection {
    Closing,
    Opening,
}
#[derive(Debug, PartialEq)]
pub enum BracketType {
    Round,
}

#[derive(Debug, PartialEq)]
pub struct Bracket {
    pub direction: BracketDirection,
    pub br_type: BracketType,
}

#[derive(Debug, PartialEq)]
pub struct Operation {
    precedence: Precedence,
    ident: String,
    op_type: OperationType,
}

pub struct ClassifierIter<'a> {
    tokens: Iter<'a, Token>,
    expect_operator: bool,
    next: Option<&'a Token>,
    context: &'a Context,
}

// pub struct Classifier<'a>(&'a [Token]);

#[derive(Debug, PartialEq)]
pub enum Classification {
    Infix(Operation),
    Prefix(Operation),
    Postfix(Operation),
    Bracket(Bracket),
    Separator,
    Ident(String),
    Literal(i32),
}

impl<'a> Iterator for ClassifierIter<'a> {
    type Item = Result<Classification, String>;

    fn next(&mut self) -> Option<Result<Classification, String>> {
        let next = if let Some(token) = self.next {
            Some(token)
        } else {
            self.tokens.next()
        };
        self.next = None;
        match next {
            Some(token) => {
                None
            },
            None => None
        }
    }
}

pub fn classify<'a>(tokens: &'a [Token], context: &'a Context) -> ClassifierIter<'a> {
    ClassifierIter {
        tokens: tokens.iter(),
        expect_operator: false,
        next: None,
        context,
    }
}
