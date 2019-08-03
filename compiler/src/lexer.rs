//! We dont use nom because:
//! 1. we need runtime defined lexical definitions
//! 2. Need to port the lexer to chop it self
//! 

use super::tokens::Token;

pub struct Position {
    // filename: &str,
    line: u32,
    column: u32,
}

// pub struct Token {
//     pos: Position,

// }



struct LexerState<'a> {
    code: &'a str,
    // code_bytes: Vec<u8>,
    pos: usize,
}

impl<'a> LexerState<'a> {
    pub fn consume_identifier(&mut self) -> Token {
        unimplemented!();
    }

    pub fn get_char(&self) -> &str{
        &self.code[self.pos..self.pos+1]
    }

    pub fn skip_whitespaces(&mut self) {
        loop {
            match self.get_char() {
                " "|"\t"|"\n" => self.pos += 1,
                _ => break
            }
        }
        // loop {
        //     match self.code.chars().nth(self.pos).unwrap_or(b'\0') {
        //         b' '| b'\t' | b'\n' => self.pos += 1,
        //         _ => break
        //     }
        // }
    }
}

pub struct Lexer<'a> {
    code: &'a str,
}

// impl<'a> Lexer<'a> {
//     pub fn new(code: &'a str) -> Lexer {
//         Lexer {

//         }
//     }

//     pub fn tokenize(&self) -> Vec<Token> {
//         unimplemented!();
//     }
// }

pub fn tokenize(code: &str) -> Vec<Token> {
    let mut state = LexerState {
        code,
        pos: 0
    };

    match state.get_char() {
        "a"|"b"|"c"|"d"|"e"|"f"|"g"|"h"|'A'..'Z'|'_' => state.consume_identifier(),
        _ => unimplemented!()
    }

    unimplemented!();
}
