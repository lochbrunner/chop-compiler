mod compiler;

extern crate nom_locate;

#[cfg(test)]
#[macro_use]
extern crate p_macro;

fn main() {
    let a = compiler::lexer::lex(&":=");
    println!("Tokens: {:?}", a);
}
