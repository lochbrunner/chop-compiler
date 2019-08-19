mod compiler;
mod evaluation;

extern crate clap;
extern crate nom_locate;

#[macro_use]
extern crate maplit;

#[cfg(test)]
#[macro_use]
extern crate p_macro;

use clap::{App, Arg};
use std::fs;
use std::io;

fn main() {
    let matches = App::new("Sample data generator")
        .version("0.0.1")
        .author("Matthias Lochbrunner <matthias_lochbrunner@web.de>")
        .arg(
            Arg::with_name("filename")
                .help("filename containing the source code")
                .required(true)
                .index(1),
        )
        .get_matches();

    let filename = matches
        .value_of("filename")
        .expect("Filename parameter given");

    let code = fs::read_to_string(filename).expect("Something went wrong reading the file");
    match compiler::compile(&code, filename) {
        Err(error) => error.print(filename),
        Ok(bytecode) => {
            if let Err(msg) = evaluation::evaluate(&bytecode, &mut io::stdout()) {
                println!("Runtime Error: {}", msg);
            }
        }
    };
}
