mod evaluation;

extern crate clap;
extern crate core;

extern crate maplit;

use clap::{App, Arg};
use std::fs;
use std::io;

fn run(filename: &str) -> Result<(), ()> {
    match fs::read_to_string(filename) {
        Ok(code) => match core::build(&code) {
            Err(error) => {
                error.print(filename);
                if let Some(line) = code.lines().nth(error.location.line as usize - 1) {
                    eprintln!("{}", line);
                }
                Err(())
            }
            Ok(bytecode) => {
                if let Err(msg) = evaluation::evaluate(&bytecode, &mut io::stdout()) {
                    eprintln!("Runtime Error: {}", msg);
                    Err(())
                } else {
                    Ok(())
                }
            }
        },
        Err(msg) => {
            eprintln!("Could not open file {}: {}", filename, msg);
            Err(())
        }
    }
}

fn main() {
    let matches = App::new("Chop interpreter")
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

    ::std::process::exit(match run(filename) {
        Ok(_) => 0,
        Err(_) => 1,
    });
}
