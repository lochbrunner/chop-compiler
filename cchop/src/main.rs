extern crate clap;
extern crate core;
mod link;

use clap::{App, Arg};
use core::llvm;
use std::fs;
use std::path::Path;

fn run(input: &str, output: &str) -> Result<(), ()> {
    let wd = "./build";
    if let Err(msg) = fs::create_dir_all(wd) {
        eprintln!("Could not create directory: {}", msg);
        return Err(());
    }
    let file_stem = Path::new(output).file_stem().unwrap().to_str().unwrap();
    let llvm_file = format!("{}/{}.ll", wd, file_stem);

    match fs::read_to_string(input) {
        Ok(code) => match core::compile(&code, input) {
            Err(error) => {
                error.print(input);
                Err(())
            }
            Ok(bytecode) => match llvm::export(&bytecode, input) {
                Ok(code) => match fs::write(&llvm_file, code) {
                    Ok(_) => match link::link(&llvm_file, output, wd, file_stem) {
                        Ok(_) => Ok(()),
                        Err(msg) => {
                            eprintln!("Could not link to file {}: {}", output, msg);
                            Err(())
                        }
                    },
                    Err(msg) => {
                        eprintln!("Could not write to file {}: {}", output, msg);
                        Err(())
                    }
                },
                Err(error) => {
                    error.print(input);
                    Err(())
                }
            },
        },
        Err(msg) => {
            eprintln!("Could not open file {}: {}", input, msg);
            Err(())
        }
    }
}

fn main() {
    let matches = App::new("Chop compiler")
        .version("0.0.1")
        .author("Matthias Lochbrunner <matthias_lochbrunner@web.de>")
        .arg(
            Arg::with_name("input")
                .help("filename containing the source code")
                .required(true)
                .index(1),
        )
        .arg(
            Arg::with_name("output")
                .short("o")
                .long("output")
                .help("output filename")
                .takes_value(true),
        )
        .get_matches();

    let input = matches
        .value_of("input")
        .expect("Input filename parameter given");
    let output = matches
        .value_of("output")
        .expect("Output filename parameter given");

    ::std::process::exit(match run(input, output) {
        Ok(_) => 0,
        Err(_) => 1,
    });
}
