extern crate clap;
extern crate core;
mod link;
mod llvm;

#[macro_use]
extern crate maplit;

use clap::{App, Arg};
use std::fs;
use std::path::Path;

fn run(input: &str, output: &str, emit_llvm: bool) -> Result<(), ()> {
    let wd = "./build";
    if let Err(msg) = fs::create_dir_all(wd) {
        eprintln!("Could not create directory: {}", msg);
        return Err(());
    }
    let file_stem = Path::new(output).file_stem().unwrap().to_str().unwrap();
    let llvm_file = if emit_llvm {
        output.to_owned()
    } else {
        format!("{}/{}.ll", wd, file_stem)
    };

    match fs::read_to_string(input) {
        Ok(code) => match core::build(&code) {
            Err(error) => {
                error.print(input);
                Err(())
            }
            Ok(bytecode) => match llvm::export(&bytecode, input) {
                Ok(code) => match fs::write(&llvm_file, code) {
                    Ok(_) => {
                        if emit_llvm {
                            Ok(())
                        } else {
                            match link::link(&llvm_file, output, wd, file_stem) {
                                Ok(_) => Ok(()),
                                Err(msg) => {
                                    eprintln!(
                                        "Could not link to file {} to {}: {}",
                                        llvm_file, output, msg
                                    );
                                    Err(())
                                }
                            }
                        }
                    }
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
        .arg(
            Arg::with_name("emit-llvm")
                .long("--emit-llvm")
                .help("Dumps LLVM code."),
        )
        .get_matches();

    let input = matches
        .value_of("input")
        .expect("Input filename parameter given");
    let output = matches
        .value_of("output")
        .expect("Output filename parameter given");
    let emit_llvm = matches.occurrences_of("emit-llvm") > 0;

    ::std::process::exit(match run(input, output, emit_llvm) {
        Ok(_) => 0,
        Err(_) => 1,
    });
}
