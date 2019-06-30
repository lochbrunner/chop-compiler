use std::fs::File;
use std::io::{BufWriter, Write};
use std::process::Command;
use std::str;

fn write_llvm<W>(writer: &mut W) -> std::io::Result<()>
where
    W: Write,
{
    writer
        .write_all("@.str = internal constant [14 x i8] c\"hello, world\\0A\\00\"\n".as_bytes())?;
    writer.write_all("declare i32 @printf(i8*, ...)\n".as_bytes())?;
    writer.write_all("define i32 @main(i32 %argc, i8** %argv) nounwind {\n".as_bytes())?;
    writer.write_all("entry:\n".as_bytes())?;
    writer.write_all(
        "  %tmp1 = getelementptr [14 x i8], [14 x i8]* @.str, i32 0, i32 0\n".as_bytes(),
    )?;
    writer.write_all("  %tmp2 = call i32 (i8*, ...) @printf( i8* %tmp1 ) nounwind\n".as_bytes())?;
    writer.write_all("  ret i32 0\n".as_bytes())?;
    writer.write_all("}\n".as_bytes())
}

fn llvm_ir_to_binary(name: &str) {
    // let out = Command::new("llc")
    //     .arg("--version")
    //     .output()
    //     .expect("failed to execute process");
    // print!("env.err: {}", str::from_utf8(&out.stderr).unwrap());
    // print!("env.out: {}", str::from_utf8(&out.stdout).unwrap());
    let out = Command::new("/usr/lib/llvm-8/bin/llc")
        .env_clear()
        .arg(format!("{}.bc", name))
        .arg("-o")
        .arg(format!("{}.s", name))
        .arg("-filetype=asm")
        .output()
        .expect("failed to execute process");
    print!("llc.err: {}", str::from_utf8(&out.stderr).unwrap());
    print!("llc.out: {}", str::from_utf8(&out.stdout).unwrap());
    let out = Command::new("gcc")
        .arg(format!("{}.s", name))
        .arg("-no-pie")
        .arg("-o")
        .arg(name)
        // .env_clear()
        // .env("PATH", "/home/matthias/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/snap/bin:/home/matthias/.local/bin")
        .output()
        .expect("failed to execute process");
    print!("gcc.err: {}", str::from_utf8(&out.stderr).unwrap());
    print!("gcc.out: {}", str::from_utf8(&out.stdout).unwrap());
}

fn main() {
    let name = "text";
    let file = File::create(format!("{}.bc", name)).expect("Unable to create file");
    let mut writer = BufWriter::new(file);
    write_llvm(&mut writer).expect("Unable to write data");
    llvm_ir_to_binary(name);
}
