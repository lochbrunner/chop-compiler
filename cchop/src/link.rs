use std::process::Command;

pub fn link(input: &str, output: &str, wd: &str, file_stem: &str) -> Result<(), String> {
    let object_file = format!("{}/{}.s", wd, file_stem);
    match Command::new("llc")
        .args(&[input, "-o", &object_file])
        .output()
    {
        Ok(_) => (),
        Err(msg) => return Err(msg.to_string()),
    }

    match Command::new("gcc")
        .args(&[&object_file, "-o", output])
        .output()
    {
        Ok(_) => Ok(()),
        Err(e) => match e.kind() {
            std::io::ErrorKind::NotFound => Err(
                "Can not find llc.\nYou need to install the LLVM tools.\nSee https://apt.llvm.org"
                    .to_owned(),
            ),
            _ => Err(e.to_string()),
        },
    }
}
