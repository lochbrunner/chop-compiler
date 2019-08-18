#[derive(PartialEq, Debug)]
pub enum ByteCode {
    StdOut, // For now hard-coded
    PushInt32(i32),
}
