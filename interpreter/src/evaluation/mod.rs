pub mod bytecode;

use bytecode::ByteCode;
use std::io::Write;

#[derive(Debug)]
enum StackItem {
    Int32(i32),
}

pub fn evaluate(code: &[ByteCode], writer: &mut dyn Write) -> Result<(), String> {
    let mut stack: Vec<StackItem> = Vec::new();
    for instruction in code.iter() {
        match instruction {
            ByteCode::StdOut => match stack.pop() {
                Some(stack_item) => match stack_item {
                    StackItem::Int32(v) => {
                        if let Err(error) = writeln!(writer, "{}", v) {
                            return Err(format!("Error writing to stdout: {}", error));
                        }
                    }
                },
                None => return Err("Function stdout expects one argument.".to_string()),
            },
            ByteCode::PushInt32(v) => stack.push(StackItem::Int32(*v)),
        }
    }
    Ok(())
}

#[cfg(test)]
mod specs {
    use super::*;
    use std::io::Cursor;
    #[test]
    fn milestone_1() {
        let bytecode = vec![ByteCode::PushInt32(42), ByteCode::StdOut];
        let mut stdout = Cursor::new(vec![]);
        let result = evaluate(&bytecode, &mut stdout);
        assert!(result.is_ok());
        assert_eq!(&stdout.get_ref()[0..2], b"42");
    }
}
