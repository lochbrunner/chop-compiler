use core::bytecode::ByteCode;
use std::cmp::{max, min};
use std::io::Write;

#[derive(Debug)]
enum StackItem {
    Int32(i32),
}

fn pop_as_int32(stack: &mut Vec<StackItem>) -> Result<i32, String> {
    match stack.pop() {
        Some(stack_item) => match stack_item {
            StackItem::Int32(v) => Ok(v),
        },
        None => Err("Not enough elements on stack.".to_string()),
    }
}

pub fn evaluate(code: &[ByteCode], writer: &mut dyn Write) -> Result<(), String> {
    let mut stack: Vec<StackItem> = Vec::new();

    let register_size = code
        .iter()
        .filter(|s| **s == ByteCode::AllocaInt32)
        .fold(0, |acc, _| acc + 1);
    let mut register: Vec<i32> = Vec::with_capacity(register_size);
    for _ in 0..register_size {
        register.push(0);
    }

    for instruction in code.iter() {
        match instruction {
            // Build ins
            ByteCode::StdOut => {
                let v = pop_as_int32(&mut stack)?;
                if let Err(error) = writeln!(writer, "{}", v) {
                    return Err(format!("Error writing to stdout: {}", error));
                }
            }
            ByteCode::Max => {
                let a = pop_as_int32(&mut stack)?;
                let b = pop_as_int32(&mut stack)?;
                stack.push(StackItem::Int32(max(a, b)))
            }
            ByteCode::Min => {
                let a = pop_as_int32(&mut stack)?;
                let b = pop_as_int32(&mut stack)?;
                stack.push(StackItem::Int32(min(a, b)))
            }
            ByteCode::PushInt32(v) => stack.push(StackItem::Int32(*v)),
            ByteCode::AddInt32 => {
                let a = pop_as_int32(&mut stack)?;
                let b = pop_as_int32(&mut stack)?;
                stack.push(StackItem::Int32(a + b))
            }
            ByteCode::SubInt32 => {
                let b = pop_as_int32(&mut stack)?;
                let a = pop_as_int32(&mut stack)?;
                stack.push(StackItem::Int32(a - b))
            }
            ByteCode::MulInt32 => {
                let b = pop_as_int32(&mut stack)?;
                let a = pop_as_int32(&mut stack)?;
                stack.push(StackItem::Int32(a * b))
            }
            ByteCode::DivInt32 => {
                let b = pop_as_int32(&mut stack)?;
                let a = pop_as_int32(&mut stack)?;
                stack.push(StackItem::Int32(a / b))
            }
            ByteCode::RemInt32 => {
                let b = pop_as_int32(&mut stack)?;
                let a = pop_as_int32(&mut stack)?;
                stack.push(StackItem::Int32(a % b))
            }
            ByteCode::StoreInt32(index) => {
                let a = pop_as_int32(&mut stack)?;
                register[*index] = a;
            }
            ByteCode::LoadInt32(index) => {
                if register.len() - 1 < *index {
                    return Err(format!("No value in register at {}", *index));
                }
                let value = register[*index];
                stack.push(StackItem::Int32(value));
            }
            ByteCode::AllocaInt32 => (),
        }
    }
    Ok(())
}

#[cfg(test)]
mod specs {
    use super::*;
    use std::io::Cursor;
    use ByteCode::*;
    #[test]
    fn milestone_1() {
        let bytecode = vec![PushInt32(42), StdOut];
        let mut stdout = Cursor::new(vec![]);
        let result = evaluate(&bytecode, &mut stdout);
        assert!(result.is_ok());
        assert_eq!(&stdout.get_ref()[0..2], b"42");
    }
    #[test]
    fn milestone_1_advanced() {
        let bytecode = vec![
            PushInt32(42),
            StdOut,
            PushInt32(35),
            StdOut,
            PushInt32(28),
            StdOut,
        ];

        let mut stdout = Cursor::new(vec![]);
        let result = evaluate(&bytecode, &mut stdout);
        assert!(result.is_ok());
        assert_eq!(&stdout.get_ref()[0..9], b"42\n35\n28\n");
    }

    #[test]
    fn operator_simple() {
        let bytecode = vec![PushInt32(3), PushInt32(5), AddInt32, StdOut];

        let mut stdout = Cursor::new(vec![]);
        let result = evaluate(&bytecode, &mut stdout);
        assert!(result.is_ok());
        assert_eq!(&stdout.get_ref()[0..2], b"8\n");
    }
}
