use core::{bytecode::ByteCode, declaration::Type};
use std::cmp::{max, min};
use std::io::Write;

#[derive(Debug, Clone)]
enum StackItem {
    Int64(i64),
    Int32(i32),
    Int16(i16),
    Int8(i8),
    Float(i64),
}

fn pop_generic(stack: &mut Vec<StackItem>) -> Result<StackItem, String> {
    match stack.pop() {
        Some(stack_item) => Ok(stack_item),
        None => Err("Not enough elements on stack.".to_string()),
    }
}

fn pop_as_int8(stack: &mut Vec<StackItem>) -> Result<i8, String> {
    let stack_item = pop_generic(stack)?;
    match stack_item {
        StackItem::Int8(v) => Ok(v),
        _ => Err(format!(
            "Stack item is of type {:?} but expected {:?}.",
            stack_item,
            Type::Int8
        )),
    }
}

fn pop_as_int16(stack: &mut Vec<StackItem>) -> Result<i16, String> {
    let stack_item = pop_generic(stack)?;
    match stack_item {
        StackItem::Int16(v) => Ok(v),
        _ => Err(format!(
            "Stack item is of type {:?} but expected {:?}.",
            stack_item,
            Type::Int16
        )),
    }
}

fn pop_as_int32(stack: &mut Vec<StackItem>) -> Result<i32, String> {
    let stack_item = pop_generic(stack)?;
    match stack_item {
        StackItem::Int32(v) => Ok(v),
        _ => Err(format!(
            "Stack item is of type {:?} but expected {:?}.",
            stack_item,
            Type::Int32
        )),
    }
}

fn pop_as_int64(stack: &mut Vec<StackItem>) -> Result<i64, String> {
    let stack_item = pop_generic(stack)?;
    match stack_item {
        StackItem::Int64(v) => Ok(v),
        _ => Err(format!(
            "Stack item is of type {:?} but expected {:?}.",
            stack_item,
            Type::Int64
        )),
    }
}

fn check_types_equal_3(r: &Type, a: &Type, b: &Type) -> Result<(), String> {
    if r != a || r != b {
        Err(format!(
            "Return type {:?} and argument types {:?} {:?} differ.",
            r, a, b
        ))
    } else {
        Ok(())
    }
}

pub fn evaluate(code: &[ByteCode], writer: &mut dyn Write) -> Result<(), String> {
    let mut stack: Vec<StackItem> = Vec::new();

    let mut register: Vec<StackItem> = Vec::new();
    for alloca in code.iter() {
        if let ByteCode::Alloca(t) = alloca {
            match t {
                Type::Int64 => register.push(StackItem::Int64(0)),
                Type::Int32 => register.push(StackItem::Int32(0)),
                Type::Int16 => register.push(StackItem::Int16(0)),
                Type::Int8 => register.push(StackItem::Int8(0)),
                Type::Void | Type::Type => (),
            }
        }
    }

    for instruction in code.iter() {
        match instruction {
            // Build ins
            ByteCode::StdOut => {
                let v = pop_generic(&mut stack)?;
                let s = match v {
                    StackItem::Int8(v) => v.to_string(),
                    StackItem::Int16(v) => v.to_string(),
                    StackItem::Int32(v) => v.to_string(),
                    StackItem::Int64(v) => v.to_string(),
                    _ => return Err(format!("Type {:?} is not implemented yet!", v)),
                };
                if let Err(error) = writeln!(writer, "{}", s) {
                    return Err(format!("Error writing to stdout: {}", error));
                }
            }
            ByteCode::Call2(ident, return_type, a_type, b_type) => {
                let ident = ident as &str;
                match ident {
                    "max" => {
                        check_types_equal_3(return_type, a_type, b_type)?;
                        match return_type {
                            Type::Int32 => {
                                let a = pop_as_int32(&mut stack)?;
                                let b = pop_as_int32(&mut stack)?;
                                stack.push(StackItem::Int32(max(a, b)))
                            }
                            Type::Int8 => {
                                let a = pop_as_int8(&mut stack)?;
                                let b = pop_as_int8(&mut stack)?;
                                stack.push(StackItem::Int8(max(a, b)))
                            }
                            _ => {
                                return Err(format!(
                                    "Function {} is not implemented for type {:?}",
                                    ident, return_type
                                ))
                            }
                        }
                    }
                    "min" => {
                        check_types_equal_3(return_type, a_type, b_type)?;
                        match return_type {
                            Type::Int32 => {
                                let a = pop_as_int32(&mut stack)?;
                                let b = pop_as_int32(&mut stack)?;
                                stack.push(StackItem::Int32(min(a, b)))
                            }
                            Type::Int8 => {
                                let a = pop_as_int8(&mut stack)?;
                                let b = pop_as_int8(&mut stack)?;
                                stack.push(StackItem::Int8(min(a, b)))
                            }
                            _ => {
                                return Err(format!(
                                    "Function {} is not implemented for type {:?}",
                                    ident, return_type
                                ))
                            }
                        }
                    }
                    _ => return Err(format!("Unknown function {}", ident)),
                }
            }
            ByteCode::PushInt32(v) => stack.push(StackItem::Int32(*v)),
            ByteCode::Add(Type::Int8) => {
                let a = pop_as_int8(&mut stack)?;
                let b = pop_as_int8(&mut stack)?;
                stack.push(StackItem::Int8(a + b))
            }
            ByteCode::Add(Type::Int32) => {
                let a = pop_as_int32(&mut stack)?;
                let b = pop_as_int32(&mut stack)?;
                stack.push(StackItem::Int32(a + b))
            }
            ByteCode::Sub(Type::Int32) => {
                let b = pop_as_int32(&mut stack)?;
                let a = pop_as_int32(&mut stack)?;
                stack.push(StackItem::Int32(a - b))
            }
            ByteCode::Mul(Type::Int32) => {
                let b = pop_as_int32(&mut stack)?;
                let a = pop_as_int32(&mut stack)?;
                stack.push(StackItem::Int32(a * b))
            }
            ByteCode::Div(Type::Int32) => {
                let b = pop_as_int32(&mut stack)?;
                let a = pop_as_int32(&mut stack)?;
                stack.push(StackItem::Int32(a / b))
            }
            ByteCode::Rem(Type::Int32) => {
                let b = pop_as_int32(&mut stack)?;
                let a = pop_as_int32(&mut stack)?;
                stack.push(StackItem::Int32(a % b))
            }
            ByteCode::Store(Type::Int8, index) => {
                let a = pop_as_int8(&mut stack)?;
                register[*index] = StackItem::Int8(a);
            }
            ByteCode::Store(Type::Int32, index) => {
                let a = pop_as_int32(&mut stack)?;
                register[*index] = StackItem::Int32(a);
            }
            ByteCode::Load(source_type, index) => {
                if register.len() - 1 < *index {
                    return Err(format!("No value in register at {}", *index));
                }
                let value = &register[*index];
                match source_type {
                    Type::Int32 => {
                        if let StackItem::Int32(value) = value {
                            stack.push(StackItem::Int32(*value));
                        } else {
                            return Err(format!(
                                "Register variable has wrong type. Expected {:?} but got {:?}",
                                source_type, value
                            ));
                        }
                    }
                    Type::Int8 => {
                        if let StackItem::Int8(value) = value {
                            stack.push(StackItem::Int8(*value));
                        } else {
                            return Err(format!(
                                "Register variable has wrong type. Expected {:?} but got {:?}",
                                source_type, value
                            ));
                        }
                    }
                    _ => {
                        return Err(format!(
                            "Loading variable of type {:?} is not implemented yet",
                            source_type
                        ))
                    }
                }
            }
            ByteCode::Alloca(_) => (),
            ByteCode::CastInt(from, to) => match from {
                Type::Int8 => {
                    let v = pop_as_int8(&mut stack)?;
                    match to {
                        Type::Int8 => stack.push(StackItem::Int8(v)),
                        Type::Int16 => stack.push(StackItem::Int16(i16::from(v))),
                        Type::Int32 => stack.push(StackItem::Int32(i32::from(v))),
                        Type::Int64 => stack.push(StackItem::Int64(i64::from(v))),
                        _ => {
                            return Err(format!(
                                "Casting from {:?} to {:?} is not implemented yet!",
                                from, to
                            ))
                        }
                    }
                }
                Type::Int16 => {
                    let v = pop_as_int16(&mut stack)?;
                    match to {
                        Type::Int8 => stack.push(StackItem::Int8(v as i8)),
                        Type::Int16 => stack.push(StackItem::Int16(v)),
                        Type::Int32 => stack.push(StackItem::Int32(i32::from(v))),
                        Type::Int64 => stack.push(StackItem::Int64(i64::from(v))),
                        _ => {
                            return Err(format!(
                                "Casting from {:?} to {:?} is not implemented yet!",
                                from, to
                            ))
                        }
                    }
                }
                Type::Int32 => {
                    let v = pop_as_int32(&mut stack)?;
                    match to {
                        Type::Int8 => stack.push(StackItem::Int8(v as i8)),
                        Type::Int16 => stack.push(StackItem::Int16(v as i16)),
                        Type::Int32 => stack.push(StackItem::Int32(v)),
                        Type::Int64 => stack.push(StackItem::Int64(i64::from(v))),
                        _ => {
                            return Err(format!(
                                "Casting from {:?} to {:?} is not implemented yet!",
                                from, to
                            ))
                        }
                    }
                }
                Type::Int64 => {
                    let v = pop_as_int64(&mut stack)?;
                    match to {
                        Type::Int8 => stack.push(StackItem::Int8(v as i8)),
                        Type::Int16 => stack.push(StackItem::Int16(v as i16)),
                        Type::Int32 => stack.push(StackItem::Int32(v as i32)),
                        Type::Int64 => stack.push(StackItem::Int64(v)),
                        _ => {
                            return Err(format!(
                                "Casting from {:?} to {:?} is not implemented yet!",
                                from, to
                            ))
                        }
                    }
                }
                _ => return Err(format!("Casting from {:?} is not implemented yet!", from)),
            },
            _ => return Err(format!("Illegal instruction {:?}", instruction)),
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
        let bytecode = vec![PushInt32(3), PushInt32(5), Add(Type::Int32), StdOut];

        let mut stdout = Cursor::new(vec![]);
        let result = evaluate(&bytecode, &mut stdout);
        assert!(result.is_ok());
        assert_eq!(&stdout.get_ref()[0..2], b"8\n");
    }

    #[test]
    fn milestone_5_main() {
        let bytecode = vec![
            Alloca(Type::Int32),
            PushInt32(0),
            Store(Type::Int32, 0),
            PushInt32(3),
            Alloca(Type::Int32),
            Store(Type::Int32, 1),
            Load(Type::Int32, 1),
            CastInt(Type::Int32, Type::Int8),
            PushInt32(5),
            CastInt(Type::Int32, Type::Int8),
            ByteCode::Add(Type::Int8),
            Alloca(Type::Int8),
            Store(Type::Int8, 2),
            PushInt32(7),
            CastInt(Type::Int32, Type::Int8),
            Alloca(Type::Int8),
            Store(Type::Int8, 3),
            Load(Type::Int8, 2),
            Load(Type::Int8, 3),
            Call2("max".to_string(), Type::Int8, Type::Int8, Type::Int8),
            StdOut,
        ];

        let mut stdout = Cursor::new(vec![]);

        let result = evaluate(&bytecode, &mut stdout);

        if let Err(error) = result {
            println!("{}", error);
        }

        // assert!(result.is_ok());
    }
}
