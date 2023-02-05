#![allow(non_snake_case)]

use core::{bytecode::ByteCode, declaration::Type};
use paste::paste;
use std::io::Write;
use stringify;

fn max<T>(a: T, b: T) -> T
where
    T: std::cmp::PartialOrd,
{
    if a > b {
        a
    } else {
        b
    }
}

fn min<T>(a: T, b: T) -> T
where
    T: std::cmp::PartialOrd,
{
    if a < b {
        a
    } else {
        b
    }
}

#[derive(Debug, Clone)]
enum StackItem {
    Int64(i64),
    Int32(i32),
    Int16(i16),
    Int8(i8),
    UInt64(u64),
    UInt32(u32),
    UInt16(u16),
    UInt8(u8),
    USize(usize),
    Float32(f32),
    Float64(f64),
}

fn pop_generic(stack: &mut Vec<StackItem>) -> Result<StackItem, String> {
    match stack.pop() {
        Some(stack_item) => Ok(stack_item),
        None => Err("Not enough elements on stack.".to_string()),
    }
}

macro_rules! pop_typed {
    ($type:ident, $type_rs:ident) => {
        paste! {
        fn [<pop_as_ $type_rs>](stack: &mut Vec<StackItem>) -> Result<$type_rs, String> {
            let stack_item = pop_generic(stack)?;
            match stack_item {
                StackItem::$type(v) => Ok(v),
                _ => Err(format!(
                    "Stack item is of type {:?} but expected {:?}.",
                    stack_item,
                    Type::$type
                )),
            }
        }
        }
    };
}

pop_typed!(Int8, i8);
pop_typed!(Int16, i16);
pop_typed!(Int32, i32);
pop_typed!(Int64, i64);
pop_typed!(UInt8, u8);
pop_typed!(UInt16, u16);
pop_typed!(UInt32, u32);
pop_typed!(UInt64, u64);
pop_typed!(USize, usize);
pop_typed!(Float32, f32);
pop_typed!(Float64, f64);

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

macro_rules! operator_t {
    ($name:ident, $op:tt, {$($long_type:ident => $rust_type:ident),*}) => {
        paste! {
            fn $name(result_type: &Type, stack: &mut Vec<StackItem>) -> Result<(), String> {
                match result_type {
                    $(Type::$long_type => {
                        let a = [<pop_as_ $rust_type>](stack)?;
                        let b = [<pop_as_ $rust_type>](stack)?;
                        stack.push(StackItem::$long_type(a $op b));
                    })*
                    _ => unreachable!(),
                }
                Ok(())
            }
        }
    };
}

macro_rules! builtin_2_t {
    ($name:ident, $op:tt, {$($long_type:ident => $rust_type:ident),*}) => {
        paste! {
            fn $name(result_type: &Type, stack: &mut Vec<StackItem>) -> Result<(), String> {
                match result_type {
                    $(Type::$long_type => {
                        let a = [<pop_as_ $rust_type>](stack)?;
                        let b = [<pop_as_ $rust_type>](stack)?;
                        stack.push(StackItem::$long_type($op(a,b)));
                    })*
                    _ => {
                        return Err(format!(
                            "[Builtin]: Function {} is not implemented for type {:?}",
                            stringify!{$ident}, result_type
                        ))
                    }
                }
                Ok(())
            }
        }
    };
}

macro_rules! store_t {
    {$($long_type:ident => $rust_type:ident),+} => {
        paste! {
            fn store(result_type: &Type, index: & usize, stack: &mut Vec<StackItem>, register: &mut Vec<StackItem>) -> Result<(), String> {
                match result_type {
                    $(Type::$long_type => {
                        let a = [<pop_as_ $rust_type>](stack)?;
                        register[*index] = StackItem::$long_type(a);
                    })+
                    _ => ()
                }
                Ok(())
            }
        }
    };
}

macro_rules! load_t {
    ($($long_type:ident),+) => {
        paste! {
            fn load(source_type: &Type, index: & usize, stack: &mut Vec<StackItem>, register: &mut Vec<StackItem>) -> Result<(), String> {
                if register.len() - 1 < *index {
                    return Err(format!("No value in register at {}", *index));
                }
                let value = &register[*index];
                match source_type {
                    $(Type::$long_type => {
                        if let StackItem::$long_type(value) = value {
                            stack.push(StackItem::$long_type(*value));
                        } else {
                            return Err(format!(
                                "Register variable has wrong type. Expected {:?} but got {:?}",
                                source_type, value
                            ));
                        }
                    })+
                    _ => {
                        return Err(format!(
                            "Loading variable of type {:?} is not implemented yet",
                            source_type
                        ))
                    }
                }
                Ok(())
            }
        }
    };
}

// macro_rules! cast_int_t {
//     {$($long_type:ident => $rust_type:ident),+} => {
//         paste! {
//             fn cast(from: &Type, to: &Type, stack: &mut Vec<StackItem>) -> Result<(), String>{
//                 match from {
//                     $($long_type => {
//                         let v = [<pop_as_ $rust_type>](&mut stack)?;
//                         match to {
//                             Type::Int8 => stack.push(StackItem::Int8(v)),
//                             Type::Int16 => stack.push(StackItem::Int16(i16::from(v))),
//                             Type::Int32 => stack.push(StackItem::Int32(i32::from(v))),
//                             Type::Int64 => stack.push(StackItem::Int64(i64::from(v))),
//                             _ => {
//                                 return Err(format!(
//                                     "Casting from {:?} to {:?} is not implemented yet!",
//                                     from, to
//                                 ));
//                             }
//                         };
//                         Ok(())
//                     })+
//                 }
//             }
//         }
//     };
// }

operator_t!(add,+, {Int8 => i8, Int16 => i16, Int32 => i32, Int64 => i64, UInt8 => u8, UInt16 => u16, UInt32 => u32, UInt64 => u64, USize => usize, Float32 => f32, Float64 => f64});
operator_t!(sub,-, {Int8 => i8, Int16 => i16, Int32 => i32, Int64 => i64, UInt8 => u8, UInt16 => u16, UInt32 => u32, UInt64 => u64, USize => usize, Float32 => f32, Float64 => f64});
operator_t!(mul,*, {Int8 => i8, Int16 => i16, Int32 => i32, Int64 => i64, UInt8 => u8, UInt16 => u16, UInt32 => u32, UInt64 => u64, USize => usize, Float32 => f32, Float64 => f64});
operator_t!(div,/, {Int8 => i8, Int16 => i16, Int32 => i32, Int64 => i64, UInt8 => u8, UInt16 => u16, UInt32 => u32, UInt64 => u64, USize => usize, Float32 => f32, Float64 => f64});
operator_t!(rem,%, {Int8 => i8, Int16 => i16, Int32 => i32, Int64 => i64, UInt8 => u8, UInt16 => u16, UInt32 => u32, UInt64 => u64, USize => usize});
builtin_2_t!(max_builtin, max, {Int8 => i8, Int16 => i16, Int32 => i32, Int64 => i64, UInt8 => u8, UInt16 => u16, UInt32 => u32, UInt64 => u64, USize => usize, Float32 => f32, Float64 => f64});
builtin_2_t!(min_builtin, min, {Int8 => i8, Int16 => i16, Int32 => i32, Int64 => i64, UInt8 => u8, UInt16 => u16, UInt32 => u32, UInt64 => u64, USize => usize, Float32 => f32, Float64 => f64});
store_t! {Int8 => i8, Int16 => i16, Int32 => i32, Int64 => i64, UInt8 => u8, UInt16 => u16, UInt32 => u32, UInt64 => u64, USize => usize, Float32 => f32, Float64 => f64}
load_t![Int8, Int16, Int32, Int64, UInt8, UInt16, UInt32, UInt64, USize, Float32, Float64];

fn cast(from: &Type, to: &Type, stack: &mut Vec<StackItem>) -> Result<(), String> {
    match from {
        Type::Int8 => {
            let v = pop_as_i8(stack)?;
            match to {
                Type::Int8 => stack.push(StackItem::Int8(v)),
                Type::Int16 => stack.push(StackItem::Int16(i16::from(v))),
                Type::Int32 => stack.push(StackItem::Int32(i32::from(v))),
                Type::Int64 => stack.push(StackItem::Int64(i64::from(v))),
                Type::UInt8 => stack.push(StackItem::UInt8(v as u8)),
                Type::UInt16 => stack.push(StackItem::UInt16(v as u16)),
                Type::UInt32 => stack.push(StackItem::UInt32(v as u32)),
                Type::UInt64 => stack.push(StackItem::UInt64(v as u64)),
                Type::USize => stack.push(StackItem::USize(v as usize)),
                _ => {
                    return Err(format!(
                        "Casting from {:?} to {:?} is not implemented yet!",
                        from, to
                    ))
                }
            }
        }
        Type::Int16 => {
            let v = pop_as_i16(stack)?;
            match to {
                Type::Int8 => stack.push(StackItem::Int8(v as i8)),
                Type::Int16 => stack.push(StackItem::Int16(v)),
                Type::Int32 => stack.push(StackItem::Int32(i32::from(v))),
                Type::Int64 => stack.push(StackItem::Int64(i64::from(v))),
                Type::UInt8 => stack.push(StackItem::UInt8(v as u8)),
                Type::UInt16 => stack.push(StackItem::UInt16(v as u16)),
                Type::UInt32 => stack.push(StackItem::UInt32(v as u32)),
                Type::UInt64 => stack.push(StackItem::UInt64(v as u64)),
                Type::USize => stack.push(StackItem::USize(v as usize)),
                _ => {
                    return Err(format!(
                        "Casting from {:?} to {:?} is not implemented yet!",
                        from, to
                    ))
                }
            }
        }
        Type::Int32 => {
            let v = pop_as_i32(stack)?;
            match to {
                Type::Int8 => stack.push(StackItem::Int8(v as i8)),
                Type::Int16 => stack.push(StackItem::Int16(v as i16)),
                Type::Int32 => stack.push(StackItem::Int32(v)),
                Type::Int64 => stack.push(StackItem::Int64(i64::from(v))),
                Type::UInt8 => stack.push(StackItem::UInt8(v as u8)),
                Type::UInt16 => stack.push(StackItem::UInt16(v as u16)),
                Type::UInt32 => stack.push(StackItem::UInt32(v as u32)),
                Type::UInt64 => stack.push(StackItem::UInt64(v as u64)),
                Type::USize => stack.push(StackItem::USize(v as usize)),
                _ => {
                    return Err(format!(
                        "Casting from {:?} to {:?} is not implemented yet!",
                        from, to
                    ))
                }
            }
        }
        Type::Int64 => {
            let v = pop_as_i64(stack)?;
            match to {
                Type::Int8 => stack.push(StackItem::Int8(v as i8)),
                Type::Int16 => stack.push(StackItem::Int16(v as i16)),
                Type::Int32 => stack.push(StackItem::Int32(v as i32)),
                Type::Int64 => stack.push(StackItem::Int64(v)),
                Type::UInt8 => stack.push(StackItem::UInt8(v as u8)),
                Type::UInt16 => stack.push(StackItem::UInt16(v as u16)),
                Type::UInt32 => stack.push(StackItem::UInt32(v as u32)),
                Type::UInt64 => stack.push(StackItem::UInt64(v as u64)),
                Type::USize => stack.push(StackItem::USize(v as usize)),
                _ => {
                    return Err(format!(
                        "Casting from {:?} to {:?} is not implemented yet!",
                        from, to
                    ))
                }
            }
        }
        Type::UInt8 => {
            let v = pop_as_u8(stack)?;
            match to {
                Type::Int8 => stack.push(StackItem::Int8(v as i8)),
                Type::Int16 => stack.push(StackItem::Int16(i16::from(v))),
                Type::Int32 => stack.push(StackItem::Int32(i32::from(v))),
                Type::Int64 => stack.push(StackItem::Int64(i64::from(v))),
                Type::UInt8 => stack.push(StackItem::UInt8(v as u8)),
                Type::UInt16 => stack.push(StackItem::UInt16(v as u16)),
                Type::UInt32 => stack.push(StackItem::UInt32(v as u32)),
                Type::UInt64 => stack.push(StackItem::UInt64(v as u64)),
                Type::USize => stack.push(StackItem::USize(v as usize)),
                _ => {
                    return Err(format!(
                        "Casting from {:?} to {:?} is not implemented yet!",
                        from, to
                    ))
                }
            }
        }
        Type::UInt16 => {
            let v = pop_as_u16(stack)?;
            match to {
                Type::Int8 => stack.push(StackItem::Int8(v as i8)),
                Type::Int16 => stack.push(StackItem::Int16(v as i16)),
                Type::Int32 => stack.push(StackItem::Int32(i32::from(v))),
                Type::Int64 => stack.push(StackItem::Int64(i64::from(v))),
                Type::UInt8 => stack.push(StackItem::UInt8(v as u8)),
                Type::UInt16 => stack.push(StackItem::UInt16(v as u16)),
                Type::UInt32 => stack.push(StackItem::UInt32(v as u32)),
                Type::UInt64 => stack.push(StackItem::UInt64(v as u64)),
                Type::USize => stack.push(StackItem::USize(v as usize)),
                _ => {
                    return Err(format!(
                        "Casting from {:?} to {:?} is not implemented yet!",
                        from, to
                    ))
                }
            }
        }
        Type::UInt32 => {
            let v = pop_as_u32(stack)?;
            match to {
                Type::Int8 => stack.push(StackItem::Int8(v as i8)),
                Type::Int16 => stack.push(StackItem::Int16(v as i16)),
                Type::Int32 => stack.push(StackItem::Int32(v as i32)),
                Type::Int64 => stack.push(StackItem::Int64(i64::from(v))),
                Type::UInt8 => stack.push(StackItem::UInt8(v as u8)),
                Type::UInt16 => stack.push(StackItem::UInt16(v as u16)),
                Type::UInt32 => stack.push(StackItem::UInt32(v as u32)),
                Type::UInt64 => stack.push(StackItem::UInt64(v as u64)),
                Type::USize => stack.push(StackItem::USize(v as usize)),
                _ => {
                    return Err(format!(
                        "Casting from {:?} to {:?} is not implemented yet!",
                        from, to
                    ))
                }
            }
        }
        Type::UInt64 => {
            let v = pop_as_u64(stack)?;
            match to {
                Type::Int8 => stack.push(StackItem::Int8(v as i8)),
                Type::Int16 => stack.push(StackItem::Int16(v as i16)),
                Type::Int32 => stack.push(StackItem::Int32(v as i32)),
                Type::Int64 => stack.push(StackItem::Int64(v as i64)),
                Type::UInt8 => stack.push(StackItem::UInt8(v as u8)),
                Type::UInt16 => stack.push(StackItem::UInt16(v as u16)),
                Type::UInt32 => stack.push(StackItem::UInt32(v as u32)),
                Type::UInt64 => stack.push(StackItem::UInt64(v as u64)),
                Type::USize => stack.push(StackItem::USize(v as usize)),
                _ => {
                    return Err(format!(
                        "Casting from {:?} to {:?} is not implemented yet!",
                        from, to
                    ))
                }
            }
        }
        Type::USize => {
            let v = pop_as_usize(stack)?;
            match to {
                Type::Int8 => stack.push(StackItem::Int8(v as i8)),
                Type::Int16 => stack.push(StackItem::Int16(v as i16)),
                Type::Int32 => stack.push(StackItem::Int32(v as i32)),
                Type::Int64 => stack.push(StackItem::Int64(v as i64)),
                Type::UInt8 => stack.push(StackItem::UInt8(v as u8)),
                Type::UInt16 => stack.push(StackItem::UInt16(v as u16)),
                Type::UInt32 => stack.push(StackItem::UInt32(v as u32)),
                Type::UInt64 => stack.push(StackItem::UInt64(v as u64)),
                Type::USize => stack.push(StackItem::USize(v as usize)),
                _ => {
                    return Err(format!(
                        "Casting from {:?} to {:?} is not implemented yet!",
                        from, to
                    ))
                }
            }
        }
        Type::Float32 => {
            let v = pop_as_f32(stack)?;
            match to {
                Type::Float64 => stack.push(StackItem::Float64(v as f64)),
                _ => {
                    return Err(format!(
                        "Casting from {:?} to {:?} is not implemented yet!",
                        from, to
                    ))
                }
            }
        }
        Type::Float64 => {
            let v = pop_as_f64(stack)?;
            match to {
                Type::Float32 => stack.push(StackItem::Float32(v as f32)),
                _ => {
                    return Err(format!(
                        "Casting from {:?} to {:?} is not implemented yet!",
                        from, to
                    ))
                }
            }
        }
        _ => return Err(format!("Casting from {:?} is not implemented yet!", from)),
    }
    Ok(())
}
// cast_int_t! {Int8 => i8, Int16 => i16, Int32 => i32, Int64 => i64}

pub fn evaluate(code: &[ByteCode], writer: &mut dyn Write) -> Result<(), String> {
    let mut stack: Vec<StackItem> = Vec::new();

    let mut register: Vec<StackItem> = Vec::new();
    for alloca in code.iter() {
        if let ByteCode::Alloca(t) = alloca {
            match t {
                Type::Float64 => register.push(StackItem::Float64(0.)),
                Type::Float32 => register.push(StackItem::Float32(0.)),
                Type::Int64 => register.push(StackItem::Int64(0)),
                Type::Int32 => register.push(StackItem::Int32(0)),
                Type::Int16 => register.push(StackItem::Int16(0)),
                Type::Int8 => register.push(StackItem::Int8(0)),
                Type::UInt64 => register.push(StackItem::UInt64(0)),
                Type::UInt32 => register.push(StackItem::UInt32(0)),
                Type::UInt16 => register.push(StackItem::UInt16(0)),
                Type::UInt8 => register.push(StackItem::UInt8(0)),
                Type::USize => register.push(StackItem::USize(0)),
                Type::Void | Type::Type => (),
            }
        }
    }

    for instruction in code.iter() {
        match instruction {
            // Build ins
            ByteCode::StdOut(_) => {
                let v = pop_generic(&mut stack)?;
                let s = match v {
                    StackItem::Int8(v) => v.to_string(),
                    StackItem::Int16(v) => v.to_string(),
                    StackItem::Int32(v) => v.to_string(),
                    StackItem::Int64(v) => v.to_string(),
                    StackItem::UInt8(v) => v.to_string(),
                    StackItem::UInt16(v) => v.to_string(),
                    StackItem::UInt32(v) => v.to_string(),
                    StackItem::UInt64(v) => v.to_string(),
                    StackItem::USize(v) => v.to_string(),
                    StackItem::Float32(v) => v.to_string(),
                    StackItem::Float64(v) => v.to_string(),
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
                        max_builtin(return_type, &mut stack)?;
                    }
                    "min" => {
                        check_types_equal_3(return_type, a_type, b_type)?;
                        min_builtin(return_type, &mut stack)?;
                    }
                    _ => return Err(format!("Unknown function {}", ident)),
                }
            }
            ByteCode::PushInt8(v) => stack.push(StackItem::Int8(*v)),
            ByteCode::PushInt16(v) => stack.push(StackItem::Int16(*v)),
            ByteCode::PushInt32(v) => stack.push(StackItem::Int32(*v)),
            ByteCode::PushInt64(v) => stack.push(StackItem::Int64(*v)),
            ByteCode::PushUInt8(v) => stack.push(StackItem::UInt8(*v)),
            ByteCode::PushUInt16(v) => stack.push(StackItem::UInt16(*v)),
            ByteCode::PushUInt32(v) => stack.push(StackItem::UInt32(*v)),
            ByteCode::PushUInt64(v) => stack.push(StackItem::UInt64(*v)),
            ByteCode::PushUSize(v) => stack.push(StackItem::USize(*v)),
            ByteCode::PushFloat32(v) => stack.push(StackItem::Float32(*v)),
            ByteCode::PushFloat64(v) => stack.push(StackItem::Float64(*v)),
            ByteCode::Add(dtype) => add(dtype, &mut stack)?,
            ByteCode::Sub(dtype) => sub(dtype, &mut stack)?,
            ByteCode::Mul(dtype) => mul(dtype, &mut stack)?,
            ByteCode::Div(dtype) => div(dtype, &mut stack)?,
            ByteCode::Rem(dtype) => rem(dtype, &mut stack)?,
            ByteCode::Store(dtype, index) => store(dtype, index, &mut stack, &mut register)?,
            ByteCode::Load(source_type, index) => {
                load(source_type, index, &mut stack, &mut register)?
            }
            ByteCode::Alloca(_) => (),
            ByteCode::CastInt(from, to) => cast(from, to, &mut stack)?,
            // _ => return Err(format!("Illegal instruction {:?}", instruction)),
        }
    }
    Ok(())
}

#[cfg(test)]
mod specs {
    #![macro_use]
    macro_rules! assert_ok(
        ($result:expr) => (assert!($result.is_ok(), "Not ok: {:?}", $result.unwrap_err()));
    );
    use super::*;
    use std::io::Cursor;
    use ByteCode::*;
    #[test]
    fn milestone_1() {
        let bytecode = vec![PushInt32(42), StdOut(Type::Int32)];
        let mut stdout = Cursor::new(vec![]);
        let result = evaluate(&bytecode, &mut stdout);
        assert_ok!(result);
        assert_eq!(&stdout.get_ref()[0..2], b"42");
    }
    #[test]
    fn milestone_1_advanced() {
        let bytecode = vec![
            PushInt32(42),
            StdOut(Type::Int32),
            PushInt32(35),
            StdOut(Type::Int32),
            PushInt32(28),
            StdOut(Type::Int32),
        ];

        let mut stdout = Cursor::new(vec![]);
        let result = evaluate(&bytecode, &mut stdout);
        assert_ok!(result);
        assert_eq!(&stdout.get_ref()[0..9], b"42\n35\n28\n");
    }

    #[test]
    fn operator_simple() {
        let bytecode = vec![
            PushInt32(3),
            PushInt32(5),
            Add(Type::Int32),
            StdOut(Type::Int32),
        ];

        let mut stdout = Cursor::new(vec![]);
        let result = evaluate(&bytecode, &mut stdout);
        assert_ok!(result);
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
            StdOut(Type::Int8),
        ];

        let mut stdout = Cursor::new(vec![]);

        let result = evaluate(&bytecode, &mut stdout);

        assert_ok!(result);
    }
}
