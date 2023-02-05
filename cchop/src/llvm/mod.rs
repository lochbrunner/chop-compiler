use std::collections::HashMap;
use std::fmt;

use core::{
    declaration::{Signature, Type},
    ByteCode, CompilerError,
};

mod buildins;

fn write_header(source_filename: &str, code: &mut String) {
    code.push_str(&format!("; ModuleID = '{}\n", source_filename));
    code.push_str(&format!("source_filename = \"{}\"\n", source_filename));
    code.push_str("target datalayout = \"e-m:e-i64:64-f80:128-n8:16:32:64-S128\"\n");
    code.push_str("target triple = \"x86_64-pc-linux-gnu\"\n");
}

fn write_empty_line(code: &mut String) {
    code.push_str("\n");
}

fn write_format_string(code: &mut String) {
    code.push_str("@.str.i = private unnamed_addr constant [4 x i8] c\"%i\\0A\\00\", align 1\n");
    code.push_str("@.str.g = private unnamed_addr constant [4 x i8] c\"%g\\0A\\00\", align 1\n");
    code.push_str("@.str.u = private unnamed_addr constant [4 x i8] c\"%u\\0A\\00\", align 1\n");
}

fn write_printf_declaration(code: &mut String) {
    code.push_str("declare dso_local i32 @printf(i8*, ...) #1\n");
}

fn write_footer(code: &mut String) {
    code.push_str("!llvm.module.flags = !{!0}\n");
    code.push_str("!llvm.ident = !{!1}\n");
    code.push_str("\n");
    code.push_str("!0 = !{i32 1, !\"wchar_size\", i32 4}\n");
    // TODO: put our selves in this?
    code.push_str("!1 = !{!\"cchop version 0.0.1\"}\n");
}

fn write_attribute(index: u32, attr: HashMap<&str, &str>, code: &mut String) {
    code.push_str(&format!("attributes #{} = {{ ", index));
    for (k, v) in attr.iter() {
        if k.contains('-') {
            code.push('\"');
            code.push_str(k);
            code.push('\"');
        } else {
            code.push_str(k);
        }
        code.push(' ');
        if v != &"" {
            code.push_str("=\"");
            code.push_str(v);
            code.push_str("\" ");
        }
    }
    code.push_str("}\n");
}

#[derive(Debug)]
/// Same as in evaluation
enum StackItem {
    Float64(f64),
    Float32(f32),
    Int64(i64),
    Int32(i32),
    Int16(i16),
    Int8(i8),
    UInt64(u64),
    UInt32(u32),
    UInt16(u16),
    UInt8(u8),
    USize(usize),
    Ref(usize),
}

fn stack_item_to_type(item: &StackItem) -> Option<Type> {
    match item {
        StackItem::Float64(_) => Some(Type::Float64),
        StackItem::Float32(_) => Some(Type::Float32),
        StackItem::Int64(_) => Some(Type::Int64),
        StackItem::Int32(_) => Some(Type::Int32),
        StackItem::Int16(_) => Some(Type::Int16),
        StackItem::Int8(_) => Some(Type::Int8),
        StackItem::UInt64(_) => Some(Type::UInt64),
        StackItem::UInt32(_) => Some(Type::UInt32),
        StackItem::UInt16(_) => Some(Type::UInt16),
        StackItem::UInt8(_) => Some(Type::UInt8),
        StackItem::USize(_) => Some(Type::USize),
        StackItem::Ref(_) => None,
    }
}

fn store<T>(index: usize, value: T, v_type: &Type, code: &mut String)
where
    T: fmt::Display,
{
    code.push_str(&format!(
        "  store {} {}, {}* %{}, align {}\n",
        v_type.to_llvm(),
        value,
        v_type.to_llvm(),
        index,
        v_type.align(),
    ));
}

fn asserted_pop(
    expected_type: &Type,
    stack: &mut Vec<StackItem>,
) -> Result<StackItem, CompilerError> {
    if let Some(item) = stack.pop() {
        if let Some(actual_type) = stack_item_to_type(&item) {
            if actual_type == *expected_type {
                Ok(item)
            } else {
                Err(CompilerError::global(&format!(
                    "Expected stack item of type {:?}, but got {:?}",
                    expected_type, actual_type
                )))
            }
        } else {
            Ok(item)
        }
    } else {
        Err(CompilerError::global("Missing argument on stack"))
    }
}

fn get_last_item_rep_any(stack: &mut Vec<StackItem>) -> Result<String, CompilerError> {
    match stack.pop() {
        None => Err(CompilerError::global("Missing argument on stack")),
        Some(item) => match item {
            StackItem::Ref(r) => Ok(format!("%{}", r)),
            StackItem::Int8(v) => Ok(v.to_string()),
            StackItem::Int16(v) => Ok(v.to_string()),
            StackItem::Int32(v) => Ok(v.to_string()),
            StackItem::Int64(v) => Ok(v.to_string()),
            StackItem::UInt8(v) => Ok(v.to_string()),
            StackItem::UInt16(v) => Ok(v.to_string()),
            StackItem::UInt32(v) => Ok(v.to_string()),
            StackItem::UInt64(v) => Ok(v.to_string()),
            StackItem::USize(v) => Ok(v.to_string()),
            StackItem::Float32(v) => Ok(format!("{:.6e}", v)),
            StackItem::Float64(v) => Ok(format!("{:.6e}", v)),
        },
    }
}

fn get_last_item_rep_checked(
    expected_type: &Type,
    stack: &mut Vec<StackItem>,
) -> Result<String, CompilerError> {
    match asserted_pop(expected_type, stack)? {
        StackItem::Ref(r) => Ok(format!("%{}", r)),
        StackItem::Int8(v) => Ok(v.to_string()),
        StackItem::Int16(v) => Ok(v.to_string()),
        StackItem::Int32(v) => Ok(v.to_string()),
        StackItem::Int64(v) => Ok(v.to_string()),
        StackItem::UInt8(v) => Ok(v.to_string()),
        StackItem::UInt16(v) => Ok(v.to_string()),
        StackItem::UInt32(v) => Ok(v.to_string()),
        StackItem::UInt64(v) => Ok(v.to_string()),
        StackItem::USize(v) => Ok(v.to_string()),
        StackItem::Float32(v) => Ok(format!("{:.6e}", v)),
        StackItem::Float64(v) => Ok(format!("{:.6e}", v)),
    }
}

fn call_stdout(
    register_counter: &mut usize,
    stack: &mut Vec<StackItem>,
    code: &mut String,
    arg_type: &Type,
) -> Result<(), CompilerError> {
    let arg = get_last_item_rep_checked(arg_type, stack)?;
    *register_counter += 1;
    let (template, dtype) = match arg_type {
        Type::Float32 => ("@.str.g", "double"),
        Type::Float64 => ("@.str.g", "double"),
        Type::Int8 => ("@.str.i", "i8"),
        Type::Int16 => ("@.str.i", "i16"),
        Type::Int32 => ("@.str.i", "i32"),
        Type::UInt8 => ("@.str.u", "i8"),
        Type::UInt16 => ("@.str.u", "i16"),
        Type::UInt32 => ("@.str.u", "i32"),
        _ => return Err(CompilerError::global(&format!("Missing argument on stack"))),
    };
    code.push_str(&format!("  %{} = call i32 (i8*, ...) @printf(i8* noundef getelementptr inbounds ([4 x i8], [4 x i8]* {}, i32 0, i32 0), {} noundef {})\n", register_counter, template, dtype, arg));
    Ok(())
}

trait ToLLVM {
    fn to_llvm(&self) -> &'static str;
    fn align(&self) -> u8;
}

impl ToLLVM for Type {
    fn to_llvm(&self) -> &'static str {
        match self {
            Type::Int8 => "i8",
            Type::Int16 => "i16",
            Type::Int32 => "i32",
            Type::Int64 => "i64",
            // LLVM does not distinguish between signed and unsigned.
            Type::UInt8 => "i8",
            Type::UInt16 => "i16",
            Type::UInt32 => "i32",
            Type::UInt64 => "i64",
            Type::USize => "usize",
            Type::Float32 => "float",
            Type::Float64 => "double",
            Type::Void => "void",
            Type::Type => panic!("Type can not be used as an variable"),
        }
    }
    fn align(&self) -> u8 {
        match self {
            Type::Int8 | Type::UInt8 => 1,
            Type::Int16 | Type::UInt16 => 2,
            Type::Int32 | Type::UInt32 => 4,
            Type::Float32 => 4,
            Type::USize => 4,
            Type::Int64 | Type::UInt64 => 8,
            Type::Float64 => 8,
            _ => panic!("Type can not be used as an variable"),
        }
    }
}

fn mangle(ident: &str, signature: &Signature<Type>) -> String {
    let args = signature
        .args
        .iter()
        .map(|t| t.to_llvm())
        .collect::<Vec<_>>();
    format!(
        "{}_{}__{}",
        ident,
        signature.return_type.to_llvm(),
        args.join("_")
    )
}

fn call_function_2_gen(
    function_name: &str,
    return_type: &Type,
    a_type: &Type,
    b_type: &Type,
    register_counter: &mut usize,
    stack: &mut Vec<StackItem>,
    code: &mut String,
) -> Result<(), CompilerError> {
    let b = get_last_item_rep_checked(b_type, stack)?;
    let a = get_last_item_rep_checked(a_type, stack)?;
    let function_name = mangle(
        function_name,
        &Signature {
            return_type: return_type.clone(),
            args: vec![a_type.clone(), b_type.clone()],
        },
    );
    *register_counter += 1;
    code.push_str(&format!(
        "  %{} = call {} @{}({} {}, {} {})\n",
        register_counter,
        return_type.to_llvm(),
        function_name,
        a_type.to_llvm(),
        a,
        b_type.to_llvm(),
        b
    ));
    stack.push(StackItem::Ref(*register_counter));
    Ok(())
}

fn operator(
    operator_name: &str,
    op_type: &Type,
    register_counter: &mut usize,
    stack: &mut Vec<StackItem>,
    code: &mut String,
) -> Result<(), CompilerError> {
    *register_counter += 1;
    let b = get_last_item_rep_any(stack)?;
    let a = get_last_item_rep_any(stack)?;
    code.push_str(&format!(
        "  %{} = {} {} {}, {}\n",
        register_counter,
        operator_name,
        op_type.to_llvm(),
        a,
        b
    ));
    stack.push(StackItem::Ref(*register_counter));
    Ok(())
}

/// See https://llvm.org/docs/LangRef.html#conversion-operations
fn cast(
    from: &Type,
    to: &Type,
    register_counter: &mut usize,
    stack: &mut Vec<StackItem>,
    code: &mut String,
) -> Result<(), CompilerError> {
    *register_counter += 1;
    let value = get_last_item_rep_checked(from, stack)?;
    let op_code = match (from, to) {
        (_, Type::Float32 | Type::Float64) => "fpext",
        (Type::Int32 | Type::UInt32, Type::Int8 | Type::UInt8) => "trunc",
        _ => "sext",
    };
    code.push_str(&format!(
        "  %{} = {} {} {} to {}\n",
        register_counter,
        op_code,
        from.to_llvm(),
        value,
        to.to_llvm(),
    ));
    stack.push(StackItem::Ref(*register_counter));
    Ok(())
}

pub fn export(instructions: &[ByteCode], source_filename: &str) -> Result<String, CompilerError> {
    let mut code = String::new();

    write_header(source_filename, &mut code);
    write_empty_line(&mut code);
    write_format_string(&mut code);
    buildins::write_functions(&mut code);
    write_empty_line(&mut code);
    // The main function
    code.push_str("; Function Attrs: noinline nounwind optnone uwtable\n");
    code.push_str("define dso_local i32 @main() #0 {\n");
    let mut register_counter = 0;

    // Find all alloca
    for instruction in instructions.iter() {
        if let ByteCode::Alloca(dtype) = instruction {
            register_counter += 1;
            code.push_str(&format!(
                "  %{} = alloca {}, align {}\n",
                register_counter,
                dtype.to_llvm(),
                dtype.align()
            ));
        }
    }

    let mut stack: Vec<StackItem> = Vec::new();
    for instruction in instructions.iter() {
        match instruction {
            ByteCode::StdOut(arg_type) => {
                call_stdout(&mut register_counter, &mut stack, &mut code, arg_type)?
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
            ByteCode::Call2(ident, return_type, arg_type_0, arg_type_1) => {
                call_function_2_gen(
                    ident,
                    return_type,
                    arg_type_0,
                    arg_type_1,
                    &mut register_counter,
                    &mut stack,
                    &mut code,
                )?;
            }
            ByteCode::Store(op_type, index) => {
                let a = get_last_item_rep_checked(op_type, &mut stack)?;
                store(*index + 1, a, op_type, &mut code);
            }
            ByteCode::Alloca(_) => (),
            ByteCode::Load(op_type, index) => {
                register_counter += 1;
                code.push_str(&format!(
                    "  %{0} = load {1}, {1}* %{2}, align 4\n",
                    register_counter,
                    op_type.to_llvm(),
                    index + 1
                ));
                stack.push(StackItem::Ref(register_counter));
            }
            ByteCode::Add(op_type) => {
                let op_code = match op_type {
                    Type::Float32 | Type::Float64 => "fadd",
                    _ => "add",
                };
                operator(
                    op_code,
                    op_type,
                    &mut register_counter,
                    &mut stack,
                    &mut code,
                )?
            }
            ByteCode::Sub(op_type) => {
                let op_code = match op_type {
                    Type::Float32 | Type::Float64 => "fsub",
                    _ => "sub",
                };
                operator(
                    op_code,
                    op_type,
                    &mut register_counter,
                    &mut stack,
                    &mut code,
                )?
            }
            ByteCode::Mul(op_type) => {
                let op_code = match op_type {
                    Type::Float32 | Type::Float64 => "fmul",
                    _ => "mul",
                };
                operator(
                    op_code,
                    op_type,
                    &mut register_counter,
                    &mut stack,
                    &mut code,
                )?
            }
            ByteCode::Div(op_type) => operator(
                "sdiv",
                op_type,
                &mut register_counter,
                &mut stack,
                &mut code,
            )?,
            ByteCode::Rem(op_type) => operator(
                "srem",
                op_type,
                &mut register_counter,
                &mut stack,
                &mut code,
            )?,
            ByteCode::CastInt(from, to) => {
                cast(from, to, &mut register_counter, &mut stack, &mut code)?;
            }
        }
    }

    code.push_str("  ret i32 0\n");
    code.push_str("}\n\n");
    // End of main

    write_printf_declaration(&mut code);
    write_empty_line(&mut code);

    let main_attr = hashmap! {
        "noinline" => "",
        "nounwind" => "",
        "optnone" => "",
        "uwtable" => "",
        "correctly-rounded-divide-sqrt-fp-math"=>"false",
        "disable-tail-calls"=>"false",
        "less-precise-fpmad"=>"false",
        "min-legal-vector-width"=>"0",
        "no-frame-pointer-elim"=>"true",
        "no-frame-pointer-elim-non-leaf"=>"",
        "no-infs-fp-math"=>"false",
        "no-jump-tables"=>"false",
        "no-nans-fp-math"=>"false",
        "no-signed-zeros-fp-math"=>"false",
        "no-trapping-math"=>"false",
        "stack-protector-buffer-size"=>"8",
        "target-cpu"=>"x86-64",
        "target-features"=>"+fxsr,+mmx,+sse,+sse2,+x87",
        "unsafe-fp-math"=>"false",
        "use-soft-float"=>"false"
    };
    write_attribute(0, main_attr, &mut code);

    let printf_attr = hashmap! {
        "correctly-rounded-divide-sqrt-fp-math"=>"false",
        "disable-tail-calls"=>"false",
        "less-precise-fpmad"=>"false",
        "no-frame-pointer-elim"=>"true",
        "no-frame-pointer-elim-non-leaf"=>"",
        "no-infs-fp-math"=>"false",
        "no-nans-fp-math"=>"false",
        "no-signed-zeros-fp-math"=>"false",
        "no-trapping-math"=>"false",
        "stack-protector-buffer-size"=>"8",
        "target-cpu"=>"x86-64",
        "target-features"=>"+fxsr,+mmx,+sse,+sse2,+x87",
        "unsafe-fp-math"=>"false",
        "use-soft-float"=>"false"
    };
    write_attribute(1, printf_attr, &mut code);
    write_empty_line(&mut code);

    write_footer(&mut code);

    Ok(code)
}
