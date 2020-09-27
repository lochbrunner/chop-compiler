use std::collections::HashMap;
use std::fmt;

use core::{ByteCode, CompilerError, declaration::Type};

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
    code.push_str("@.str = private unnamed_addr constant [4 x i8] c\"%d\\0A\\00\", align 1\n");
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
    Int64(i64),
    Int32(i32),
    Int16(i16),
    Int8(i8),
    Ref(usize),
}

fn store<T>(index: usize, value: T, v_type: &Type, code: &mut String)
where
    T: fmt::Display,
{
    code.push_str(&format!(
        "  store {} {}, {}* %{}, align 4\n",
        v_type.to_llvm(),
        value,
        v_type.to_llvm(),
        index
    ));
}

fn get_last_item_rep_gen(stack: &mut Vec<StackItem>) -> Result<String, CompilerError> {
    match stack.pop() {
        None => Err(CompilerError::global("Missing argument on stack")),
        Some(item) => match item {
            StackItem::Ref(r) => Ok(format!("%{}", r)),
            StackItem::Int8(v) => Ok(v.to_string()),
            StackItem::Int16(v) => Ok(v.to_string()),
            StackItem::Int32(v) => Ok(v.to_string()),
            StackItem::Int64(v) => Ok(v.to_string()),
        },
    }
}

fn get_last_item_rep_i32(stack: &mut Vec<StackItem>) -> Result<String, CompilerError> {
    match stack.pop() {
        None => Err(CompilerError::global("Missing argument on stack")),
        Some(item) => match item {
            StackItem::Int32(v) => Ok(v.to_string()),
            StackItem::Ref(r) => Ok(format!("%{}", r)),
            _ => Err(CompilerError::global(&format!(
                "Expected stack item of type Int32, but got {:?}",
                item
            ))),
        },
    }
}

fn call_stdout(
    register_counter: &mut usize,
    stack: &mut Vec<StackItem>,
    code: &mut String,
) -> Result<(), CompilerError> {
    let arg = get_last_item_rep_i32(stack)?;
    *register_counter += 1;
    code.push_str(&format!("  %{} = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i32 0, i32 0), i32 {})\n", 
                                    register_counter, arg));
    Ok(())
}

trait ToLLVM {
    fn to_llvm(&self) -> &'static str;
}

impl ToLLVM for Type {
    fn to_llvm(&self) -> &'static str {
        match self {
            Type::Int8 => "i8",
            Type::Int16 => "i16",
            Type::Int32 => "i32",
            Type::Int64 => "i64",
            Type::Void => "void",
        }
    }
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
    let b = get_last_item_rep_gen(stack)?;
    let a = get_last_item_rep_gen(stack)?;
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
    let b = get_last_item_rep_gen(stack)?;
    let a = get_last_item_rep_gen(stack)?;
    code.push_str(&format!(
        "  %{} = {} nsw {} {}, {}\n",
        operator_name,
        register_counter,
        op_type.to_llvm(),
        a,
        b
    ));
    stack.push(StackItem::Ref(*register_counter));
    Ok(())
}

fn cast(
    from: &Type,
    to: &Type,
    register_counter: &mut usize,
    stack: &mut Vec<StackItem>,
    code: &mut String,
) -> Result<(), CompilerError> {
    *register_counter += 1;
    let value = get_last_item_rep_gen(stack)?;
    code.push_str(&format!(
        "  %{} = sext {} {} to {}\n",
        register_counter,
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
    buildins::write_min_function(&mut code);
    buildins::write_max_function(&mut code);
    write_empty_line(&mut code);
    // The main function
    code.push_str("; Function Attrs: noinline nounwind optnone uwtable\n");
    code.push_str("define dso_local i32 @main() #0 {\n");
    let mut register_counter = 0;

    // Find all alloca
    for _ in instructions
        .iter()
        .filter(|s| **s == ByteCode::Alloca(Type::Int32))
    {
        register_counter += 1;
        code.push_str(&format!("  %{} = alloca i32, align 4\n", register_counter));
    }

    let mut stack: Vec<StackItem> = Vec::new();
    for instruction in instructions.iter() {
        match instruction {
            ByteCode::StdOut => call_stdout(&mut register_counter, &mut stack, &mut code)?,
            ByteCode::PushInt32(v) => stack.push(StackItem::Int32(*v)),
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
                let a = get_last_item_rep_i32(&mut stack)?;
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
                operator("add", op_type, &mut register_counter, &mut stack, &mut code)?
            }
            ByteCode::Sub(op_type) => {
                operator("sub", op_type, &mut register_counter, &mut stack, &mut code)?
            }
            ByteCode::Mul(op_type) => {
                operator("mul", op_type, &mut register_counter, &mut stack, &mut code)?
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
            _ => {
                return Err(CompilerError::global(&format!(
                    "Unknown instruction {:?}",
                    instruction
                )))
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
