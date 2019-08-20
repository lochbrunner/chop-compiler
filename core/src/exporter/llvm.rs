use crate::CompilerError;
use std::collections::HashMap;

use crate::bytecode::ByteCode;

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
    code.push_str("!1 = !{!\"clang version 8.0.0-3 (tags/RELEASE_800/final)\"}\n");
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
    Int32(i32),
}

pub fn export(instructions: &[ByteCode], source_filename: &str) -> Result<String, CompilerError> {
    let mut code = String::new();

    write_header(source_filename, &mut code);
    write_empty_line(&mut code);
    write_format_string(&mut code);
    write_empty_line(&mut code);
    // The main function
    code.push_str("; Function Attrs: noinline nounwind optnone uwtable\n");
    code.push_str("define dso_local i32 @main() #0 {\n");
    code.push_str("  %1 = alloca i32, align 4\n");
    code.push_str("  store i32 0, i32* %1, align 4\n");

    let mut stack_counter = 1;

    let mut stack: Vec<StackItem> = Vec::new();
    for instruction in instructions.iter() {
        match instruction {
            ByteCode::StdOut => match stack.pop() {
                Some(stack_item) => match stack_item {
                    StackItem::Int32(v) => {
                        stack_counter += 1;
                        code.push_str(&format!(
                                    "  %{} = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i32 0, i32 0), i32 {})\n", 
                                    stack_counter, v));
                    }
                },
                None => {
                    return Err(CompilerError {
                        location: crate::token::Location { line: 0, offset: 0 },
                        msg: format!(
                        "Exporter Error: Function stdout expects an int as argument but got {:?}",
                        instruction
                    ),
                    })
                }
            },
            ByteCode::PushInt32(v) => stack.push(StackItem::Int32(*v)),
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
