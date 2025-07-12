mod gen;
use crate::gen::generate_llvm;

mod ir;
use crate::ir::print_ir;
use crate::ir::Globals;

mod compile;
use crate::compile::compile_to_ir;

mod lex;
use crate::lex::Lexer;

use core::str;

use std::env;
use std::error::Error;
use std::fs;
use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::process::Command;

fn compile(
    code: &str,
    file_name: &str,
    should_print_ir: bool,
    numbering_fix: bool,
) -> Result<String, String> {
    let mut lexer = Lexer::new(code, file_name);
    let mut globals = Globals::new();

    let locals = compile_to_ir(&mut lexer, &mut globals)?;
    if should_print_ir {
        print_ir(&locals, &globals);
    }

    generate_llvm(&locals, &globals, numbering_fix)
}

fn run_stage(program: &str, input_file: &str, output_file: &str) -> Result<(), Box<dyn Error>> {
    if Command::new(program)
        .arg("-o")
        .arg(output_file)
        .arg(input_file)
        .status()
        .map_err(|err| format!("running {program} failed: {err}"))?
        .success()
    {
        Result::Ok(())
    } else {
        Result::Err(Box::from(format!("{program} failed")))
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Flag {
    None,
    OutputFile,
}

fn change_extension(path: &str, old_extension: &str, new_extension: &str) -> String {
    path.trim_end_matches(old_extension).to_owned() + new_extension
}

fn do_work() -> Result<(), Box<dyn Error>> {
    let mut input_file = Option::<String>::None;
    let mut output_file = Option::<String>::None;
    let mut lex = false;
    let mut ir = false;
    let mut print = false;
    let mut run = false;
    let mut numbering_fix = false;

    let mut current_flag = Flag::None;
    for arg in env::args().skip(1) {
        match arg.as_str() {
            "-o" => {
                current_flag = Flag::OutputFile;
            }
            "--run" => {
                if run {
                    return Result::Err(Box::from("--run specified twice"));
                }
                run = true;
            }
            "--lex" => {
                if lex {
                    return Result::Err(Box::from("--lex specified twice"));
                }
                lex = true;
            }
            "--ir" => {
                if ir {
                    return Result::Err(Box::from("--ir specified twice"));
                }
                ir = true;
            }
            "--print" => {
                if print {
                    return Result::Err(Box::from("--print specified twice"));
                }
                print = true;
            }
            "--numbering-fix" => {
                if numbering_fix {
                    return Result::Err(Box::from("--numbering-fix specified twice"));
                }
                numbering_fix = true;
            }
            flag if flag.starts_with('-') => {
                return Result::Err(Box::from(format!("flag {flag} is unknown")))
            }
            arg => match current_flag {
                Flag::None => {
                    if input_file.is_none() {
                        input_file = Option::Some(arg.to_owned());
                    } else {
                        return Result::Err(Box::from("multiple input files provided"));
                    }
                }
                Flag::OutputFile => {
                    current_flag = Flag::None;
                    if output_file.is_none() {
                        output_file = Option::Some(arg.to_owned());
                    } else {
                        return Result::Err(Box::from("multiple input files provided"));
                    }
                }
            },
        }
    }

    if current_flag == Flag::OutputFile {
        return Result::Err(Box::from("-o expects an output file as an argument"));
    }

    let extension = ".jost";
    let input_file = input_file.ok_or("no input files provided")?;
    let ir_file = change_extension(input_file.as_str(), extension, ".ll");
    let bc_file = change_extension(input_file.as_str(), extension, ".bc");
    let asm_file = change_extension(input_file.as_str(), extension, ".s");
    let output_file = change_extension(input_file.as_str(), extension, ".exe");

    let mut code = String::new();
    OpenOptions::new()
        .read(true)
        .open(&input_file)?
        .read_to_string(&mut code)?;

    if lex {
        Lexer::debug_print(code.as_str());
    }

    let llvm = compile(code.as_str(), &input_file, ir, numbering_fix)?;

    OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&ir_file)?
        .write_all(llvm.as_bytes())?;

    if print {
        println!("{llvm}");
    }

    run_stage("llvm-as", ir_file.as_str(), &bc_file)?;
    run_stage("llc", &bc_file, &asm_file)?;
    run_stage("clang", &asm_file, output_file.as_str())?;

    if run {
        let abs_output_path = fs::canonicalize(&output_file)?;
        Command::new(&abs_output_path).status()?;
    }

    Result::Ok(())
}

fn main() {
    match do_work() {
        Ok(()) => {}
        Err(err) => println!("{err}"),
    }
}
