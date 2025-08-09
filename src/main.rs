mod gen;
use crate::gen::generate_llvm;

mod ir;
use crate::ir::print_ir;
use crate::ir::Globals;

mod compile;
use crate::compile::compile_to_ir;

mod lex;
use crate::lex::Lexer;

mod types;

use core::str;

use std::env;
use std::error::Error;
use std::fs;
use std::fs::read_dir;
use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::path::Path;
use std::process::Command;
use std::process::Stdio;

fn compile(
    code: &str,
    file_name: &Path,
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

fn run_stage(program: &str, input_file: &Path, output_file: &Path) -> Result<(), Box<dyn Error>> {
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

#[derive(Clone)]
struct Flags {
    lex: bool,
    ir: bool,
    print: bool,
    run: bool,
    numbering_fix: bool,
    run_as_test: bool,
}

impl Flags {
    fn new() -> Self {
        Self {
            lex: false,
            ir: false,
            print: false,
            run: false,
            numbering_fix: false,
            run_as_test: false,
        }
    }
}

fn compile_file(
    input_file: &Path,
    output_file: Option<&Path>,
    flags: Flags,
) -> Result<(), Box<dyn Error>> {
    if !input_file.try_exists()? {
        Result::Err(Box::from(format!(
            "{} doesn't exist",
            input_file.to_string_lossy()
        )))
    } else if input_file.is_dir() {
        if flags.run_as_test {
            for path in read_dir(input_file)? {
                let path = path?.path();
                if path.is_dir() {
                    compile_file(&path, output_file, flags.clone())?;
                } else if path
                    .extension()
                    .is_some_and(|extension| extension == "jost")
                {
                    if let Result::Err(error) = compile_file(&path, output_file, flags.clone()) {
                        println!(
                            "test {} \x1b[31merror\x1b[0m\n{error}",
                            path.to_string_lossy()
                        );
                    } else {
                        println!("test {} \x1b[32mok\x1b[0m", path.to_string_lossy());
                    }
                }
            }
            Result::Ok(())
        } else {
            Result::Err(Box::from(format!(
                "{} is a directory, can't compile it except --test mode",
                input_file.to_string_lossy()
            )))
        }
    } else {
        let ir_file = input_file.with_extension("ll");
        let bc_file = input_file.with_extension("bc");
        let asm_file = input_file.with_extension("s");
        let output_file = output_file.map_or_else(
            || input_file.with_extension("exe"),
            |output_file| output_file.to_owned(),
        );

        let mut code = String::new();
        OpenOptions::new()
            .read(true)
            .open(input_file)?
            .read_to_string(&mut code)?;

        if flags.lex {
            Lexer::debug_print(code.as_str());
        }

        let llvm = compile(code.as_str(), input_file, flags.ir, flags.numbering_fix)?;

        OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&ir_file)?
            .write_all(llvm.as_bytes())?;

        if flags.print {
            println!("{llvm}");
        }

        run_stage("llvm-as", &ir_file, &bc_file)?;
        run_stage("llc", &bc_file, &asm_file)?;
        run_stage("clang", &asm_file, &output_file)?;

        if flags.run_as_test {
            let abs_path = fs::canonicalize(&output_file)?;
            let input_path = abs_path.with_extension("in");
            let captured_output_path = abs_path.with_extension("out.capture");
            let expected_output_path = abs_path.with_extension("out");

            let stdin = if input_path.try_exists()? {
                Stdio::from(OpenOptions::new().read(true).open(input_path)?)
            } else {
                Stdio::null()
            };

            let stdout = OpenOptions::new()
                .write(true)
                .create(true)
                .truncate(true)
                .open(&captured_output_path)?;

            let status = Command::new(abs_path)
                .stdin(stdin)
                .stdout(stdout)
                .status()?;

            if !status.success() {
                return Result::Err(Box::from(format!(
                    "compiled program failed with exit code {}",
                    status
                        .code()
                        .map(|exit_code| exit_code.to_string())
                        .unwrap_or("none".to_owned())
                )));
            }

            if expected_output_path.try_exists()? {
                let mut expected_output = String::new();
                OpenOptions::new()
                    .read(true)
                    .open(expected_output_path)?
                    .read_to_string(&mut expected_output)?;

                let mut captured_output = String::new();
                OpenOptions::new()
                    .read(true)
                    .open(captured_output_path)?
                    .read_to_string(&mut captured_output)?;

                if expected_output != captured_output {
                    return Result::Err(Box::from(format!("Captured output doesn't match expected\nCaptured output:\n{captured_output}Expected output:\n{expected_output}")));
                }
            }
        }

        if flags.run {
            let abs_path = fs::canonicalize(&output_file)?;
            let status = Command::new(&abs_path).status()?;
            if !status.success() {
                return Result::Err(Box::from(format!(
                    "compiled program failed with exit code {}",
                    status
                        .code()
                        .map(|exit_code| exit_code.to_string())
                        .unwrap_or("none".to_owned())
                )));
            }
        }

        Result::Ok(())
    }
}

fn do_work() -> Result<(), Box<dyn Error>> {
    let mut flags = Flags::new();
    let mut input_file = Option::<String>::None;
    let mut output_file = Option::<String>::None;

    let mut current_flag = Flag::None;
    for arg in env::args().skip(1) {
        match arg.as_str() {
            "-o" => {
                current_flag = Flag::OutputFile;
            }
            "--run" => {
                if flags.run {
                    return Result::Err(Box::from("--run specified twice"));
                }
                flags.run = true;
            }
            "--lex" => {
                if flags.lex {
                    return Result::Err(Box::from("--lex specified twice"));
                }
                flags.lex = true;
            }
            "--ir" => {
                if flags.ir {
                    return Result::Err(Box::from("--ir specified twice"));
                }
                flags.ir = true;
            }
            "--print" => {
                if flags.print {
                    return Result::Err(Box::from("--print specified twice"));
                }
                flags.print = true;
            }
            "--numbering-fix" => {
                if flags.numbering_fix {
                    return Result::Err(Box::from("--numbering-fix specified twice"));
                }
                flags.numbering_fix = true;
            }
            "--test" => {
                if flags.run_as_test {
                    return Result::Err(Box::from("--test specified twice"));
                }
                flags.run_as_test = true;
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

    let input_file = input_file.ok_or("no input files provided")?;
    compile_file(
        Path::new(&input_file),
        output_file.as_ref().map(Path::new),
        flags,
    )?;

    Result::Ok(())
}

fn main() {
    match do_work() {
        Ok(()) => {}
        Err(err) => println!("{err}"),
    }
}
