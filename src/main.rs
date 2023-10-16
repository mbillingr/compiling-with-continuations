use crate::core::reference::Ref;
use clap::{Parser, Subcommand};
use std::io::{stdin, stdout, Read, Write};

pub mod core;
pub mod languages;
pub mod transformations;

/// Transform code represented by s-expressions.
#[derive(Debug, Parser)]
struct CliApp {
    #[command(subcommand)]
    command: CliCmd,

    #[arg(long, default_value = "__")]
    gensym_delimiter: String,
}

#[derive(Debug, Clone, Subcommand)]
enum CliCmd {
    /// Interpret CPS
    InterpretCps { output_type: String },

    /// Convert mini-lambda into CPS language
    ToCps,

    /// Distinguish references to known functions from variable references
    ConvertLabels,

    /// Perform η-reduction on the CPS language
    EtaReduceCps,
}

fn main() {
    let args = CliApp::parse();

    match args.command {
        CliCmd::InterpretCps { output_type } => {
            interpret_cps(match output_type.to_lowercase().as_str() {
                "bool" => AnswerType::Bool,
                "int" => AnswerType::Int,
                "float" => AnswerType::Float,
                "str" => AnswerType::Str,
                _ => panic!("Invalid output type"),
            })
        }
        CliCmd::ToCps => to_cps(args.gensym_delimiter),
        CliCmd::ConvertLabels => convert_labels(),
        CliCmd::EtaReduceCps => eta_reduce(args.gensym_delimiter),
    }
}

enum AnswerType {
    Bool,
    Int,
    Float,
    Str,
}

fn interpret_cps(answer_type: AnswerType) {
    type Expr = crate::languages::cps_lang::ast::Expr<Ref<str>>;

    let mut src = String::new();
    stdin().read_to_string(&mut src).unwrap();

    let expr_in = Expr::from_str(&src).unwrap();

    unsafe {
        let answer = crate::languages::cps_lang::interpreter::exec(&expr_in);
        match answer_type {
            AnswerType::Bool => writeln!(stdout(), "{}", answer.as_bool()).unwrap(),
            AnswerType::Int => writeln!(stdout(), "{}", answer.as_int()).unwrap(),
            AnswerType::Float => writeln!(stdout(), "{}", answer.as_float()).unwrap(),
            AnswerType::Str => writeln!(stdout(), "{}", answer.as_str()).unwrap(),
        }
    }
}

fn to_cps(gensym_delimiter: String) {
    use crate::transformations::mini_lambda_to_cps_lang::Context;
    type LExpr = crate::languages::mini_lambda::ast::Expr<Ref<str>>;
    type CExpr = crate::languages::cps_lang::ast::Expr<Ref<str>>;

    let ctx = Box::leak(Box::new(Context::new(gensym_delimiter)));

    let mut src = String::new();
    stdin().read_to_string(&mut src).unwrap();

    let expr_in = LExpr::from_str(&src).unwrap();

    let expr_out = ctx.convert(&expr_in, Box::new(|x| CExpr::Halt(x)));

    writeln!(stdout(), "{}", expr_out).unwrap();
}

fn eta_reduce(gensym_delimiter: String) {
    use crate::transformations::cps_eta_reduction::Context;
    type CExpr = crate::languages::cps_lang::ast::Expr<Ref<str>>;

    let ctx = Box::leak(Box::new(Context::new(gensym_delimiter)));

    let mut src = String::new();
    stdin().read_to_string(&mut src).unwrap();

    let expr_in = CExpr::from_str(&src).unwrap();

    let expr_out = ctx.eta_reduce(&expr_in);

    writeln!(stdout(), "{}", expr_out).unwrap();
}

fn convert_labels() {
    use crate::transformations::label_fixrefs::Context;
    type CExpr = crate::languages::cps_lang::ast::Expr<Ref<str>>;

    let ctx = Box::leak(Box::new(Context::new()));

    let mut src = String::new();
    stdin().read_to_string(&mut src).unwrap();

    let expr_in = CExpr::from_str(&src).unwrap();

    let expr_out = ctx.convert_labels(&expr_in);

    writeln!(stdout(), "{}", expr_out).unwrap();
}
