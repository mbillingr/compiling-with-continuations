use crate::core::reference::Ref;
use crate::transformations::GensymContext;
use clap::{Parser, Subcommand};
use std::fs::File;
use std::io::{stdin, stdout, Read, Write};
use std::path::Path;
use std::sync::Arc;

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

    #[arg(default_value = None)]
    input_file: Option<String>,
}

#[derive(Debug, Clone, Subcommand)]
enum CliCmd {
    /// Run a Type-Lang program
    RunTypeLang { source_file: Option<String> },

    /// Interpret CPS
    InterpretCps,

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
        CliCmd::RunTypeLang { source_file } => run_typelang(source_file.as_ref().map(Path::new)),
        CliCmd::InterpretCps => interpret_cps(),
        CliCmd::ToCps => to_cps(args.gensym_delimiter),
        CliCmd::ConvertLabels => convert_labels(),
        CliCmd::EtaReduceCps => eta_reduce(),
    }
}

fn run_typelang(source_file: Option<&Path>) {
    use crate::languages::mini_lambda::interpreter;
    use crate::languages::type_lang::type_checker::Checker;
    use crate::transformations::{type_lang_monomorphize, type_lang_to_mini_lambda};
    type TExpr = crate::languages::type_lang::ast::Expr;

    let mut src = String::new();
    match source_file {
        None => stdin().read_to_string(&mut src).unwrap(),
        Some(path) => File::open(path).unwrap().read_to_string(&mut src).unwrap(),
    };

    let gs = Arc::new(GensymContext::default());

    let expr_in = TExpr::from_str(&src).unwrap();
    let checked = Checker::check_program(&expr_in).unwrap();
    let mono = type_lang_monomorphize::Context::new(gs.clone()).monomporphize(&checked);
    let mini_la = type_lang_to_mini_lambda::Context::new(gs.clone()).convert(&mono);
    println!("{}", mini_la);
    unsafe { interpreter::exec(&mini_la, &mut stdout(), &mut stdin().lock()) }
}

fn interpret_cps() {
    type Expr = crate::languages::cps_lang::ast::Expr<Ref<str>>;

    let mut src = String::new();
    stdin().read_to_string(&mut src).unwrap();

    let expr_in = Expr::from_str(&src).unwrap();

    unsafe {
        crate::languages::cps_lang::interpreter::exec(&expr_in, &mut stdout(), &mut stdin().lock());
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

fn eta_reduce() {
    use crate::transformations::cps_eta_reduction::Context;
    type CExpr = crate::languages::cps_lang::ast::Expr<Ref<str>>;

    let mut src = String::new();
    stdin().read_to_string(&mut src).unwrap();

    let expr_in = CExpr::from_str(&src).unwrap();

    let expr_out = Context.eta_reduce(&expr_in);

    writeln!(stdout(), "{}", expr_out).unwrap();
}

fn convert_labels() {
    use crate::transformations::label_fixrefs::Context;
    type CExpr = crate::languages::cps_lang::ast::Expr<Ref<str>>;

    let ctx = Box::leak(Box::new(Context::new()));

    let mut src = String::new();
    stdin().read_to_string(&mut src).unwrap();

    let expr_in = CExpr::from_str(&src).unwrap();

    let expr_out = ctx.analyze_refs(&expr_in);

    writeln!(stdout(), "{}", expr_out).unwrap();
}
