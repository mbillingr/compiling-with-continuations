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
        CliCmd::InterpretCps => interpret_cps(),
        CliCmd::ToCps => to_cps(args.gensym_delimiter),
        CliCmd::ConvertLabels => convert_labels(),
        CliCmd::EtaReduceCps => eta_reduce(),
    }
}

fn interpret_cps() {
    type Expr = crate::languages::cps_lang::ast::Expr<Ref<str>>;

    let mut src = String::new();
    stdin().read_to_string(&mut src).unwrap();

    let expr_in = Expr::from_str(&src).unwrap();

    unsafe {
        crate::languages::cps_lang::interpreter::exec(&expr_in, &mut stdout());
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
