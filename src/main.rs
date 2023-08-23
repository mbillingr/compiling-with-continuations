use crate::languages::mini_lambda::ast::Expr;
use crate::languages::mini_lambda::interpreter::exec;

pub mod core;
pub mod languages;
pub mod transformations;

fn main() {
    println!("{:?}", unsafe {
        exec(&Expr::App(
            Expr::Fn("x".into(), Expr::Var("x".into()).into()).into(),
            Expr::Int(42).into(),
        ))
    })
}
