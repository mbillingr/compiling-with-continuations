use crate::core::answer::Answer;
use crate::core::env::Env;
use crate::core::reference::Ref;
use crate::languages::cps_lang::ast;

type Expr = ast::Expr<Ref<str>>;
type Value = ast::Value<Ref<str>>;

pub unsafe fn exec(expr: &Expr) -> Answer {
    eval_expr(expr, Env::Empty)
}

pub unsafe fn eval_expr(mut expr: &Expr, mut env: Env) -> Answer {
    match expr {
        Expr::App(Value::Halt, args) => eval_val(&args[0], env),
        _ => todo!("{:?}", expr),
    }
}

pub fn eval_val(val: &Value, env: Env) -> Answer {
    match val {
        Value::Int(x) => Answer::from_int(*x),
        _ => todo!("{:?}", val),
    }
}
