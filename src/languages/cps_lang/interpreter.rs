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
    loop {
        match expr {
            Expr::Record(items, outvar, cnt) => {
                let mut data = Vec::with_capacity(items.len());
                for item in &**items {
                    data.push(eval_val(item, env));
                }
                env = env.extend(*outvar, Answer::tuple(data));
                expr = cnt;
            }

            Expr::Select(idx, recval, outvar, cnt) => {
                let rec = eval_val(recval, env);
                env = env.extend(*outvar, rec.get_item(*idx));
                expr = cnt;
            }

            Expr::App(Value::Halt, args) => return eval_val(&args[0], env),

            _ => todo!("{:?}", expr),
        }
    }
}

pub fn eval_val(val: &Value, env: Env) -> Answer {
    match val {
        Value::Var(v) => env.lookup(v),
        Value::Int(x) => Answer::from_int(*x),
        _ => todo!("{:?}", val),
    }
}
