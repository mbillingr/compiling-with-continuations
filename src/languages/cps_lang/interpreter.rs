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

            Expr::Offset(idx, recval, outvar, cnt) => {
                let rec = eval_val(recval, env);
                env = env.extend(*outvar, rec.ptr_offset(*idx));
                expr = cnt;
            }

            Expr::Select(idx, recval, outvar, cnt) => {
                let rec = eval_val(recval, env);
                env = env.extend(*outvar, rec.get_item(*idx));
                expr = cnt;
            }

            Expr::App(Value::Halt, args) => return eval_val(&args[0], env),

            Expr::App(fval, argvals) => {
                let f = eval_val(fval, env);
                let args = argvals.iter().map(move |a| eval_val(a, env));

                let cls = f.as_ref::<Closure>();

                env = cls.captured_env;
                for (a, v) in args.zip(&*cls.params) {
                    env = env.extend(*v, a);
                }
                expr = &cls.body;
            }

            Expr::Fix(defs, cnt) => {
                let closures: Vec<_> = defs
                    .iter()
                    .map(|(_, params, body)| {
                        Closure {
                            captured_env: Env::Empty, //placeholder
                            params: *params,
                            body: *body,
                        }
                    })
                    .map(Ref::new)
                    .collect();

                let mut common_env = env.clone();
                for (name, cls) in defs.iter().map(|(name, _, _)| name).zip(&closures) {
                    common_env = common_env.extend(*name, Answer::from_ref(*cls));
                }

                for cls in closures.into_iter() {
                    cls.unsafe_mutate(|cls| cls.captured_env = common_env);
                }

                env = common_env;
                expr = cnt;
            }

            Expr::Switch(val, cnts) => {
                let idx = eval_val(val, env).as_int();
                expr = &cnts[idx as usize];
            }

            Expr::PrimOp(op, args, _, cnts) if op.is_branching() => {
                let x = (0..op.n_args()).map(|i| eval_val(&args[i], env));
                let p = op.apply(x);
                expr = &cnts[p.repr()];
            }

            Expr::PrimOp(op, args, vars, cnts) => {
                let x = (0..op.n_args()).map(|i| eval_val(&args[i], env));
                env = env.extend(vars[0], op.apply(x));
                expr = &cnts[0];
            }

            Expr::Panic(msg) => panic!("{}", msg),
        }
    }
}

pub fn eval_val(val: &Value, env: Env) -> Answer {
    match val {
        Value::Var(v) => env.lookup(v),
        Value::Int(x) => Answer::from_int(*x),
        Value::Real(x) => Answer::from_float(*x),
        Value::String(s) => Answer::from_str(*s),
        Value::Halt => Answer::from_ref(Ref::new(Closure {
            captured_env: Env::Empty,
            params: Ref::array(vec!["x".into()]),
            body: Expr::App(Value::Halt, Ref::array(vec![Value::Var("x".into())])).into(),
        })),
    }
}

struct Closure {
    captured_env: Env,
    params: Ref<[Ref<str>]>,
    body: Ref<Expr>,
}
