use crate::core::answer::Answer;
use crate::core::env::Env;
use crate::core::reference::Ref;
use crate::languages::mini_lambda::ast;
use crate::languages::mini_lambda::ast::{Con, ConRep};
use std::io::{BufRead, Write};

type Expr = ast::Expr<Ref<str>>;

pub struct Closure {
    captured_env: Env,
    var: Ref<str>,
    body: Ref<Expr>,
}

pub unsafe fn exec(expr: &Expr, out: &mut impl Write, inp: &mut impl BufRead) {
    eval(expr, Env::Empty, out, inp);
}

pub unsafe fn eval(
    mut expr: &Expr,
    mut env: Env,
    out: &mut impl Write,
    inp: &mut impl BufRead,
) -> Answer {
    loop {
        match expr {
            Expr::Var(v) => return env.lookup(&**v),

            Expr::Fn(var, body) => {
                return Answer::from_ref(Ref::new(Closure {
                    captured_env: env.clone(),
                    var: *var,
                    body: *body,
                }))
            }

            Expr::Fix(fnames, funcs, body) => {
                let closures: Vec<_> = funcs
                    .iter()
                    .map(|f| {
                        if let Expr::Fn(var, body) = *f {
                            Closure {
                                captured_env: Env::Empty, //placeholder
                                var,
                                body,
                            }
                        } else {
                            panic!("not a function")
                        }
                    })
                    .map(Ref::new)
                    .collect();

                let mut common_env = env.clone();
                for (name, cls) in fnames.iter().zip(&closures) {
                    common_env = common_env.extend(*name, Answer::from_ref(*cls));
                }

                for cls in closures.into_iter() {
                    cls.unsafe_mutate(|cls| cls.captured_env = common_env);
                }

                expr = body;
                env = common_env;
            }

            Expr::App(rator, rand) => match (&**rator, &**rand) {
                (Expr::Prim(op), _) if op.n_args() == 1 => {
                    return op.apply(vec![eval(&**rand, env, out, inp)], out, inp)
                }
                (Expr::Prim(op), Expr::Record(args)) => {
                    let args = (0..op.n_args())
                        .map(|i| eval(&args[i], env, out, inp))
                        .collect();
                    return op.apply(args, out, inp);
                }
                (Expr::Prim(op), _) => {
                    let arg = eval(rand, env, out, inp);
                    return op.apply(
                        (0..op.n_args()).map(|i| arg.get_item(i as isize)).collect(),
                        out,
                        inp,
                    );
                }
                _ => {
                    let f = eval(&**rator, env, out, inp);
                    let a = eval(&**rand, env, out, inp);
                    let cls = f.as_ref::<Closure>();
                    env = cls.captured_env.extend(cls.var, a);
                    expr = &cls.body;
                }
            },

            Expr::Int(i) => return Answer::from_int(*i),

            Expr::Real(r) => return Answer::from_float(*r),

            Expr::String(s) => return Answer::from_str(*s),

            Expr::Switch(x, _conrep, branches, default) => {
                let val = eval(x, env, out, inp);
                let mut cont = None;
                for (cnd, branch) in &**branches {
                    if matches(val, cnd) {
                        cont = Some(branch);
                        break;
                    }
                }
                if let Some(c) = cont {
                    expr = c;
                } else {
                    expr = default.as_ref().unwrap();
                }
            }

            Expr::Con(ConRep::Tagged(tag), val) => {
                return Answer::tuple(vec![eval(val, env, out, inp), Answer::from_usize(*tag)])
            }

            Expr::DeCon(ConRep::Tagged(tag), val) => {
                let value = eval(val, env, out, inp);
                if value.get_item(1).as_usize() != *tag {
                    panic!(
                        "expected tag {}, but got {}",
                        tag,
                        value.get_item(1).as_usize()
                    )
                }
                return value.get_item(0);
            }

            Expr::Con(ConRep::Constant(tag), _value) => {
                // the value is ignored
                return Answer::tag(*tag);
            }

            Expr::DeCon(ConRep::Constant(_), _) => {
                panic!("Cannot deconstruct a constant")
            }

            Expr::Con(ConRep::Transparent, val) => {
                expr = val;
            }

            Expr::DeCon(ConRep::Transparent, val) => {
                expr = val;
            }

            Expr::Record(fields) => {
                let mut data = Vec::with_capacity(fields.len());
                for f in &**fields {
                    data.push(eval(f, env, out, inp));
                }
                return Answer::tuple(data);
            }

            Expr::Select(idx, rec) => return eval(rec, env, out, inp).get_item(*idx),

            Expr::ShowInt(value) => {
                let v = eval(value, env, out, inp);
                write!(out, "{}", v.as_int()).unwrap();
                return v;
            }
            Expr::ShowReal(value) => {
                let v = eval(value, env, out, inp);
                write!(out, "{}", v.as_float()).unwrap();
                return v;
            }
            Expr::ShowStr(value) => {
                let v = eval(value, env, out, inp);
                write!(out, "{}", v.as_str()).unwrap();
                return v;
            }

            Expr::Prim(_) => {
                let var: Ref<str> = "_x_".into();
                return Answer::from_ref(Ref::new(Closure {
                    captured_env: Env::Empty,
                    var,
                    body: Ref::new(Expr::App(expr.clone().into(), Expr::Var(var).into())),
                }));
            }

            Expr::Panic(msg) => panic!("{}", msg),
        }
    }
}

unsafe fn matches(val: Answer, con: &Con) -> bool {
    match con {
        Con::Data(ConRep::Constant(tag)) => val.maybe_tag() && (val.as_tag() == *tag),
        Con::Data(ConRep::Tagged(tag)) => {
            val.maybe_pointer() && (val.get_item(1).as_usize() == *tag)
        }
        Con::Data(ConRep::Transparent) => true,
        Con::Int(c) => val.as_int() == *c,
        Con::Real(c) => val.as_float() == *c,
        Con::String(s) => val.as_str().as_str() == &**s,
    }
}
