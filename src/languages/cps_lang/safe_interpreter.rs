use crate::core::reference::Ref;
use crate::languages::common_primops::PrimOp;
use crate::languages::cps_lang::ast;
use crate::languages::cps_lang::ast::{Expr, Value};
use std::io::Write;

pub fn exec<V: Clone + Eq, F: Clone + Eq>(expr: &Expr<V, F>, out: &mut impl Write) -> Answer<V, F> {
    eval_expr(expr, Env::Empty, out)
}

pub fn eval_expr<V: Clone + Eq, F: Clone + Eq>(
    mut expr: &Expr<V, F>,
    mut env: Env<V, F>,
    out: &mut impl Write,
) -> Answer<V, F> {
    loop {
        match expr {
            Expr::Record(items, outvar, cnt) => {
                let mut data = Vec::with_capacity(items.len());
                for (item, ap) in &**items {
                    let val = eval_val(item, env);
                    data.push(resolve_accesspath(val, ap));
                }
                env = env.extend_var(outvar.clone(), Answer::record(data));
                expr = cnt;
            }

            Expr::Offset(idx, recval, outvar, cnt) => {
                let rec = eval_val(recval, env);
                env = env.extend_var(outvar.clone(), rec.ptr_offset(*idx));
                expr = cnt;
            }

            Expr::Select(idx, recval, outvar, cnt) => {
                let rec = eval_val(recval, env);
                env = env.extend_var(outvar.clone(), rec.get_item(*idx));
                expr = cnt;
            }

            Expr::App(fval, argvals) => {
                let f = eval_val(fval, env);
                let cls = f.as_closure().as_ref();
                assert_eq!(argvals.len(), cls.params.len());

                let args = argvals.iter().map(move |a| eval_val(a, env));

                env = cls.captured_env;
                for (a, v) in args.zip(&*cls.params) {
                    env = env.extend_var(v.clone(), a);
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
                    common_env = common_env.extend_fun(name.clone(), Answer::Closure(cls.clone()));
                }

                for cls in closures.into_iter() {
                    unsafe { cls.unsafe_mutate(|cls| cls.captured_env = common_env) }
                }

                env = common_env;
                expr = cnt;
            }

            Expr::Switch(val, cnts) => {
                let idx = eval_val(val, env).as_int();
                expr = &cnts[idx as usize];
            }

            Expr::PrimOp(op, args, vars, cnts) => {
                let x: Vec<_> = (0..op.n_args()).map(|i| eval_val(&args[i], env)).collect();
                match op {
                    PrimOp::CorP => match x[0] {
                        Answer::Record(_, _) => expr = &cnts[1],
                        _ => expr = &cnts[0],
                    },
                    PrimOp::Untag => {
                        env = env.extend_var(vars[0].clone(), Answer::Int((x[0].as_int() - 1) / 2));
                        expr = &cnts[0];
                    }
                    PrimOp::IsZero => {
                        if x[0].as_int() == 0 {
                            expr = &cnts[1];
                        } else {
                            expr = &cnts[0];
                        }
                    }
                    PrimOp::ISame => {
                        if x[0].as_int() == x[1].as_int() {
                            expr = &cnts[1];
                        } else {
                            expr = &cnts[0];
                        }
                    }
                    PrimOp::ILess => {
                        if x[0].as_int() < x[1].as_int() {
                            expr = &cnts[1];
                        } else {
                            expr = &cnts[0];
                        }
                    }
                    PrimOp::INeg => {
                        env = env.extend_var(vars[0].clone(), Answer::Int(-x[0].as_int()));
                        expr = &cnts[0];
                    }
                    PrimOp::IAdd => {
                        env = env.extend_var(
                            vars[0].clone(),
                            Answer::Int(x[0].as_int() + x[1].as_int()),
                        );
                        expr = &cnts[0];
                    }
                    PrimOp::ISub => {
                        env = env.extend_var(
                            vars[0].clone(),
                            Answer::Int(x[0].as_int() - x[1].as_int()),
                        );
                        expr = &cnts[0];
                    }
                    PrimOp::IMul => {
                        env = env.extend_var(
                            vars[0].clone(),
                            Answer::Int(x[0].as_int() * x[1].as_int()),
                        );
                        expr = &cnts[0];
                    }
                    PrimOp::IDiv => {
                        env = env.extend_var(
                            vars[0].clone(),
                            Answer::Int(x[0].as_int() / x[1].as_int()),
                        );
                        expr = &cnts[0];
                    }
                    PrimOp::FSame => {
                        if x[0].as_float() == x[1].as_float() {
                            expr = &cnts[1];
                        } else {
                            expr = &cnts[0];
                        }
                    }
                    PrimOp::SSame => {
                        if x[0].as_str() == x[1].as_str() {
                            expr = &cnts[1];
                        } else {
                            expr = &cnts[0];
                        }
                    }
                    PrimOp::ShowInt => {
                        write!(out, "{}", x[0].as_int()).unwrap();
                        env = env.extend_var(vars[0].clone(), x[0].clone());
                        expr = &cnts[0];
                    }
                    PrimOp::ShowReal => {
                        write!(out, "{}", x[0].as_float()).unwrap();
                        env = env.extend_var(vars[0].clone(), x[0].clone());
                        expr = &cnts[0];
                    }
                    PrimOp::ShowStr => {
                        write!(out, "{}", x[0].as_str()).unwrap();
                        env = env.extend_var(vars[0].clone(), x[0].clone());
                        expr = &cnts[0];
                    }
                    _ => todo!("{:?}", op),
                }
            }

            Expr::Halt(v) => return eval_val(v, env),

            Expr::Panic(msg) => panic!("{}", msg),
        }
    }
}

pub fn eval_val<V: Clone + Eq, F: Clone + Eq>(val: &Value<V, F>, env: Env<V, F>) -> Answer<V, F> {
    match val {
        Value::Var(v) => env.lookup_var(v),
        Value::Label(v) => env.lookup_fun(v),
        Value::Int(x) => Answer::Int(*x),
        Value::Real(x) => Answer::Float(*x),
        Value::String(s) => Answer::String(*s),
    }
}

fn resolve_accesspath<V: Clone, F: Clone>(val: Answer<V, F>, ap: &ast::AccessPath) -> Answer<V, F> {
    match ap {
        ast::AccessPath::Ref(0) => val,
        ast::AccessPath::Ref(i) => val.ptr_offset(*i),
        ast::AccessPath::Sel(i, ap) => resolve_accesspath(val.get_item(*i), ap),
    }
}

#[derive(Debug)]
pub enum Env<V: 'static, F: 'static> {
    Empty,
    Var(Ref<(V, Answer<V, F>, Self)>),
    Fun(Ref<(F, Answer<V, F>, Self)>),
}

impl<V, F> Copy for Env<V, F> {}
impl<V, F> Clone for Env<V, F> {
    fn clone(&self) -> Self {
        match self {
            Env::Empty => Env::Empty,
            Env::Var(e) => Env::Var(*e),
            Env::Fun(e) => Env::Fun(*e),
        }
    }
}

impl<V: Clone + PartialEq, F: Clone + PartialEq> Env<V, F> {
    fn extend_var(&self, var: V, val: Answer<V, F>) -> Self {
        Env::Var(Ref::new((var, val, *self)))
    }
    fn extend_fun(&self, fun: F, val: Answer<V, F>) -> Self {
        Env::Fun(Ref::new((fun, val, *self)))
    }

    fn lookup_var(&self, var: &V) -> Answer<V, F> {
        match self {
            Env::Empty => panic!("unknown variable"),
            Env::Var(Ref((v, val, _))) if v == var => val.clone(),
            Env::Var(Ref((_, _, next))) => next.lookup_var(var),
            Env::Fun(Ref((_, _, next))) => next.lookup_var(var),
        }
    }

    fn lookup_fun(&self, fun: &F) -> Answer<V, F> {
        match self {
            Env::Empty => panic!("unknown function"),
            Env::Fun(Ref((f, val, _))) if f == fun => val.clone(),
            Env::Fun(Ref((_, _, next))) => next.lookup_fun(fun),
            Env::Var(Ref((_, _, next))) => next.lookup_fun(fun),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Answer<V: 'static, F: 'static> {
    Int(i64),
    Float(f64),
    String(Ref<String>),
    Record(isize, Ref<Vec<Self>>),
    Closure(Ref<Closure<V, F>>),
}

impl<V: Clone, F: Clone> Answer<V, F> {
    fn record(fields: Vec<Self>) -> Self {
        Answer::Record(0, Ref::new(fields))
    }
    fn ptr_offset(&self, idx: isize) -> Self {
        match self {
            Answer::Record(ofs, fields) => Answer::Record(ofs + idx, fields.clone()),
            _ => panic!("Expected Record"),
        }
    }
    fn get_item(&self, idx: isize) -> Self {
        match self {
            Answer::Record(ofs, fields) => fields[(ofs + idx) as usize].clone(),
            _ => panic!("Expected Record"),
        }
    }

    fn as_closure(&self) -> Ref<Closure<V, F>> {
        match self {
            Answer::Closure(cls) => *cls,
            _ => panic!("Expected Closure"),
        }
    }

    fn as_int(&self) -> i64 {
        match self {
            Answer::Int(i) => *i,
            _ => panic!("Expected Integer"),
        }
    }

    fn as_float(&self) -> f64 {
        match self {
            Answer::Float(i) => *i,
            _ => panic!("Expected Float"),
        }
    }

    fn as_str(&self) -> &str {
        match self {
            Answer::String(s) => &**s,
            _ => panic!("Expected Float"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Closure<V: 'static, F: 'static> {
    captured_env: Env<V, F>,
    params: Ref<[V]>,
    body: Ref<Expr<V, F>>,
}
