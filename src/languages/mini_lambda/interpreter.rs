use crate::core::reference::Ref;
use crate::languages::mini_lambda::ast;

type Expr = ast::Expr<Ref<str>>;

#[derive(Debug, Copy, Clone)]
pub struct Value(usize);

impl Value {
    pub fn from_int(i: i64) -> Self {
        unsafe { Value(std::mem::transmute(i)) }
    }

    pub fn from_ref<T>(r: Ref<T>) -> Self {
        unsafe { Value(std::mem::transmute(r.as_ptr())) }
    }

    pub fn tuple(fields: Vec<Value>) -> Self {
        let obj = Box::leak(fields.into_boxed_slice());
        let fst = &obj[0] as *const _;
        unsafe { Value(std::mem::transmute(fst)) }
    }

    pub fn as_int(&self) -> i64 {
        unsafe { std::mem::transmute(self.0) }
    }

    pub unsafe fn as_ref<T>(self) -> &'static T {
        let ptr: *const T = std::mem::transmute(self.0);
        &*ptr
    }

    pub unsafe fn get_item(self, idx: isize) -> Value {
        let fst: *const Value = std::mem::transmute(self.0);
        *fst.offset(idx)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Env {
    Empty,
    Entry(Ref<str>, Value, Ref<Env>),
}

impl Env {
    fn extend(&self, var: Ref<str>, val: Value) -> Self {
        Env::Entry(var, val, Ref::new(self.clone()))
    }

    fn lookup(&self, var: &str) -> Value {
        let mut env = self;
        loop {
            match env {
                Env::Empty => panic!("Unbound variable: {var}"),
                Env::Entry(v, val, _) if &**v == var => return *val,
                Env::Entry(_, _, next) => env = next,
            }
        }
    }
}

pub struct Closure {
    captured_env: Env,
    var: Ref<str>,
    body: Ref<Expr>,
}

pub unsafe fn exec(expr: &Expr) -> Value {
    eval(expr, Env::Empty)
}

pub unsafe fn eval(mut expr: &Expr, mut env: Env) -> Value {
    loop {
        match expr {
            Expr::Var(v) => return env.lookup(&**v),

            Expr::Fn(var, body) => {
                return Value::from_ref(Ref::new(Closure {
                    captured_env: env.clone(),
                    var: *var,
                    body: *body,
                }))
            }

            Expr::App(rator, rand) => {
                let f = eval(&**rator, env);
                let a = eval(&**rand, env);
                let cls = f.as_ref::<Closure>();
                env = cls.captured_env.extend(cls.var, a);
                expr = &cls.body;
            }

            Expr::Int(i) => return Value::from_int(*i),

            Expr::Record(fields) => {
                let mut data = Vec::with_capacity(fields.len());
                for f in &**fields {
                    data.push(eval(f, env));
                }
                return Value::tuple(data);
            }

            Expr::Select(idx, rec) => return eval(rec, env).get_item(*idx),

            _ => todo!("{:?}", expr),
        }
    }
}
