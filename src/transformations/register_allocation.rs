use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Value};
use std::borrow::Borrow;

pub fn allocate(n_registers: usize, expr: &Expr<Ref<str>>) -> Expr<Ref<str>> {
    let ctx = AllocationContext::new(n_registers);
    ctx.allocate(expr, Env::Empty)
}

struct AllocationContext {
    register_names: Vec<Ref<str>>,
}

impl AllocationContext {
    pub fn new(n_registers: usize) -> Self {
        AllocationContext {
            register_names: (0..n_registers)
                .map(|r| Ref::from(format!("r{r}")))
                .collect(),
        }
    }

    fn allocate(&self, expr: &Expr<Ref<str>>, mut env: Env) -> Expr<Ref<str>> {
        match expr {
            Expr::Record(fields, var, cnt) => {
                let (r, env) = self.assign_register(var, env);
                Expr::Record(
                    Ref::array(
                        fields
                            .iter()
                            .map(|(f, ap)| (self.transform_value(f, env), ap.clone()))
                            .collect(),
                    ),
                    r,
                    Ref::new(self.allocate(cnt, env)),
                )
            }

            Expr::Select(idx, rec, var, cnt) => {
                let (r, env) = self.assign_register(var, env);
                Expr::Select(
                    *idx,
                    self.transform_value(rec, env),
                    r,
                    Ref::new(self.allocate(cnt, env)),
                )
            }

            Expr::PrimOp(op, args, vars, cnts) => {
                let args_out: Vec<_> = args.iter().map(|a| self.transform_value(a, env)).collect();

                let mut vars_out = vec![];
                for v in vars.iter() {
                    let (r, env_) = self.assign_register(v, env);
                    env = env_;
                    vars_out.push(r);
                }

                let cnts_out: Vec<_> = cnts
                    .iter()
                    .map(|c| self.allocate(c, env))
                    .map(Ref::new)
                    .collect();

                Expr::PrimOp(
                    *op,
                    Ref::array(args_out),
                    Ref::array(vars_out),
                    Ref::array(cnts_out),
                )
            }

            Expr::Halt(value) => Expr::Halt(self.transform_value(value, env)),

            _ => todo!("{expr:?}"),
        }
    }

    fn transform_value(&self, value: &Value<Ref<str>>, env: Env) -> Value<Ref<str>> {
        match value {
            Value::Var(v) => Value::Var(env.lookup(v).clone()),
            _ => value.clone(),
        }
    }

    fn assign_register(&self, var: &Ref<str>, env: Env) -> (Ref<str>, Env) {
        let r = self.register_names[0];
        (r, env.extend(var.clone(), r))
    }
}

type Env = Environment<Ref<str>, Ref<str>>;

#[derive(Debug)]
enum Environment<K: 'static, V: 'static> {
    Empty,
    Binding(Ref<(K, V, Self)>),
}

impl<K, V> Copy for Environment<K, V> {}

impl<K, V> Clone for Environment<K, V> {
    fn clone(&self) -> Self {
        match self {
            Environment::Empty => Environment::Empty,
            Environment::Binding(b) => Environment::Binding(*b),
        }
    }
}

impl<K, V> Environment<K, V> {
    fn extend(&self, key: K, value: V) -> Self {
        Environment::Binding(Ref::new((key, value, *self)))
    }

    fn lookup<T>(&self, key: T) -> &V
    where
        K: PartialEq,
        T: Borrow<K>,
    {
        match self {
            Environment::Empty => panic!("Key not found"),
            Environment::Binding(Ref((k, v, _))) if k == key.borrow() => v,
            Environment::Binding(Ref((_, _, next))) => next.lookup(key),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn fail_allocation() {
        allocate(
            1,
            &Expr::from_str(
                "(record (1 2) r (select 0 r a (select 1 r b (primop + (a b) (c) ((halt c))))))",
            )
            .unwrap(),
        );
    }

    #[test]
    fn simple_allocate() {
        let x = Expr::from_str("(record (1 2) r (halt r))").unwrap();
        let y = Expr::from_str("(record (1 2) r0 (halt r0))").unwrap();
        assert_eq!(allocate(1, &x), y);
    }

    #[test]
    fn allocate_multiple_registers() {
        let x = Expr::from_str(
            "(record (1 2) r (select 0 r a (select 1 r b (primop + (a b) (c) ((halt c))))))",
        )
        .unwrap();
        let y = Expr::from_str(
            "(record (1 2) r0 (select 0 r0 r1 (select 1 r0 r0 (primop + (r1 r0) (r0) ((halt r0))))))",
        )
        .unwrap();
        assert_eq!(allocate(2, &x), y);
    }
}
