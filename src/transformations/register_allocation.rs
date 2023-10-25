use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Value};

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

    fn allocate(&self, expr: &Expr<Ref<str>>, env: Env) -> Expr<Ref<str>> {
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
            _ => todo!(),
        }
    }

    fn transform_value(&self, value: &Value<Ref<str>>, env: Env) -> Value<Ref<str>> {
        match value {
            Value::Var(v) => Value::Var(env.lookup(v)),
            _ => value.clone(),
        }
    }

    fn assign_register<V>(&self, var: &V, env: Env) -> (Ref<str>, Env) {
        (self.register_names[0], env)
    }
}

type Env = Environment<Ref<str>, Ref<str>>;

#[derive(Debug, Copy, Clone)]
enum Environment<K: 'static, V: 'static> {
    Empty,
    Binding(Ref<(K, V, Self)>),
}

impl<K, V> Environment<K, V> {
    fn lookup<T>(&self, k: T) -> V {
        todo!()
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
}
