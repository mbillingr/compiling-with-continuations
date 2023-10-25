use crate::core::reference::Ref;
use crate::core::sets::Set;
use crate::languages::cps_lang::ast::{Expr, Value};
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

pub fn allocate(n_registers: usize, expr: &Expr<Ref<str>>) -> Expr<Ref<str>> {
    let ctx = AllocationContext::new(n_registers);
    ctx.allocate(expr)
}

#[derive(Debug, Clone)]
struct AllocationContext {
    available_registers: BinaryHeap<Reverse<Ref<str>>>,
    env: Env,
}

impl AllocationContext {
    pub fn new(n_registers: usize) -> Self {
        AllocationContext {
            available_registers: (0..n_registers)
                .map(|r| Ref::from(format!("r{r}")))
                .map(Reverse)
                .collect(),
            env: Env::new(),
        }
    }

    fn allocate(self, expr: &Expr<Ref<str>>) -> Expr<Ref<str>> {
        let ctx_before = self;
        println!("{expr:?}");
        println!("    {ctx_before:?}");
        let free_after = expr
            .continuation_exprs()
            .into_iter()
            .map(Expr::free_vars)
            .map(Set::from)
            .reduce(|x, y| x.union(&y))
            .unwrap_or(Set::empty());
        let ctx_after = ctx_before.free_unused_registers(free_after);
        println!("    {ctx_after:?}");

        match expr {
            Expr::Record(fields, var, cnt) => {
                let fields_out = fields
                    .iter()
                    .map(|(f, ap)| (ctx_before.transform_value(f), ap.clone()))
                    .collect();
                let (r, ctx_after) = ctx_after.assign_register(var);
                Expr::Record(Ref::array(fields_out), r, Ref::new(ctx_after.allocate(cnt)))
            }

            Expr::Select(idx, rec, var, cnt) => {
                let rec_out = ctx_before.transform_value(rec);
                let (r, ctx_after) = ctx_after.assign_register(var);
                Expr::Select(*idx, rec_out, r, Ref::new(ctx_after.allocate(cnt)))
            }

            Expr::PrimOp(op, args, vars, cnts) => {
                let args_out: Vec<_> = args.iter().map(|a| ctx_before.transform_value(a)).collect();

                let mut ctx_after = ctx_after;
                let mut vars_out = vec![];
                for v in vars.iter() {
                    let (r, ctx_) = ctx_after.assign_register(v);
                    ctx_after = ctx_;
                    vars_out.push(r);
                }

                let cnts_out: Vec<_> = cnts
                    .iter()
                    .map(|c| ctx_after.clone().allocate(c))
                    .map(Ref::new)
                    .collect();

                Expr::PrimOp(
                    *op,
                    Ref::array(args_out),
                    Ref::array(vars_out),
                    Ref::array(cnts_out),
                )
            }

            Expr::Halt(value) => Expr::Halt(ctx_before.transform_value(value)),

            _ => todo!("{expr:?}"),
        }
    }

    fn transform_value(&self, value: &Value<Ref<str>>) -> Value<Ref<str>> {
        match value {
            Value::Var(v) => Value::Var(self.env.get(v).expect("unbound variable").clone()),
            _ => value.clone(),
        }
    }

    fn assign_register(mut self, var: &Ref<str>) -> (Ref<str>, Self) {
        let r = self.available_registers.pop().unwrap().0;
        self.env.insert(var.clone(), r);
        (r, self)
    }

    fn free_unused_registers(&self, free_vars: Set<Ref<str>>) -> Self {
        let mut available_registers = self.available_registers.clone();

        let mut env = Env::new();
        for (k, v) in self.env.iter() {
            if free_vars.contains(k) {
                env.insert(*k, *v);
            } else {
                available_registers.push(Reverse(*v));
            }
        }

        AllocationContext {
            available_registers,
            env,
        }
    }
}

type Env = HashMap<Ref<str>, Ref<str>>;

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
