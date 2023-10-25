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
    all_registers: Ref<[Ref<str>]>,
    available_registers: BinaryHeap<Reverse<Ref<str>>>,
    env: Env,
}

impl AllocationContext {
    pub fn new(n_registers: usize) -> Self {
        let all_registers: Vec<_> = (0..n_registers)
            .map(|r| Ref::from(format!("r{r}")))
            .collect();
        AllocationContext {
            available_registers: all_registers.iter().copied().map(Reverse).collect(),
            all_registers: Ref::array(all_registers),
            env: Env::new(),
        }
    }

    pub fn fresh(&self) -> Self {
        AllocationContext {
            all_registers: self.all_registers,
            available_registers: self.all_registers.iter().copied().map(Reverse).collect(),
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

            Expr::Offset(idx, rec, var, cnt) => {
                let rec_out = ctx_before.transform_value(rec);
                let (r, ctx_after) = ctx_after.assign_register(var);
                Expr::Offset(*idx, rec_out, r, Ref::new(ctx_after.allocate(cnt)))
            }

            Expr::App(rator, rands) => Expr::App(
                ctx_before.transform_value(rator),
                Ref::array(
                    rands
                        .iter()
                        .map(|a| ctx_before.transform_value(a))
                        .collect(),
                ),
            ),

            Expr::Fix(defs, cnt) => {
                let mut defs_out = vec![];
                for (f, ps, bdy) in defs.iter() {
                    let mut ctx_fn = ctx_before.fresh();
                    let mut p_out = vec![];
                    for p in ps.iter() {
                        let (r, ctx_) = ctx_fn.assign_register(p);
                        ctx_fn = ctx_;
                        p_out.push(r);
                    }
                    let b_out = ctx_fn.allocate(bdy);
                    defs_out.push((*f, Ref::array(p_out), Ref::new(b_out)))
                }
                Expr::Fix(Ref::array(defs_out), Ref::new(ctx_after.allocate(cnt)))
            }

            Expr::Switch(val, cnts) => {
                let val_out = ctx_before.transform_value(val);

                let cnts_out: Vec<_> = cnts
                    .iter()
                    .map(|c| ctx_after.clone().allocate(c))
                    .map(Ref::new)
                    .collect();

                Expr::Switch(val_out, Ref::array(cnts_out))
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

            Expr::Panic(msg) => Expr::Panic(*msg),
        }
    }

    fn transform_value(&self, value: &Value<Ref<str>>) -> Value<Ref<str>> {
        match value {
            Value::Var(v) => Value::Var(
                self.env
                    .get(v)
                    .unwrap_or_else(|| panic!("unbound variable {v:?}"))
                    .clone(),
            ),
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
            all_registers: self.all_registers,
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

    #[test]
    fn unused_variables_give_back_their_registers() {
        let x = Expr::from_str("(record () a (offset 0 a b (offset 0 b c (halt c))))").unwrap();
        let y =
            Expr::from_str("(record () r0 (offset 0 r0 r0 (offset 0 r0 r0 (halt r0))))").unwrap();
        assert_eq!(allocate(2, &x), y);
    }

    #[test]
    fn register_usage_considers_all_switch_branches() {
        let x =
            Expr::from_str("(record () a (offset 0 a b (switch 0 (halt b) (halt a))))").unwrap();
        let y = Expr::from_str("(record () r0 (offset 0 r0 r1 (switch 0 (halt r1) (halt r0))))")
            .unwrap();
        assert_eq!(allocate(2, &x), y);
    }

    #[test]
    fn functions_allocated_independently() {
        let x = Expr::from_str("(fix ((f (x) (halt x)) (g (k x) (k x))) ((@ g) (@ f) 0))").unwrap();
        let y = Expr::from_str("(fix ((f (r0) (halt r0)) (g (r0 r1) (r0 r1))) ((@ g) (@ f) 0))")
            .unwrap();
        assert_eq!(allocate(2, &x), y);
    }
}
