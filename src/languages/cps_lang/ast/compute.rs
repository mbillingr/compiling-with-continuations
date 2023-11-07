use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{AccessPath, Expr, List, Value};

pub trait Compute<'e, V, F = V> {
    fn visit_expr(&mut self, expr: &'e Expr<V, F>) -> Computation;
    fn visit_value(&mut self, value: &Value<V, F>);
    fn post_visit_expr(&mut self, expr: &'e Expr<V, F>);

    fn compute_for_expr(&mut self, expr: &'e Expr<V, F>)
    where
        Self: Sized,
    {
        expr.compute(self)
    }

    fn compute_for_value(&mut self, val: &'e Value<V, F>)
    where
        Self: Sized,
    {
        val.compute(self)
    }

    fn compute_for_exprs(&mut self, exprs: &'e List<Ref<Expr<V, F>>>)
    where
        Self: Sized,
    {
        for v in exprs.iter() {
            self.compute_for_expr(v)
        }
    }

    fn compute_for_values(&mut self, values: &'e List<Value<V, F>>)
    where
        Self: Sized,
    {
        for v in values.iter() {
            self.compute_for_value(v)
        }
    }

    fn compute_for_fields(&mut self, fields: &'e List<(Value<V, F>, AccessPath)>)
    where
        Self: Sized,
    {
        for (f, _) in fields.iter() {
            self.compute_for_value(f)
        }
    }
}

pub enum Computation {
    /// Recur into children
    Continue,

    /// Don't recur, return result
    Done,
}

impl<V, F> Expr<V, F> {
    pub fn compute<'e>(&'e self, comp: &mut impl Compute<'e, V, F>) {
        match comp.visit_expr(self) {
            Computation::Continue => {}
            Computation::Done => return,
        }

        match self {
            Expr::Record(fields, _, cnt) => {
                comp.compute_for_fields(fields);
                comp.compute_for_expr(cnt);
            }

            Expr::Select(_, rec, _, cnt) => {
                rec.compute(comp);
                cnt.compute(comp);
            }

            Expr::Offset(_, rec, _, cnt) => {
                rec.compute(comp);
                cnt.compute(comp);
            }

            Expr::App(rator, rands) => {
                rator.compute(comp);
                comp.compute_for_values(rands);
            }

            Expr::Fix(defs, cnt) => {
                for (_, _, body) in defs.iter() {
                    body.compute(comp);
                }
                cnt.compute(comp);
            }

            Expr::Switch(val, cnts) => {
                val.compute(comp);
                comp.compute_for_exprs(cnts);
            }

            Expr::PrimOp(_, args, _, cnts) => {
                comp.compute_for_values(args);
                comp.compute_for_exprs(cnts);
            }

            Expr::Halt(value) => value.compute(comp),

            Expr::Panic(_) => {}
        }

        comp.post_visit_expr(self)
    }
}

impl<V, F> Value<V, F> {
    pub fn compute<'e>(&'e self, comp: &mut impl Compute<'e, V, F>) {
        comp.visit_value(self);
    }
}
