use crate::languages::cps_lang::ast::compute::{Computation, Compute};
use crate::languages::cps_lang::ast::{Expr, Value};
use std::collections::HashMap;
use std::hash::Hash;

impl<V: Clone, F: Clone + Eq + Hash> Expr<V, F> {
    pub fn collect_all_functions(&self) -> HashMap<F, FnInfo<'_, V, F>> {
        let mut fnc = FnCollect(Default::default());
        fnc.compute_for_expr(self);
        fnc.0
    }
}

pub struct FnInfo<'a, V: 'static, F: 'static> {
    pub n_app: usize,
    pub n_ref: usize,
    pub params: &'a [V],
    pub body: &'a Expr<V, F>,
}

struct FnCollect<'a, V: 'static, F: 'static>(HashMap<F, FnInfo<'a, V, F>>);

impl<'e, V: Clone, F: Clone + Eq + Hash> Compute<'e, V, F> for FnCollect<'e, V, F> {
    fn visit_expr(&mut self, expr: &'e Expr<V, F>) -> Computation {
        match expr {
            Expr::Fix(defs, cnt) => {
                for (f, p, b) in defs.iter() {
                    self.0.insert(
                        f.clone(),
                        FnInfo {
                            n_app: 0,
                            n_ref: 0,
                            params: p,
                            body: b,
                        },
                    );
                    self.compute_for_expr(b);
                }
                self.compute_for_expr(cnt);
                Computation::Done
            }

            Expr::App(Value::Label(f), args) => {
                if let Some(fninfo) = self.0.get_mut(f) {
                    fninfo.n_app += 1;
                    self.compute_for_values(args);
                }
                Computation::Done
            }

            _ => Computation::Continue,
        }
    }

    fn visit_value(&mut self, value: &Value<V, F>) {
        match value {
            Value::Label(f) => self.0.get_mut(f).unwrap().n_ref += 1,
            _ => {}
        }
    }

    fn post_visit_expr(&mut self, _: &Expr<V, F>) {}
}
