use crate::languages::cps_lang::ast::{Computation, Compute, Expr, Value};

impl<V, F> Expr<V, F> {
    pub fn size(&self) -> usize {
        let mut s = Size(0);
        self.compute(&mut s);
        s.0
    }
}

struct Size(usize);

impl<'e, V, F> Compute<'e, V, F> for Size {
    fn visit_expr(&mut self, _: &'e Expr<V, F>) -> Computation {
        Computation::Continue
    }

    fn visit_value(&mut self, _: &Value<V, F>) {}

    fn post_visit_expr(&mut self, _: &'e Expr<V, F>) {
        self.0 += 1;
    }
}
