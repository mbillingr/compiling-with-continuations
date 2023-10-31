use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Transform, Transformed, Value};
use crate::transformations::{GenSym, GensymContext};
use std::fmt::Display;
use std::sync::Arc;

pub struct Context {
    gs: Arc<GensymContext>,
}

impl Context {
    pub fn new(gs: Arc<GensymContext>) -> Self {
        Context { gs }
    }
}

impl<V: Clone, F: Clone + GenSym + Display> Transform<V, F> for Context {
    fn visit_expr(&mut self, expr: &Expr<V, F>) -> Transformed<Expr<V, F>> {
        match expr {
            Expr::Fix(defs, body) => {
                let mut defs_out = vec![];
                for (f, p, b) in defs.iter() {
                    let f_: F = self.gs.gensym(f);
                    defs_out.push((
                        f.clone(),
                        *p,
                        Ref::new(Expr::App(
                            Value::Label(f_.clone()),
                            Ref::array(p.iter().map(|a| Value::Var(a.clone())).collect()),
                        )),
                    ));
                    defs_out.push((f_, *p, *b));
                }

                Transformed::Done(Expr::Fix(
                    Ref::array(defs_out),
                    Ref::new(self.transform_expr(body)),
                ))
            }
            _ => Transformed::Continue,
        }
    }

    fn visit_value(&mut self, _: &Value<V, F>) -> Transformed<Value<V, F>> {
        Transformed::Continue
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn eta_split(exp: Expr<Ref<str>>) -> Expr<Ref<str>> {
        Context::new(Arc::new(GensymContext::new("__"))).transform_expr(&exp)
    }

    #[test]
    fn simple_split() {
        let x = Expr::from_str("(fix ((foo () (halt 0))) (foo))").unwrap();
        let y = Expr::from_str("(fix ((foo () ((@ foo__0))) (foo__0 () (halt 0))) (foo))").unwrap();
        assert_eq!(eta_split(x), y);
    }

    #[test]
    fn func_with_args() {
        let x = Expr::from_str("(fix ((foo (a b c) (halt 0))) (foo 1 2 3))").unwrap();
        let y = Expr::from_str(
            "(fix ((foo (a b c) ((@ foo__0) a b c)) (foo__0 (a b c) (halt 0))) (foo 1 2 3))",
        )
        .unwrap();
        assert_eq!(eta_split(x), y);
    }

    #[test]
    fn split_multiple_functions() {
        let x = Expr::from_str("(fix ((foo () (halt 0)) (bar () (halt 1))) (foo))").unwrap();
        let y = Expr::from_str("(fix ((foo () ((@ foo__0))) (foo__0 () (halt 0)) (bar () ((@ bar__1))) (bar__1 () (halt 1))) (foo))").unwrap();
        assert_eq!(eta_split(x), y);
    }
}
