use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{AccessPath, Expr, Transform, Transformed, Value};
use crate::transformations::{GenSym, GensymContext};
use std::sync::Arc;

pub struct LimitArgs {
    max_n_args: usize,
    gs: Arc<GensymContext>,
}

impl LimitArgs {
    pub fn new(max_n_args: usize, gs: Arc<GensymContext>) -> Self {
        LimitArgs { max_n_args, gs }
    }
    pub fn new_context(max_n_args: usize, gensym_delim: impl ToString) -> Self {
        LimitArgs {
            max_n_args,
            gs: Arc::new(GensymContext::new(gensym_delim)),
        }
    }
}

impl<V: Clone + PartialEq + GenSym> Transform<V> for LimitArgs {
    fn visit_expr(&mut self, expr: &Expr<V>) -> Transformed<Expr<V>> {
        match expr {
            Expr::App(f, args) if args.len() > self.max_n_args => {
                let r: V = self.gs.gensym("args");
                Transformed::Done(Expr::Record(
                    Ref::array(
                        args.iter()
                            .skip(1) // don't put continuation arg in record
                            .map(|a| (a.clone(), AccessPath::Ref(0)))
                            .collect(),
                    ),
                    r.clone(),
                    Ref::new(Expr::App(
                        f.clone(),
                        Ref::array(vec![args[0].clone(), Value::Var(r)]),
                    )),
                ))
            }

            Expr::Fix(defs, body) => {
                let mut defs_out = vec![];
                for (f, p, b) in defs.iter() {
                    let mut b_out = Ref::new(self.transform_expr(b));
                    if p.len() <= self.max_n_args {
                        defs_out.push((f.clone(), *p, b_out));
                    } else {
                        let args: V = self.gs.gensym("args");
                        for (i, param) in p.iter().skip(1).enumerate().rev() {
                            b_out = Ref::new(Expr::Select(
                                i as isize,
                                Value::Var(args.clone()),
                                param.clone(),
                                b_out,
                            ));
                        }
                        defs_out.push((f.clone(), Ref::array(vec![p[0].clone(), args]), b_out))
                    }
                }
                Transformed::Done(Expr::Fix(
                    Ref::array(defs_out),
                    self.transform_expr(body).into(),
                ))
            }
            _ => Transformed::Continue,
        }
    }

    fn visit_value(&mut self, _: &Value<V>) -> Transformed<Value<V>> {
        Transformed::Continue
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_no_change() {
        let x = Expr::from_str("(fix ((f (k a b) (k b))) (f c 1 2))").unwrap();
        assert_eq!(LimitArgs::new_context(3, "_").transform_expr(&x), x);
    }

    #[test]
    fn test_limit_applies() {
        let x = Expr::from_str("(fix ((f (k a b) (k b))) (f c 1 2))").unwrap();
        let y = Expr::from_str(
            "(fix ((f (k args_0)
                      (select 0 args_0 a 
                          (select 1 args_0 b (k b))))) 
                (record ((1 (ref 0)) (2 (ref 0))) args_1 
                    (f c args_1)))",
        )
        .unwrap();
        assert_eq!(LimitArgs::new_context(2, "_").transform_expr(&x), y);
    }
}
