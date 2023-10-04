use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Value};

pub trait Transform<V> {
    fn transform_expr(&mut self, expr: &Expr<V>) -> Transformed<Expr<V>>;
    fn transform_value(&mut self, value: &Value<V>) -> Transformed<Value<V>>;

    fn apply(&mut self, expr: &Expr<V>) -> Expr<V>
        where
            V: Clone,
            Self: Sized
    {
        expr.transform(self)
    }
}

pub enum Transformed<T> {
    None,
    Done(T),
    Again(T),
}

impl<V: Clone> Expr<V> {
    pub fn transform(&self, transformer: &mut impl Transform<V>) -> Self {
        match transformer.transform_expr(self) {
            Transformed::None => {}
            Transformed::Done(new_expr) => return new_expr,
            Transformed::Again(new_expr) => return new_expr.transform(transformer),
        }

        match self {
            Expr::Record(fields, var, cnt) => {
                let fields_out = fields
                    .iter()
                    .map(|(f, ap)| (f.transform(transformer), ap.clone()))
                    .collect();
                let cnt_out = cnt.transform(transformer);
                Expr::Record(Ref::array(fields_out), var.clone(), Ref::new(cnt_out))
            }

            Expr::Select(idx, rec, var, cnt) => Expr::Select(
                *idx,
                rec.transform(transformer),
                var.clone(),
                Ref::new(cnt.transform(transformer)),
            ),

            Expr::Offset(idx, rec, var, cnt) => Expr::Offset(
                *idx,
                rec.transform(transformer),
                var.clone(),
                Ref::new(cnt.transform(transformer)),
            ),

            Expr::App(rator, rands) => Expr::App(
                rator.transform(transformer),
                Ref::array(rands.iter().map(|a| a.transform(transformer)).collect()),
            ),

            Expr::Fix(defs, cnt) => {
                let defs_out = defs
                    .iter()
                    .map(|(name, params, body)| {
                        (name.clone(), *params, Ref::new(body.transform(transformer)))
                    })
                    .collect();
                let cnt_out = cnt.transform(transformer);
                Expr::Fix(Ref::array(defs_out), Ref::new(cnt_out))
            }

            Expr::Switch(val, cnts) => {
                let cnts_out = cnts
                    .iter()
                    .map(|c| c.transform(transformer))
                    .map(Ref::new)
                    .collect();
                Expr::Switch(val.transform(transformer), Ref::array(cnts_out))
            }

            Expr::PrimOp(op, args, vars, cnts) => {
                let args_out = args.iter().map(|a| a.transform(transformer)).collect();
                let cnts_out = cnts
                    .iter()
                    .map(|c| c.transform(transformer))
                    .map(Ref::new)
                    .collect();
                Expr::PrimOp(*op, Ref::array(args_out), *vars, Ref::array(cnts_out))
            }

            Expr::Halt(value) => Expr::Halt(value.transform(transformer)),

            Expr::Panic(msg) => Expr::Panic(*msg),
        }
    }
}

impl<V: Clone> Value<V> {
    pub fn transform(&self, transformer: &mut impl Transform<V>) -> Self {
        match transformer.transform_value(self) {
            Transformed::None => self.clone(),
            Transformed::Done(new_value) => new_value,
            Transformed::Again(new_value) => return new_value.transform(transformer),
        }
    }
}
