use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{AccessPath, Expr, List, Value};

pub trait Transform<V: Clone, F: Clone = V> {
    fn visit_expr(&mut self, expr: &Expr<V, F>) -> Transformed<Expr<V, F>>;
    fn visit_value(&mut self, value: &Value<V, F>) -> Transformed<Value<V, F>>;

    fn transform_expr(&mut self, expr: &Expr<V, F>) -> Expr<V, F>
    where
        Self: Sized,
    {
        expr.transform(self)
    }

    fn transform_value(&mut self, value: &Value<V, F>) -> Value<V, F>
    where
        Self: Sized,
    {
        value.transform(self)
    }

    fn transform_values(&mut self, values: &List<Value<V, F>>) -> List<Value<V, F>>
    where
        Self: Sized,
    {
        Ref::array(values.iter().map(|x| x.transform(self)).collect())
    }

    fn transform_fields(
        &mut self,
        fields: &List<(Value<V, F>, AccessPath)>,
    ) -> List<(Value<V, F>, AccessPath)>
    where
        Self: Sized,
    {
        Ref::array(
            fields
                .iter()
                .map(|(f, ap)| (f.transform(self), ap.clone()))
                .collect(),
        )
    }
}

pub enum Transformed<T> {
    /// The transform does not modify the node directly, but will recur into its children
    Continue,

    /// The transform replaces the node and is done with this branch
    Done(T),

    /// The transform should run again on the replaced node
    Again(T),
}

impl<V: Clone, F: Clone> Expr<V, F> {
    pub fn transform(&self, transformer: &mut impl Transform<V, F>) -> Self {
        match transformer.visit_expr(self) {
            Transformed::Continue => {}
            Transformed::Done(new_expr) => return new_expr,
            Transformed::Again(new_expr) => return new_expr.transform(transformer),
        }

        match self {
            Expr::Record(fields, var, cnt) => Expr::Record(
                transformer.transform_fields(fields),
                var.clone(),
                Ref::new(transformer.transform_expr(cnt)),
            ),

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
                transformer.transform_values(rands),
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
                let cnts_out = cnts
                    .iter()
                    .map(|c| c.transform(transformer))
                    .map(Ref::new)
                    .collect();
                Expr::PrimOp(
                    *op,
                    transformer.transform_values(args),
                    *vars,
                    Ref::array(cnts_out),
                )
            }

            Expr::Halt(value) => Expr::Halt(value.transform(transformer)),

            Expr::Panic(msg) => Expr::Panic(*msg),
        }
    }
}

impl<V: Clone, F: Clone> Value<V, F> {
    pub fn transform(&self, transformer: &mut impl Transform<V, F>) -> Self {
        match transformer.visit_value(self) {
            Transformed::Continue => self.clone(),
            Transformed::Done(new_value) => new_value,
            Transformed::Again(new_value) => return new_value.transform(transformer),
        }
    }
}
