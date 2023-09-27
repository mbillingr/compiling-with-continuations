use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Value};
use std::collections::HashMap;
use std::hash::Hash;

/// Convert references to known functions from Var to Label

pub struct Context {}

#[derive(Clone)]
struct Binding {
    is_label: bool,
}

impl Context {
    pub fn new() -> Self {
        Context {}
    }

    fn convert_labels<V: std::fmt::Debug + Clone + Eq + Hash>(
        &mut self,
        expr: &Expr<V>,
    ) -> Expr<V> {
        self.convert_exp(expr, &HashMap::new())
    }

    fn convert_exp<V: std::fmt::Debug + Clone + Eq + Hash>(
        &mut self,
        expr: &Expr<V>,
        bindings: &HashMap<V, Binding>,
    ) -> Expr<V> {
        match expr {
            Expr::Record(fields, r, cnt) => {
                let fields_out = fields
                    .iter()
                    .map(|(v, p)| (self.convert_val(v, bindings), p.clone()))
                    .collect();
                let cnt_out = self.convert_with(cnt, &bindings, r);
                Expr::Record(Ref::array(fields_out), r.clone(), cnt_out.into())
            }

            Expr::Select(idx, r, x, cnt) => {
                let r_out = self.convert_val(r, bindings);
                let cnt_out = self.convert_with(cnt, &bindings, x);
                Expr::Select(*idx, r_out, x.clone(), cnt_out.into())
            }

            Expr::Offset(idx, r, x, cnt) => {
                let r_out = self.convert_val(r, bindings);
                let cnt_out = self.convert_with(cnt, &bindings, x);
                Expr::Offset(*idx, r_out, x.clone(), cnt_out.into())
            }

            Expr::App(func, args) => Expr::App(
                self.convert_val(func, bindings),
                self.convert_vals(args, bindings),
            ),

            Expr::Fix(funcs, body) => {
                let mut bnd = bindings.clone();
                for (f, _, _) in funcs.iter() {
                    bnd.insert(f.clone(), Binding { is_label: true });
                }
                let mut funcs_out = vec![];
                for (f, p, fb) in funcs.iter() {
                    let mut locals = bnd.clone();
                    for p in p.iter() {
                        locals.insert(p.clone(), Binding { is_label: false });
                    }
                    funcs_out.push((f.clone(), *p, self.convert_exp(fb, &locals).into()));
                }
                Expr::Fix(Ref::array(funcs_out), self.convert_exp(body, &bnd).into())
            }

            Expr::Switch(val, arms) => {
                let val_out = self.convert_val(val, bindings);
                let arms_out = arms
                    .iter()
                    .map(|x| self.convert_exp(x, bindings).into())
                    .collect();
                Expr::Switch(val_out, Ref::array(arms_out))
            }

            Expr::PrimOp(op, args, ress, cnts) => {
                let args_out = self.convert_vals(args, bindings);
                let mut bindings = bindings.clone();
                for r in ress.iter().cloned() {
                    bindings.insert(r, Binding { is_label: false });
                }
                let cnts_out = cnts
                    .iter()
                    .map(|c| self.convert_exp(c, &bindings).into())
                    .collect();
                Expr::PrimOp(*op, args_out, *ress, Ref::array(cnts_out))
            }

            Expr::Panic(msg) => Expr::Panic(*msg),
        }
    }

    fn convert_with<V: std::fmt::Debug + Clone + Eq + Hash>(
        &mut self,
        expr: &Expr<V>,
        bindings: &HashMap<V, Binding>,
        name: &V,
    ) -> Expr<V> {
        let mut bindings = bindings.clone();
        bindings.insert(name.clone(), Binding { is_label: false });
        self.convert_exp(expr, &bindings)
    }

    fn convert_val<V: std::fmt::Debug + Clone + Eq + Hash>(
        &mut self,
        val: &Value<V>,
        bindings: &HashMap<V, Binding>,
    ) -> Value<V> {
        if let Value::Var(x) = val {
            if let Some(Binding { is_label: true }) = bindings.get(x) {
                return Value::Label(x.clone());
            }
        }
        val.clone()
    }

    fn convert_vals<V: std::fmt::Debug + Clone + Eq + Hash>(
        &mut self,
        vals: &[Value<V>],
        bindings: &HashMap<V, Binding>,
    ) -> Ref<[Value<V>]> {
        Ref::array(
            vals.into_iter()
                .map(|v| self.convert_val(v, bindings))
                .collect(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        cps_expr, cps_expr_list, cps_field_list, cps_ident_list, cps_value, cps_value_list,
    };

    #[test]
    fn convert_vars() {
        let mut bindings = HashMap::new();
        bindings.insert("x", Binding { is_label: true });
        bindings.insert("y", Binding { is_label: false });

        assert_eq!(
            Context::new().convert_val(&Value::Var("x"), &bindings),
            Value::Label("x")
        );
        assert_eq!(
            Context::new().convert_val(&Value::Var("y"), &bindings),
            Value::Var("y")
        );
        assert_eq!(
            Context::new().convert_val(&Value::Var("z"), &bindings),
            Value::Var("z")
        );
    }

    #[test]
    fn convert_fix() {
        let x: Expr<&str> = cps_expr!(fix f(x)=(f x) in (f f));
        let y: Expr<&str> = cps_expr!(fix f(x)=((@f) x) in ((@f) (@f)));
        assert_eq!(Context::new().convert_labels(&x), y);

        let x: Expr<&str> = cps_expr!(fix f(x)=(x) in (switch f [(f f)]));
        let y: Expr<&str> = cps_expr!(fix f(x)=(x) in (switch (@f) [((@f) (@f))]));
        assert_eq!(Context::new().convert_labels(&x), y);
    }

    #[test]
    fn dont_convert_funcs_shadowed_by_locals() {
        let x: Expr<&str> = cps_expr!(fix f(x)=(x); g(f)=(f) in (g f));
        let y: Expr<&str> = cps_expr!(fix f(x)=(x); g(f)=(f) in ((@g) (@f)));
        assert_eq!(Context::new().convert_labels(&x), y);
    }

    #[test]
    fn dont_convert_funcs_shadowed_by_exprs() {
        let x: Expr<&str> = cps_expr!(fix f(x)=(x) in (record [] f (f)));
        assert_eq!(Context::new().convert_labels(&x), x);

        let x: Expr<&str> = cps_expr!(fix f(x)=(x) in (select 0 r f (f)));
        assert_eq!(Context::new().convert_labels(&x), x);

        let x: Expr<&str> = cps_expr!(fix f(x)=(x) in (offset 0 r f (f)));
        assert_eq!(Context::new().convert_labels(&x), x);

        let x: Expr<&str> = cps_expr!(fix f(x)=(x) in (box (int 0) [f] [(f f)]));
        assert_eq!(Context::new().convert_labels(&x), x);
    }
}
