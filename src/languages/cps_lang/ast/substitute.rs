use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Transform, Transformed, Value};

struct SubstituteVar<V: 'static>(V, Value<V>);

impl<V: Clone + PartialEq> Transform<V> for SubstituteVar<V> {
    fn visit_expr(&mut self, expr: &Expr<V>) -> Transformed<Expr<V>> {
        match expr {
            Expr::Record(fields, var, cnt) if var == &self.0 => Transformed::Done(Expr::Record(
                self.transform_fields(fields),
                var.clone(),
                *cnt,
            )),

            Expr::Select(idx, rec, var, cnt) if var == &self.0 => Transformed::Done(Expr::Select(
                *idx,
                self.transform_value(rec),
                var.clone(),
                *cnt,
            )),

            Expr::Offset(idx, rec, var, cnt) if var == &self.0 => Transformed::Done(Expr::Offset(
                *idx,
                self.transform_value(rec),
                var.clone(),
                *cnt,
            )),

            Expr::Fix(defs, _) if defs.iter().any(|(f, _, _)| f == &self.0) => {
                // var is shadowed by definition
                Transformed::Done(expr.clone())
            }

            Expr::Fix(defs, cnt) => {
                let mut defs_out = Vec::with_capacity(defs.len());
                for (f, params, fbody) in defs.iter() {
                    if params.contains(&self.0) {
                        defs_out.push((f.clone(), *params, *fbody));
                    } else {
                        defs_out.push((f.clone(), *params, Ref::new(self.transform_expr(fbody))));
                    }
                }
                let cnt_out = self.transform_expr(cnt);
                Transformed::Done(Expr::Fix(Ref::array(defs_out), Ref::new(cnt_out)))
            }

            Expr::PrimOp(op, args, vars, cnts) if vars.contains(&self.0) => {
                Transformed::Done(Expr::PrimOp(*op, self.transform_values(args), *vars, *cnts))
            }

            Expr::Record(_, _, _)
            | Expr::Select(_, _, _, _)
            | Expr::Offset(_, _, _, _)
            | Expr::App(_, _)
            | Expr::Switch(_, _)
            | Expr::PrimOp(_, _, _, _)
            | Expr::Halt(_)
            | Expr::Panic(_) => Transformed::Continue,
        }
    }

    fn visit_value(&mut self, value: &Value<V>) -> Transformed<Value<V>> {
        match value {
            Value::Var(v) | Value::Label(v) if v == &self.0 => Transformed::Done(self.1.clone()),
            _ => Transformed::Continue,
        }
    }
}

impl<V: Clone + PartialEq> Expr<V> {
    pub fn substitute_vars(self, subs: impl IntoIterator<Item = (V, Value<V>)>) -> Self {
        let mut out = self.clone();
        for (var, val) in subs {
            out = out.substitute_var(&var, &val);
        }
        out
    }

    pub fn substitute_var(&self, var: &V, val: &Value<V>) -> Self {
        SubstituteVar(var.clone(), val.clone()).transform_expr(self)
    }
}

impl<V: Clone + PartialEq> Value<V> {
    pub fn substitute_var(&self, var: &V, val: &Value<V>) -> Self {
        match self {
            Value::Var(v) | Value::Label(v) if v == var => val.clone(),
            _ => self.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::common_primops::PrimOp;
    use crate::{
        cps_expr, cps_expr_list, cps_field, cps_field_list, cps_ident_list, cps_value, list,
    };

    #[test]
    fn variable_value_substituted() {
        let x = Value::Var("foo");
        let y = x.substitute_var(&"foo", &Value::Int(0));
        assert_eq!(y, Value::Int(0));
    }

    #[test]
    fn label_value_substituted() {
        let x = Value::Label("foo");
        let y = x.substitute_var(&"foo", &Value::Int(0));
        assert_eq!(y, Value::Int(0));
    }

    #[test]
    fn other_variable_not_substituted() {
        let x = Value::Var("bar");
        let y = x.substitute_var(&"foo", &Value::Int(0));
        assert_eq!(y, x);
    }

    #[test]
    fn non_variable_values_pass_through() {
        let x = Value::Int(42);
        let y = x.substitute_var(&"foo", &Value::Int(0));
        assert_eq!(y, x);
    }

    #[test]
    fn substitute_record() {
        let x: Expr<&str> = cps_expr!(record [x y z] r y);
        let y = x.substitute_var(&"y", &Value::Var("YY"));
        assert_eq!(y, cps_expr!(record [x YY z] r YY));

        let x: Expr<&str> = cps_expr!(record [r] r r);
        let y = x.substitute_var(&"r", &Value::Var("x"));
        assert_eq!(y, cps_expr!(record [x] r r));
    }

    #[test]
    fn substitute_select() {
        let x: Expr<&str> = cps_expr!(select 0 r x r);
        let y = x.substitute_var(&"r", &Value::Var("s"));
        assert_eq!(y, cps_expr!(select 0 s x s));

        let x: Expr<&str> = cps_expr!(select 0 x x x);
        let y = x.substitute_var(&"x", &Value::Var("y"));
        assert_eq!(y, cps_expr!(select 0 y x x));
    }

    #[test]
    fn substitute_offset() {
        let x: Expr<&str> = cps_expr!(offset 0 r x r);
        let y = x.substitute_var(&"r", &Value::Var("s"));
        assert_eq!(y, cps_expr!(offset 0 s x s));

        let x: Expr<&str> = cps_expr!(offset 0 x x x);
        let y = x.substitute_var(&"x", &Value::Var("y"));
        assert_eq!(y, cps_expr!(offset 0 y x x));
    }

    #[test]
    fn substitute_app() {
        let x: Expr<&str> = cps_expr!(a b);
        let y = x.substitute_var(&"x", &Value::Var("y"));
        assert_eq!(y, x);

        let x: Expr<&str> = cps_expr!(x x x);
        let y = x.substitute_var(&"x", &Value::Var("y"));
        assert_eq!(y, cps_expr!(y y y));
    }

    #[test]
    fn substitute_fix() {
        let x: Expr<&str> = cps_expr!(fix x(y)=x; f(y)=x in x);
        let y = x.substitute_var(&"x", &Value::Var("z"));
        assert_eq!(y, x);

        let x: Expr<&str> = cps_expr!(fix f(x)=x; g(y)=x; h(x)=y in x);
        let y = x.substitute_var(&"x", &Value::Var("z"));
        assert_eq!(y, cps_expr!(fix f(x)=x; g(y)=z; h(x)=y in z));
    }

    #[test]
    fn substitute_switch() {
        let x: Expr<&str> = cps_expr!(switch y [x y z]);
        let y = x.substitute_var(&"y", &Value::Var("k"));
        assert_eq!(y, cps_expr!(switch k [x k z]));
    }

    #[test]
    fn substitute_primop() {
        let x: Expr<&str> = Expr::PrimOp(
            PrimOp::IAdd,
            list![Value::Var("x"), Value::Var("x")],
            list![],
            list![Expr::App(Value::Var("x"), list![]).into()],
        );
        let y = x.substitute_var(&"x", &Value::Var("a"));
        assert_eq!(
            y,
            Expr::PrimOp(
                PrimOp::IAdd,
                list![Value::Var("a"), Value::Var("a")],
                list![],
                list![Expr::App(Value::Var("a"), list![]).into()]
            )
        );

        let x: Expr<&str> = Expr::PrimOp(
            PrimOp::IAdd,
            list![],
            list!["x"],
            list![Expr::App(Value::Var("x"), list![]).into()],
        );
        let y = x.substitute_var(&"x", &Value::Var("a"));
        assert_eq!(
            y,
            Expr::PrimOp(
                PrimOp::IAdd,
                list![],
                list!["x"],
                list![Expr::App(Value::Var("x"), list![]).into()]
            )
        );
    }
}
