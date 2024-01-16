use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Transform, Transformed, Value};

impl<V: Clone + PartialEq, F: Clone> Expr<V, F> {
    pub fn substitute_vars(self, subs: impl IntoIterator<Item = (V, Value<V, F>)>) -> Self {
        let mut out = self.clone();
        for (var, val) in subs {
            out = out.substitute_var(&var, &val);
        }
        out
    }

    pub fn substitute_var(&self, var: &V, val: &Value<V, F>) -> Self {
        SubstituteVar(var.clone(), val.clone()).transform_expr(self)
    }
}

impl<V: Clone + PartialEq, F: Clone> Value<V, F> {
    pub fn substitute_var(&self, var: &V, val: &Value<V, F>) -> Self {
        match self {
            Value::Var(v) if v == var => val.clone(),
            _ => self.clone(),
        }
    }
}

impl<V: Clone, F: Clone + PartialEq> Expr<V, F> {
    pub fn substitute_label(&self, var: &F, val: &Value<V, F>) -> Self {
        SubstituteLabel(var.clone(), val.clone()).transform_expr(self)
    }
}

impl<V: Clone, F: Clone + PartialEq> Value<V, F> {
    pub fn substitute_label(&self, var: &F, val: &Value<V, F>) -> Self {
        match self {
            Value::Label(v) if v == var => val.clone(),
            _ => self.clone(),
        }
    }
}

struct SubstituteVar<V: 'static, F: 'static>(V, Value<V, F>);

impl<V: Clone + PartialEq, F: Clone> Transform<V, F> for SubstituteVar<V, F> {
    fn visit_expr(&mut self, expr: &Expr<V, F>) -> Transformed<Expr<V, F>> {
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

    fn visit_value(&mut self, value: &Value<V, F>) -> Transformed<Value<V, F>> {
        match value {
            Value::Var(v) if v == &self.0 => Transformed::Done(self.1.clone()),
            _ => Transformed::Continue,
        }
    }
}

struct SubstituteLabel<V: 'static, F: 'static>(F, Value<V, F>);

impl<V: Clone, F: Clone + PartialEq> Transform<V, F> for SubstituteLabel<V, F> {
    fn visit_expr(&mut self, expr: &Expr<V, F>) -> Transformed<Expr<V, F>> {
        match expr {
            Expr::Fix(defs, _) if defs.iter().any(|(f, _, _)| f == &self.0) => {
                // name is shadowed by definition
                Transformed::Done(expr.clone())
            }
            _ => Transformed::Continue,
        }
    }

    fn visit_value(&mut self, value: &Value<V, F>) -> Transformed<Value<V, F>> {
        match value {
            Value::Label(f) if f == &self.0 => Transformed::Done(self.1.clone()),
            _ => Transformed::Continue,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::common_primops::PrimOp;
    use crate::{
        cps_expr, cps_expr_list, cps_field, cps_field_list, cps_ident_list, cps_value, array,
    };

    #[test]
    fn variable_value_substituted() {
        let x: Value<&str, &str> = Value::Var("foo");
        let y = x.substitute_var(&"foo", &Value::Int(0));
        assert_eq!(y, Value::Int(0));
    }

    #[test]
    fn label_value_not_substituted() {
        let x: Value<&str, &str> = Value::Label("foo");
        let y = x.substitute_var(&"foo", &Value::Int(0));
        assert_eq!(y, x);
    }

    #[test]
    fn other_variable_not_substituted() {
        let x: Value<&str, &str> = Value::Var("bar");
        let y = x.substitute_var(&"foo", &Value::Int(0));
        assert_eq!(y, x);
    }

    #[test]
    fn non_variable_values_pass_through() {
        let x: Value<&str, &str> = Value::Int(42);
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
            array![Value::Var("x"), Value::Var("x")],
            array![],
            array![Expr::App(Value::Var("x"), array![]).into()],
        );
        let y = x.substitute_var(&"x", &Value::Var("a"));
        assert_eq!(
            y,
            Expr::PrimOp(
                PrimOp::IAdd,
                array![Value::Var("a"), Value::Var("a")],
                array![],
                array![Expr::App(Value::Var("a"), array![]).into()]
            )
        );

        let x: Expr<&str> = Expr::PrimOp(
            PrimOp::IAdd,
            array![],
            array!["x"],
            array![Expr::App(Value::Var("x"), array![]).into()],
        );
        let y = x.substitute_var(&"x", &Value::Var("a"));
        assert_eq!(
            y,
            Expr::PrimOp(
                PrimOp::IAdd,
                array![],
                array!["x"],
                array![Expr::App(Value::Var("x"), array![]).into()]
            )
        );
    }
}
