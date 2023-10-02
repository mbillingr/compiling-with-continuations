use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Value};

impl<V: Clone + PartialEq> Expr<V> {
    pub fn substitute_vars(self, subs: impl IntoIterator<Item = (V, Value<V>)>) -> Self {
        let mut out = self.clone();
        for (var, val) in subs {
            out = out.substitute_var(&var, &val);
        }
        out
    }

    pub fn substitute_var(&self, var: &V, val: &Value<V>) -> Self {
        match self {
            Expr::Record(fs, r, c) => {
                let fs = fs
                    .iter()
                    .map(|(v, ap)| (v.substitute_var(var, val), ap.clone()));
                Expr::Record(
                    Ref::array(fs.collect()),
                    r.clone(),
                    substitute_if_not_shadowed(c, r, var, val),
                )
            }

            Expr::Select(idx, r, x, c) => Expr::Select(
                *idx,
                r.substitute_var(var, val),
                x.clone(),
                substitute_if_not_shadowed(c, x, var, val),
            ),

            Expr::Offset(idx, r, x, c) => Expr::Offset(
                *idx,
                r.substitute_var(var, val),
                x.clone(),
                substitute_if_not_shadowed(c, x, var, val),
            ),

            Expr::App(rator, rands) => Expr::App(
                rator.substitute_var(var, val),
                rands.substitute_var(var, val),
            ),

            Expr::Fix(defs, body) if defs.iter().any(|(f, _, _)| f == var) => {
                // substituted variable is shadowed by a definition
                Expr::Fix(*defs, *body)
            }

            Expr::Fix(defs, body) => {
                let mut defs_out = Vec::with_capacity(defs.len());
                for (f, params, fbody) in defs.iter() {
                    if params.contains(var) {
                        defs_out.push((f.clone(), *params, *fbody));
                    } else {
                        defs_out.push((f.clone(), *params, fbody.substitute_var(var, val).into()));
                    }
                }
                let body_out = body.substitute_var(var, val).into();
                Expr::Fix(Ref::array(defs_out), body_out)
            }

            Expr::Switch(v, arms) => {
                Expr::Switch(v.substitute_var(var, val), arms.substitute_var(var, val))
            }

            Expr::PrimOp(op, args, binds, cnts) => {
                let args_out = args.substitute_var(var, val);
                let cnts_out = if binds.contains(var) {
                    *cnts
                } else {
                    cnts.substitute_var(var, val)
                };
                Expr::PrimOp(*op, args_out, *binds, cnts_out)
            }

            Expr::Halt(v) => Expr::Halt(v.substitute_var(var, val)),

            Expr::Panic(msg) => Expr::Panic(*msg),
        }
    }

    pub fn rename_fn(&self, old_name: &V, new_name: &V) -> Self {
        todo!()
    }
}

fn substitute_if_not_shadowed<V: Clone + PartialEq>(
    expr: &Ref<Expr<V>>,
    binding: &V,
    var: &V,
    val: &Value<V>,
) -> Ref<Expr<V>> {
    if binding == var {
        *expr
    } else {
        expr.substitute_var(var, val).into()
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

impl<V: Clone + PartialEq> Ref<[Value<V>]> {
    pub fn substitute_var(&self, var: &V, val: &Value<V>) -> Self {
        Ref::array(self.iter().map(|v| v.substitute_var(var, val)).collect())
    }
}

impl<V: Clone + PartialEq> Ref<[Ref<Expr<V>>]> {
    pub fn substitute_var(&self, var: &V, val: &Value<V>) -> Self {
        Ref::array(
            self.iter()
                .map(|v| v.substitute_var(var, val).into())
                .collect(),
        )
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
