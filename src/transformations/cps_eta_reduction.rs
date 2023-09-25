use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Value};

fn eta_reduce<V: Clone + PartialEq>(exp: &Expr<V>) -> Expr<V> {
    match exp {
        Expr::Record(fields, r, cnt) => Expr::Record(*fields, r.clone(), eta_reduce(cnt).into()),
        Expr::App(rator, rands) => Expr::App(rator.clone(), *rands),
        Expr::Fix(defs, body) => {
            let mut defs_out = vec![];
            let mut body = *body;

            for (f, params, fbody) in defs.iter() {
                match &**fbody {
                    Expr::App(Value::Var(g), _) if f == g => {}
                    Expr::App(g, args) => {
                        if params.len() == args.len() {
                            if params.iter().zip(args.iter()).all(|(p, a)| match a {
                                Value::Var(x) => x == p,
                                _ => false,
                            }) {
                                body = substitute_expr(f, g, &body).into();
                                continue;
                            }
                        }
                    }
                    _ => {}
                }
                defs_out.push((f.clone(), *params, *fbody));
            }

            Expr::Fix(Ref::array(defs_out), body)
        }
        _ => todo!(),
    }
}

fn substitute_expr<V: Clone + PartialEq>(var: &V, val: &Value<V>, expr: &Expr<V>) -> Expr<V> {
    match expr {
        Expr::Record(fs, r, c) => {
            let fs = fs
                .iter()
                .map(|(v, ap)| (substitute_val(var, val, v), ap.clone()));
            if r == var {
                Expr::Record(Ref::array(fs.collect()), r.clone(), *c)
            } else {
                Expr::Record(
                    Ref::array(fs.collect()),
                    r.clone(),
                    substitute_expr(var, val, c).into(),
                )
            }
        }
        Expr::App(rator, rands) => Expr::App(
            substitute_val(var, val, rator),
            substitute_vals(var, val, rands.iter()),
        ),
        _ => todo!(),
    }
}

fn substitute_val<V: Clone + PartialEq>(var: &V, val: &Value<V>, original: &Value<V>) -> Value<V> {
    match original {
        Value::Var(v) if v == var => val.clone(),
        _ => original.clone(),
    }
}

fn substitute_vals<'a, V: Clone + PartialEq>(
    var: &V,
    val: &Value<V>,
    vals: impl Iterator<Item = &'a Value<V>>,
) -> Ref<[Value<V>]> {
    Ref::array(vals.map(|v| substitute_val(var, val, v)).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{cps_expr, cps_ident_list, cps_value};

    #[test]
    fn simple_reduction() {
        let x: Expr<&'static str> = cps_expr!(fix f(x)=(halt x) in (f z));
        let y: Expr<&'static str> = cps_expr!(fix in (halt z));
        assert_eq!(eta_reduce(&x), y);
    }
}
