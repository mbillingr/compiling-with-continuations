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
                                body = body.substitute_var(f, g).into();
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
