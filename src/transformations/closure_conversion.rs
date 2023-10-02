use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{AccessPath, Expr, Value};
use crate::list;
use crate::transformations::GensymContext;
use std::collections::HashMap;

pub struct Context {
    gs: GensymContext,
}

impl Context {
    pub fn new(sym_delim: &'static str) -> Self {
        Context {
            gs: GensymContext::new(sym_delim),
        }
    }
}

impl Context {
    pub fn convert_closures(&'static self, exp: &Expr<Ref<str>>) -> Expr<Ref<str>> {
        match exp {
            Expr::Record(fields, r, cnt) => {
                Expr::Record(*fields, r.clone(), self.convert_closures(cnt).into())
            }

            Expr::Select(idx, r, x, cnt) => Expr::Select(
                *idx,
                r.clone(),
                x.clone(),
                self.convert_closures(cnt).into(),
            ),

            Expr::Offset(idx, r, x, cnt) => Expr::Offset(
                *idx,
                r.clone(),
                x.clone(),
                self.convert_closures(cnt).into(),
            ),

            Expr::App(rator, rands) => Expr::App(rator.clone(), *rands),

            Expr::Fix(defs, body) => {
                let cls_arg = self.gs.gensym("cls");
                let cls_vars = dbg!(exp.fix_function_free_vars());
                let defs_out: Vec<_> = defs
                    .iter()
                    .map(|(f, p, b)| {
                        let mut fbody = *b;
                        for v in b.free_vars().iter() {
                            let idx = 1; // todo: find in cls relative to current function
                            fbody = Ref::new(Expr::Select(idx, Value::Var(cls_arg), *v, fbody));
                        }
                        (self.gs.gensym(f), p.prepend(cls_arg), fbody)
                    })
                    .collect();

                let mut cls_fields = vec![];
                for (f, _, _) in &defs_out {
                    cls_fields.push((Value::Label(*f), AccessPath::Ref(0)));
                }
                let body_out = Ref::new(Expr::Record(Ref::array(cls_fields), cls_arg, *body));

                Expr::Fix(Ref::array(defs_out), body_out)
            }

            Expr::Switch(v, arms) => Expr::Switch(
                v.clone(),
                Ref::array(
                    arms.iter()
                        .map(|x| self.convert_closures(x).into())
                        .collect(),
                ),
            ),

            Expr::PrimOp(op, args, res, cnts) => Expr::PrimOp(
                *op,
                *args,
                *res,
                Ref::array(
                    cnts.iter()
                        .map(|c| self.convert_closures(c).into())
                        .collect(),
                ),
            ),

            Expr::Halt(v) => Expr::Halt(v.clone()),

            Expr::Panic(msg) => Expr::Panic(*msg),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        cps_expr, cps_expr_list, cps_field, cps_field_list, cps_ident_list, cps_value,
        cps_value_list,
    };

    #[test]
    fn simple_conversion() {
        let ctx = Box::leak(Box::new(Context::new("__")));

        let x = cps_expr!(record [] r (fix f(x)=(halt r) in ((@f) (@f))));
        let y = cps_expr!(record [] r (fix f__1(cls__0 x)=(select 1 cls__0 r (halt r)) in (record [(@f__1) r] f (select 0 f f__2 (f__2 f)))));
        assert_eq!(ctx.convert_closures(&x), y);
    }
}
