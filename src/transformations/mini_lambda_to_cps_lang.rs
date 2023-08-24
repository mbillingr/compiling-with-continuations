use crate::core::reference::Ref;
use crate::languages::cps_lang::ast as cps;
use crate::languages::mini_lambda::ast;
use std::sync::atomic::{AtomicUsize, Ordering};

type LExpr = ast::Expr<Ref<str>>;
type LPrim = ast::PrimOp;
type CExpr = cps::Expr<Ref<str>>;
type CVal = cps::Value<Ref<str>>;
type CPrim = cps::PrimOp;

struct Context {
    sym_ctr: AtomicUsize,
    sym_delim: &'static str,
}

impl Context {
    pub fn new(sym_delim: &'static str) -> Self {
        Context {
            sym_ctr: AtomicUsize::new(0),
            sym_delim,
        }
    }
    pub fn convert(&'static self, expr: &LExpr, c: Box<dyn FnOnce(CVal) -> CExpr>) -> CExpr {
        match expr {
            LExpr::Var(v) => c(CVal::Var(*v)),
            LExpr::Int(i) => c(CVal::Int(*i)),
            LExpr::Real(r) => c(CVal::Real(*r)),
            LExpr::Record(fields) if fields.len() == 0 => c(CVal::Int(0)),
            LExpr::Record(fields) => {
                let x = self.gensym("r");
                self.convert_sequence(*fields, move |a| {
                    CExpr::Record(a, x, Ref::new(c(CVal::Var(x))))
                })
            }
            LExpr::Select(idx, rec) => {
                let idx = *idx;
                let w = self.gensym("w");
                self.convert(
                    rec,
                    Box::new(move |v| CExpr::Select(idx, v, w, Ref::new(c(CVal::Var(w))))),
                )
            }
            LExpr::App(func, arg) => match **func {
                LExpr::Prim(LPrim::INeg) => {
                    let w = self.gensym("w");
                    self.convert(
                        arg,
                        Box::new(move |v| {
                            CExpr::PrimOp(
                                CPrim::INeg,
                                Ref::array(vec![v]),
                                Ref::array(vec![w]),
                                Ref::array(vec![Ref::new(c(CVal::Var(w)))]),
                            )
                        }),
                    )
                }
                _ => todo!("{:?}", expr),
            },
            LExpr::Prim(LPrim::INeg) => {
                let x = self.gensym("x");
                self.convert(
                    &LExpr::Fn(
                        x,
                        Ref::new(LExpr::App(
                            LExpr::Prim(LPrim::INeg).into(),
                            LExpr::Var(x).into(),
                        )),
                    ),
                    c,
                )
            }
            _ => todo!("{:?}", expr),
        }
    }

    fn convert_sequence(
        &'static self,
        items: Ref<[LExpr]>,
        c: impl 'static + FnOnce(Ref<[CVal]>) -> CExpr,
    ) -> CExpr {
        self.convert_sequence_recursion(items, Vec::with_capacity(items.len()), Box::new(c))
    }

    fn convert_sequence_recursion(
        &'static self,
        items: Ref<[LExpr]>,
        mut w: Vec<CVal>,
        c: Box<dyn FnOnce(Ref<[CVal]>) -> CExpr>,
    ) -> CExpr {
        if items.is_empty() {
            c(Ref::array(w))
        } else {
            self.convert(
                &items[0],
                Box::new(move |v| {
                    w.push(v);
                    self.convert_sequence_recursion(Ref::slice(&items.as_ref()[1..]), w, c)
                }),
            )
        }
    }

    fn gensym(&self, name: &str) -> Ref<str> {
        let n = self.sym_ctr.fetch_add(1, Ordering::Relaxed);
        Ref::from(format!("{name}{}{}", self.sym_delim, n))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{cps_expr, cps_expr_list, cps_ident_list, cps_value, cps_value_list, mini_expr};

    pub fn convert_program(expr: LExpr) -> CExpr {
        // for testing we need to generate symbols that are valid rust identifiers
        let ctx = Box::leak(Box::new(Context::new("__")));
        ctx.convert(
            &expr,
            Box::new(|x| CExpr::App(CVal::Halt, Ref::array(vec![x]))),
        )
    }

    #[test]
    fn convert_variable() {
        assert_eq!(convert_program(mini_expr!(foo)), cps_expr!(halt foo));
    }

    #[test]
    fn convert_constants() {
        assert_eq!(
            convert_program(mini_expr!((int 0))),
            cps_expr!(halt (int 0))
        );
        assert_eq!(
            convert_program(mini_expr!((real 0.0))),
            cps_expr!(halt (real 0.0))
        );
    }

    #[test]
    fn convert_records() {
        assert_eq!(convert_program(mini_expr!([])), cps_expr!(halt (int 0)));
        assert_eq!(
            convert_program(mini_expr!([(int 1)])),
            cps_expr!(record [(int 1)] r__0 (halt r__0))
        );
        assert_eq!(
            convert_program(mini_expr!([(int 1) x (int 3)])),
            cps_expr!(record [(int 1) x (int 3)] r__0 (halt r__0))
        );
        assert_eq!(
            convert_program(mini_expr!([[(int 1)]])),
            cps_expr!(record [(int 1)] r__1 (record [r__1] r__0 (halt r__0)))
        );
        assert_eq!(
            convert_program(mini_expr!([[(int 1)] [(int 2)]])),
            cps_expr!(record [(int 1)] r__1 (record [(int 2)] r__2 (record [r__1 r__2] r__0 (halt r__0))))
        );
    }

    #[test]
    fn convert_select() {
        assert_eq!(
            convert_program(mini_expr!(select [(int 1)] 0)),
            cps_expr!(record [(int 1)] r__1 (select 0 r__1 w__0 (halt w__0)))
        );
    }

    #[test]
    fn convert_primops() {
        assert_eq!(
            convert_program(mini_expr!(ineg int 1)),
            cps_expr!(- (int 1) [w__0] [(halt w__0)])
        );
        assert_eq!(
            convert_program(mini_expr!(ineg)),
            //cps_expr!(- (int 1) [w__0] [(halt w__0)])
            todo!()
        );
    }
}
