use crate::core::reference::Ref;
use crate::cps_expr;
use crate::languages::mini_lambda::ast;
use crate::languages::cps_lang::ast as cps;

type LExpr = ast::Expr<Ref<str>>;
type CExpr = cps::Expr<Ref<str>>;
type CVal = cps::Value<Ref<str>>;

pub fn convert_program(expr: LExpr) -> CExpr {
    Context::new().convert(expr, |x| CExpr::App(CVal::Halt, Ref::array(vec![x])))
}

struct Context {
    sym_ctr: usize,
}

impl Context {

    pub fn new() -> Self {
        Context {
            sym_ctr: 0
        }
    }
    pub fn convert(&mut self, expr: LExpr, c: impl Fn(CVal) -> CExpr) -> CExpr {
        match expr {
            LExpr::Var(v) => c(CVal::Var(v)),
            LExpr::Int(i) => c(CVal::Int(i)),
            LExpr::Real(r) => c(CVal::Real(r)),
            LExpr::Record(fields) if fields.len() == 0 => c(CVal::Int(0)),
            LExpr::Record(fields) => {
                let x = self.gensym("r");
                self.convert_(fields, |a| CExpr::Record(a, x, Ref::new(c(CVal::Var(x)))))
            }
            _ => todo!("{:?}", expr)
        }
    }

    fn convert_(&mut self, items: Ref<[LExpr]>, c: impl Fn(Ref<[CVal]>) -> CExpr) -> CExpr {
        let mut w = vec![];

        //self.convert(item, |v|))
        todo!();

        c(Ref::array(w))
    }

    fn gensym(&mut self, name: &str) -> Ref<str> {
        self.sym_ctr += 1;
        Ref::from(format!("{name}__{}", self.sym_ctr))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{cps_expr, cps_value, cps_value_list, mini_expr};

    #[test]
    fn convert_variable() {
        assert_eq!(convert_program(mini_expr!(foo)), cps_expr!(halt foo));
    }

    #[test]
    fn convert_constants() {
        assert_eq!(convert_program(mini_expr!((int 0))), cps_expr!(halt (int 0)));
        assert_eq!(convert_program(mini_expr!((real 0.0))), cps_expr!(halt (real 0.0)));
    }

    #[test]
    fn convert_records() {
        assert_eq!(convert_program(mini_expr!([])), cps_expr!(halt (int 0)));
        assert_eq!(convert_program(mini_expr!([(int 1)])), cps_expr!(record [(int 1)] r (halt r)));
        //assert_eq!(convert_program(mini_expr!((real 0.0))), cps_expr!(halt (real 0.0)));
    }
}