use std::rc::Rc;

#[derive(Debug, PartialEq)]
pub enum Expr {
    Int(i64),
    Real(f64),
    Ref(String),
    Apply(Rc<Expr>, Rc<Expr>),
    Lambda {
        param: String,
        ptype: TyExpr,
        rtype: TyExpr,
        body: Rc<Expr>,
    },
    Fix {
        fname: String,
        tvars: Vec<String>,
        param: String,
        ptype: TyExpr,
        rtype: TyExpr,
        fbody: Rc<Expr>,
        body: Rc<Expr>,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub enum TyExpr {
    Int,
    Real,
    Var(String),
    Fn(Rc<(TyExpr, TyExpr)>),
}
