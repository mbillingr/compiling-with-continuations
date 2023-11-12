use std::rc::Rc;

#[derive(Debug, PartialEq)]
pub enum Expr {
    Int(i64),
    Real(f64),
    Ref(String),
    Apply(Rc<(Expr, Expr)>),
    Lambda(Rc<Lambda>),
    Fix(Rc<(FixDef, Expr)>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum TyExpr {
    Int,
    Real,
    Var(String),
    Fn(Rc<(TyExpr, TyExpr)>),
}

#[derive(Debug, PartialEq)]
pub struct Lambda {
    pub param: String,
    pub body: Expr,
}

#[derive(Debug, PartialEq)]
pub struct FixDef {
    pub fname: String,
    pub tvars: Vec<String>,
    pub param: String,
    pub ptype: TyExpr,
    pub rtype: TyExpr,
    pub body: Expr,
}

impl Expr {
    pub fn int(x: impl Into<i64>) -> Self {
        Expr::Int(x.into())
    }

    pub fn real(x: impl Into<f64>) -> Self {
        Expr::Real(x.into())
    }

    pub fn var(name: impl ToString) -> Self {
        Expr::Ref(name.to_string())
    }

    pub fn apply(f: impl Into<Expr>, a: impl Into<Expr>) -> Self {
        Expr::Apply(Rc::new((f.into(), a.into())))
    }

    pub fn lambda<T>(p: impl ToString, body: T) -> Self
    where
        Expr: From<T>,
    {
        Expr::Lambda(Rc::new(Lambda {
            param: p.to_string(),
            body: body.into(),
        }))
    }

    pub fn fix<T>(def: impl Into<FixDef>, body: T) -> Self
    where
        Expr: From<T>,
    {
        Expr::Fix(Rc::new((def.into(), body.into())))
    }
}

impl FixDef {
    pub fn new<V, P, R, B>(
        fname: impl ToString,
        tvars: impl IntoIterator<Item = V>,
        ptype: P,
        rtype: R,
        param: impl ToString,
        body: B,
    ) -> Self
    where
        V: ToString,
        TyExpr: From<P>,
        TyExpr: From<R>,
        Expr: From<B>,
    {
        FixDef {
            fname: fname.to_string(),
            tvars: tvars.into_iter().map(|v| v.to_string()).collect(),
            param: param.to_string(),
            ptype: ptype.into(),
            rtype: rtype.into(),
            body: body.into(),
        }
    }
}

impl TyExpr {
    pub fn func<P, R>(p: P, r: R) -> Self
    where
        TyExpr: From<P>,
        TyExpr: From<R>,
    {
        TyExpr::Fn(Rc::new((p.into(), r.into())))
    }
}

impl From<&str> for Expr {
    fn from(value: &str) -> Self {
        Expr::Ref(value.to_string())
    }
}

impl From<i64> for Expr {
    fn from(value: i64) -> Self {
        Expr::Int(value)
    }
}

impl From<f64> for Expr {
    fn from(value: f64) -> Self {
        Expr::Real(value)
    }
}

impl From<&str> for TyExpr {
    fn from(value: &str) -> Self {
        TyExpr::Var(value.to_string())
    }
}
