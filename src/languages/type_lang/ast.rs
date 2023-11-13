use std::rc::Rc;

#[derive(Debug, PartialEq)]
pub enum Expr {
    /// Integer constant
    Int(i64),

    /// Real constant
    Real(f64),

    /// Variable reference
    Ref(String),

    /// Function application
    Apply(Rc<(Self, Self)>),

    /// Enum variant construction
    Cons(Rc<(String, String, Vec<Self>)>),

    /// Enum deconstruction (will be replaced by pattern matching)
    Decons(Rc<(Self, String, Vec<String>, Self, Self)>),

    /// Anonymous function
    Lambda(Rc<Lambda<Self>>),

    /// Definition scope
    Defs(Rc<(Vec<Def>, Self)>),

    /// Placeholders for more general primitives
    Add(Rc<(Self, Self)>),
    Read(),
    Show(Rc<Self>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum TyExpr {
    Int,
    Real,
    Var(String),
    Fn(Rc<(TyExpr, TyExpr)>),
}

#[derive(Debug, PartialEq)]
pub struct Lambda<E> {
    pub param: String,
    pub body: E,
}

#[derive(Debug, PartialEq)]
pub enum Def {
    Func(FnDef),
    Enum(EnumDef),
}

#[derive(Debug, PartialEq)]
pub struct FnDef {
    pub fname: String,
    pub tvars: Vec<String>,
    pub param: String,
    pub ptype: TyExpr,
    pub rtype: TyExpr,
    pub body: Expr,
}

#[derive(Debug, PartialEq)]
pub struct EnumDef {
    pub tname: String,
    pub variants: Vec<EnumVariant>,
}

#[derive(Debug, PartialEq)]
pub enum EnumVariant {
    Constant(String),
    Constructor(String, TyExpr),
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

    pub fn cons(ety: impl ToString, variant: impl ToString, args: impl ListBuilder<Expr>) -> Self {
        Expr::Cons(Rc::new((
            ety.to_string(),
            variant.to_string(),
            args.build(),
        )))
    }

    pub fn decons(
        value: impl Into<Expr>,
        variant: impl ToString,
        vars: impl ListBuilder<String>,
        matches: impl Into<Expr>,
        mismatch: impl Into<Expr>,
    ) -> Self {
        Expr::Decons(Rc::new((
            value.into(),
            variant.to_string(),
            vars.build(),
            matches.into(),
            mismatch.into(),
        )))
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

    pub fn defs<T>(defs: impl Into<Vec<Def>>, body: T) -> Self
    where
        Expr: From<T>,
    {
        Expr::Defs(Rc::new((defs.into(), body.into())))
    }

    pub fn add(a: impl Into<Expr>, b: impl Into<Expr>) -> Self {
        Expr::Add(Rc::new((a.into(), b.into())))
    }
}

impl Def {
    pub fn func<V, P, R, B>(
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
        Def::Func(FnDef {
            fname: fname.to_string(),
            tvars: tvars.into_iter().map(|v| v.to_string()).collect(),
            param: param.to_string(),
            ptype: ptype.into(),
            rtype: rtype.into(),
            body: body.into(),
        })
    }

    pub fn enum_(tname: impl ToString, variants: impl ListBuilder<EnumVariant>) -> Self {
        Def::Enum(EnumDef {
            tname: tname.to_string(),
            variants: variants.build(),
        })
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

impl From<&str> for EnumVariant {
    fn from(name: &str) -> Self {
        EnumVariant::Constant(name.into())
    }
}

impl From<(&str, TyExpr)> for EnumVariant {
    fn from((name, ty): (&str, TyExpr)) -> Self {
        EnumVariant::Constructor(name.into(), ty)
    }
}

pub trait ListBuilder<T> {
    fn build(self) -> Vec<T>
    where
        Self: Sized,
    {
        let mut list = vec![];
        self.build_into(&mut list);
        list
    }
    fn build_into(self, buf: &mut Vec<T>);
}

impl<T> ListBuilder<T> for Vec<T> {
    fn build(self) -> Vec<T>
    where
        Self: Sized,
    {
        self
    }

    fn build_into(self, buf: &mut Vec<T>) {
        buf.extend(self)
    }
}

impl<T> ListBuilder<T> for () {
    fn build_into(self, _: &mut Vec<T>) {}
}

impl<A, OUT> ListBuilder<OUT> for (A,)
where
    A: Into<OUT>,
{
    fn build_into(self, buf: &mut Vec<OUT>) {
        buf.push(self.0.into());
    }
}

impl<A, Z, OUT> ListBuilder<OUT> for (A, Z)
where
    Z: ListBuilder<OUT>,
    A: Into<OUT>,
{
    fn build_into(self, buf: &mut Vec<OUT>) {
        buf.push(self.0.into());
        self.1.build_into(buf);
    }
}

impl<A, B, Z, OUT> ListBuilder<OUT> for (A, B, Z)
where
    Z: ListBuilder<OUT>,
    A: Into<OUT>,
    B: Into<OUT>,
{
    fn build_into(self, buf: &mut Vec<OUT>) {
        buf.push(self.0.into());
        buf.push(self.1.into());
        self.2.build_into(buf);
    }
}

impl<A, OUT, const N: usize> ListBuilder<OUT> for [A; N]
where
    A: Into<OUT>,
{
    fn build_into(self, buf: &mut Vec<OUT>) {
        buf.extend(self.into_iter().map(|x| x.into()))
    }
}
