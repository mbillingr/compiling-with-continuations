use crate::core::reference::Ref;
use crate::core::sexpr;
use crate::core::sexpr::S;
use crate::languages::common_primops::PrimOp;
use sexpr_parser::Parser;
use std::fmt::Formatter;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr<V: 'static> {
    /// variable reference
    Var(V),

    /// anonymous function
    Fn(V, Ref<Expr<V>>),

    /// mutually recursive function definitions
    Fix(Ref<[V]>, Ref<[Expr<V>]>, Ref<Expr<V>>),

    /// function application
    App(Ref<Expr<V>>, Ref<Expr<V>>),

    /// integer constant
    Int(i64),

    /// floating point constant
    Real(f64),

    /// string constant
    String(Ref<String>),

    /// generic branching
    Switch(
        Ref<Expr<V>>,
        Ref<[ConRep]>,
        Ref<[(Con, Expr<V>)]>,
        Option<Ref<Expr<V>>>,
    ),

    /// variant type construction
    Con(ConRep, Ref<Expr<V>>),

    /// variant type deconstruction
    DeCon(ConRep, Ref<Expr<V>>),

    /// record construction
    Record(Ref<[Expr<V>]>),

    /// record field access
    Select(isize, Ref<Expr<V>>),

    /// primitive
    Prim(PrimOp),

    /// variable binding
    Let(V, Ref<Expr<V>>, Ref<Expr<V>>),

    /// print an integer
    ShowInt(Ref<Expr<V>>),

    /// print a real number
    ShowReal(Ref<Expr<V>>),

    /// print a string
    ShowStr(Ref<Expr<V>>),

    /// abort with a message
    Panic(Ref<str>),
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum ConRep {
    Tagged(usize),
    Constant(usize),
    Transparent,
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Con {
    Data(ConRep),
    Int(i64),
    Real(f64),
    String(Ref<str>),
}

#[derive(Debug, PartialEq)]
pub enum Error<'i> {
    ParseError(sexpr_parser::Error<'i>),
    Syntax(sexpr::S),
}

impl<'i> From<sexpr_parser::Error<'i>> for Error<'i> {
    fn from(e: sexpr_parser::Error<'i>) -> Self {
        Error::ParseError(e)
    }
}

impl<V> Expr<V> {
    pub fn int(x: impl Into<i64>) -> Self {
        Expr::Int(x.into())
    }

    pub fn real(x: impl Into<f64>) -> Self {
        Expr::Real(x.into())
    }

    pub fn string(x: impl Into<Ref<String>>) -> Self {
        Expr::String(x.into())
    }

    pub fn var(x: impl Into<V>) -> Self {
        Self::Var(x.into())
    }

    pub fn apply(f: impl Into<Ref<Self>>, arg: impl Into<Ref<Self>>) -> Self {
        Self::App(f.into(), arg.into())
    }

    pub fn func(param: impl Into<V>, body: impl Into<Ref<Self>>) -> Self {
        Self::Fn(param.into(), body.into())
    }

    pub fn fix(
        names: impl Into<Ref<[V]>>,
        fns: impl Into<Ref<[Self]>>,
        body: impl Into<Ref<Self>>,
    ) -> Self {
        Self::Fix(names.into(), fns.into(), body.into())
    }

    pub fn record(fields: impl Into<Ref<[Self]>>) -> Self {
        Self::Record(fields.into())
    }

    pub fn con(rep: impl Into<ConRep>, val: impl Into<Ref<Self>>) -> Self {
        Self::Con(rep.into(), val.into())
    }

    pub fn decon(rep: impl Into<ConRep>, val: impl Into<Self>) -> Self {
        Self::DeCon(rep.into(), val.into().into())
    }

    pub fn switch<D: Into<Self>>(
        val: impl Into<Self>,
        conreps: impl Into<Ref<[ConRep]>>,
        arms: impl Into<Vec<(Con, Self)>>,
        default: Option<D>,
    ) -> Self {
        Self::Switch(
            val.into().into(),
            conreps.into(),
            Ref::array(arms.into()),
            default.map(D::into).map(Ref::new),
        )
    }

    pub fn select(idx: isize, rec: impl Into<Self>) -> Self {
        Self::Select(idx.into(), rec.into().into())
    }

    pub fn bind(name: impl Into<V>, value: impl Into<Self>, body: impl Into<Self>) -> Self {
        Self::Let(name.into(), value.into().into(), body.into().into())
    }
}

impl<V: From<&'static str>> Expr<V> {
    pub fn sequence(exprs: Vec<Self>) -> Self {
        exprs
            .into_iter()
            .rev()
            .reduce(|acc, x| Self::apply(Self::func("_", acc), x))
            .unwrap()
    }
}

impl Expr<Ref<str>> {
    pub fn from_str<'i>(s: &'i str) -> Result<Self, Error<'i>> {
        let sexpr = sexpr::SF.parse(s)?;
        Self::from_sexpr(&sexpr)
    }

    pub fn to_sexpr(&self) -> S {
        match self {
            Expr::Var(v) => S::Symbol(*v),
            Expr::Fn(var, body) => S::list(vec![S::symbol("fn"), S::Symbol(*var), body.to_sexpr()]),
            Expr::Fix(fnames, fns, body) => {
                let defs: Vec<_> = fns
                    .iter()
                    .map(|f| f.to_sexpr())
                    .zip(fnames.iter())
                    .map(|(f, name)| f.replace_head(S::Symbol(*name)))
                    .collect();
                S::list(vec![S::symbol("fix"), S::list(defs), body.to_sexpr()])
            }
            Expr::App(rator, rand) => S::list(vec![rator.to_sexpr(), rand.to_sexpr()]),
            Expr::Int(i) => S::Int(*i),
            Expr::Real(v) => S::Float(*v),
            Expr::String(v) => S::String(*v),
            Expr::Switch(val, conreps, arms, default) => {
                let crs = S::list(conreps.iter().map(|cr| cr.to_sexpr()).collect());
                let arms = S::list(
                    arms.iter()
                        .map(|(c, arm)| S::list(vec![c.to_sexpr(), arm.to_sexpr()]))
                        .collect(),
                );
                let mut out = vec![S::symbol("switch"), val.to_sexpr(), crs, arms];
                if let Some(x) = default {
                    out.push(x.to_sexpr());
                }
                S::list(out)
            }
            Expr::Con(conrep, value) => {
                S::list(vec![S::symbol("con"), conrep.to_sexpr(), value.to_sexpr()])
            }
            Expr::DeCon(conrep, value) => S::list(vec![
                S::symbol("decon"),
                conrep.to_sexpr(),
                value.to_sexpr(),
            ]),
            Expr::Record(fields) => {
                let mut fields_out = vec![S::symbol("record")];
                fields_out.extend(fields.iter().map(Self::to_sexpr));
                S::list(fields_out)
            }
            Expr::Select(idx, rec) => S::list(vec![
                S::symbol("select"),
                S::Int(*idx as i64),
                rec.to_sexpr(),
            ]),
            Expr::Let(var, val, body) => S::list(vec![
                S::symbol("let"),
                S::list(vec![S::Symbol(*var), val.to_sexpr()]),
                body.to_sexpr(),
            ]),
            Expr::ShowInt(value) => S::list(vec![S::symbol("show-int"), value.to_sexpr()]),
            Expr::ShowReal(value) => S::list(vec![S::symbol("show-real"), value.to_sexpr()]),
            Expr::ShowStr(value) => S::list(vec![S::symbol("show-string"), value.to_sexpr()]),
            Expr::Prim(op) => S::list(vec![S::symbol("primitive"), S::symbol(op.to_str())]),
            Expr::Panic(msg) => {
                S::list(vec![S::symbol("panic!"), S::String(msg.to_string().into())])
            }
        }
    }

    pub fn from_sexpr(s: &sexpr::S) -> Result<Self, Error<'static>> {
        use sexpr::S::*;
        match s {
            Int(x) => Ok(Expr::Int(*x)),
            Float(x) => Ok(Expr::Real(*x)),
            Symbol(s) => Ok(Expr::Var(*s)),
            String(s) => Ok(Expr::String(*s)),

            List(Ref([Symbol(Ref("fn")), Symbol(var), body])) => {
                Ok(Expr::Fn(*var, Ref::new(Self::from_sexpr(body)?)))
            }

            List(Ref([Symbol(Ref("fix")), List(Ref(fns)), body])) => Self::parse_fix(fns, body),

            List(Ref(
                [Symbol(Ref("switch")), val, List(Ref([conreps @ ..])), List(Ref([arms @ ..]))],
            )) => Self::parse_switch(val, conreps, arms, None),
            List(Ref(
                [Symbol(Ref("switch")), val, List(Ref([conreps @ ..])), List(Ref([arms @ ..])), default],
            )) => Self::parse_switch(val, conreps, arms, Some(default)),

            List(Ref([Symbol(Ref("con")), conrep, value])) => Ok(Expr::Con(
                ConRep::from_sexpr(conrep)?,
                Ref::new(Self::from_sexpr(value)?),
            )),

            List(Ref([Symbol(Ref("decon")), conrep, value])) => Ok(Expr::DeCon(
                ConRep::from_sexpr(conrep)?,
                Ref::new(Self::from_sexpr(value)?),
            )),

            List(Ref([Symbol(Ref("record")), fields @ ..])) => {
                let fields_out: Result<Vec<_>, _> = fields.iter().map(Self::from_sexpr).collect();
                Ok(Expr::Record(Ref::array(fields_out?)))
            }

            List(Ref([Symbol(Ref("select")), Int(idx), rec])) => Ok(Expr::Select(
                *idx as isize,
                Ref::new(Self::from_sexpr(rec)?),
            )),

            List(Ref([Symbol(Ref("let")), List(Ref([Symbol(var), val])), body])) => Ok(Expr::Let(
                *var,
                Ref::new(Self::from_sexpr(val)?),
                Ref::new(Self::from_sexpr(body)?),
            )),

            List(Ref([Symbol(Ref("primitive")), Symbol(Ref(op))]))
                if PrimOp::from_str(op).is_some() =>
            {
                Ok(Expr::Prim(PrimOp::from_str(op).unwrap()))
            }

            List(Ref([Symbol(Ref("panic!")), String(msg)])) => {
                Ok(Expr::Panic(msg.to_string().into()))
            }

            List(Ref([rator, rand])) => Ok(Expr::App(
                Ref::new(Self::from_sexpr(rator)?),
                Ref::new(Self::from_sexpr(rand)?),
            )),

            _ => Err(Error::Syntax(s.clone())),
        }
    }

    fn parse_fix(fns: &[S], body: &S) -> Result<Expr<Ref<str>>, Error<'static>> {
        use sexpr::S::*;

        let vars: Result<Vec<Ref<str>>, _> = fns
            .iter()
            .map(|f| {
                if let List(Ref([Symbol(fname), _, _])) = f {
                    Ok(*fname)
                } else {
                    Err(Error::Syntax(f.clone()))
                }
            })
            .collect();

        let funcs: Result<Vec<Expr<Ref<str>>>, _> = fns
            .iter()
            .map(|f| {
                if let List(Ref([_, Symbol(v), b])) = f {
                    Ok(Expr::Fn(v.clone(), Ref::new(Self::from_sexpr(b)?)))
                } else {
                    Err(Error::Syntax(f.clone()))
                }
            })
            .collect();

        Ok(Expr::Fix(
            Ref::array(vars?),
            Ref::array(funcs?),
            Ref::new(Self::from_sexpr(body)?),
        ))
    }

    fn parse_switch(
        val: &S,
        conreps: &[sexpr::S],
        arms: &[sexpr::S],
        default: Option<&sexpr::S>,
    ) -> Result<Expr<Ref<str>>, Error<'static>> {
        use sexpr::S::*;

        let conreps_out: Result<Vec<_>, _> = conreps.iter().map(ConRep::from_sexpr).collect();
        let arms_out: Result<Vec<_>, _> = arms
            .iter()
            .map(|arm| {
                if let List(Ref([con, then])) = arm {
                    Ok((Con::from_sexpr(con)?, Expr::from_sexpr(then)?))
                } else {
                    Err(Error::Syntax(arm.clone()))
                }
            })
            .collect();

        let d_out = match default {
            None => None,
            Some(d) => Some(Ref::new(Self::from_sexpr(d)?)),
        };

        Ok(Expr::Switch(
            Ref::new(Self::from_sexpr(val)?),
            Ref::array(conreps_out?),
            Ref::array(arms_out?),
            d_out,
        ))
    }
}

impl ConRep {
    pub fn from_sexpr(s: &sexpr::S) -> Result<Self, Error<'static>> {
        use sexpr::S::*;
        match s {
            Symbol(Ref("transparent")) => Ok(ConRep::Transparent),
            List(Ref([Symbol(Ref("const")), Int(c)])) => Ok(ConRep::Constant(*c as usize)),
            List(Ref([Symbol(Ref("tag")), Int(c)])) => Ok(ConRep::Tagged(*c as usize)),
            _ => Err(Error::Syntax(s.clone())),
        }
    }

    pub fn to_sexpr(&self) -> S {
        match self {
            ConRep::Transparent => S::symbol("transparent"),
            ConRep::Constant(c) => S::list(vec![S::symbol("const"), S::Int(*c as i64)]),
            ConRep::Tagged(c) => S::list(vec![S::symbol("tag"), S::Int(*c as i64)]),
        }
    }
}

impl Con {
    pub fn from_sexpr(s: &sexpr::S) -> Result<Self, Error<'static>> {
        use sexpr::S::*;
        match s {
            Int(x) => Ok(Con::Int(*x)),
            Float(x) => Ok(Con::Real(*x)),
            String(x) => Ok(Con::String((**x).clone().into())),
            Symbol(Ref("transparent")) => Ok(Con::Data(ConRep::Transparent)),
            List(Ref([Symbol(Ref("const")), Int(c)])) => {
                Ok(Con::Data(ConRep::Constant(*c as usize)))
            }
            List(Ref([Symbol(Ref("tag")), Int(c)])) => Ok(Con::Data(ConRep::Tagged(*c as usize))),
            _ => Err(Error::Syntax(s.clone())),
        }
    }

    pub fn to_sexpr(&self) -> S {
        match self {
            Con::Data(cr) => cr.to_sexpr(),
            Con::Int(v) => S::Int(*v),
            Con::Real(v) => S::Float(*v),
            Con::String(v) => S::String(Ref::new(v.to_string())),
        }
    }
}

impl std::fmt::Display for Expr<Ref<str>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_sexpr())
    }
}

impl std::fmt::Display for ConRep {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ConRep::Constant(c) => write!(f, "(const {})", c),
            ConRep::Tagged(t) => write!(f, "(tag {})", t),
            ConRep::Transparent => write!(f, "transparent"),
        }
    }
}

impl std::fmt::Display for Con {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Con::Data(c) => write!(f, "{}", c),
            Con::Int(x) => write!(f, "{}", x),
            Con::Real(x) => write!(f, "{}", x),
            Con::String(x) => write!(f, "{}", x),
        }
    }
}

impl<V> From<PrimOp> for Expr<V> {
    fn from(op: PrimOp) -> Self {
        Expr::Prim(op)
    }
}

impl<V> From<PrimOp> for Ref<Expr<V>> {
    fn from(op: PrimOp) -> Self {
        Ref::new(Expr::Prim(op))
    }
}

impl<V> From<i64> for Expr<V> {
    fn from(c: i64) -> Self {
        Expr::Int(c)
    }
}

impl<V> From<i64> for Ref<Expr<V>> {
    fn from(c: i64) -> Self {
        Ref::new(Expr::Int(c))
    }
}

impl<V> From<&'static str> for Expr<V>
where
    &'static str: Into<V>,
{
    fn from(v: &'static str) -> Self {
        Expr::Var(v.into())
    }
}

impl<V> From<&'static str> for Ref<Expr<V>>
where
    &'static str: Into<V>,
{
    fn from(v: &'static str) -> Self {
        Ref::new(Expr::Var(v.into()))
    }
}

impl From<Ref<str>> for Expr<Ref<str>> {
    fn from(v: Ref<str>) -> Self {
        Expr::Var(v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::array;

    #[test]
    fn serialize_int() {
        assert_eq!(Expr::from_str("42"), Ok(Expr::Int(42)));
        assert_eq!(Expr::Int(123).to_string(), "123");
    }

    #[test]
    fn serialize_float() {
        assert_eq!(Expr::from_str("12.34"), Ok(Expr::Real(12.34)));
        assert_eq!(Expr::Real(3.14).to_string(), "3.14");
    }

    #[test]
    fn serialize_string() {
        assert_eq!(
            Expr::from_str("\"hello\""),
            Ok(Expr::String(Ref::new("hello".to_string())))
        );
        assert_eq!(
            Expr::String(Ref::new("world".to_string())).to_string(),
            "\"world\""
        );
    }

    #[test]
    fn serialize_var() {
        assert_eq!(Expr::from_str("foo"), Ok(Expr::Var("foo".into())));
        assert_eq!(Expr::Var("bar".into()).to_string(), "bar");
    }

    #[test]
    fn serialize_fn() {
        let repr = "(fn var 42)";
        let expr = Expr::Fn("var".into(), Expr::Int(42).into());
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn serialize_fix() {
        let repr = "(fix ((foo x 1) (bar y 2)) 3)";
        let expr = Expr::Fix(
            Ref::array(vec!["foo".into(), "bar".into()]),
            Ref::array(vec![
                Expr::Fn("x".into(), Expr::Int(1).into()),
                Expr::Fn("y".into(), Expr::Int(2).into()),
            ]),
            Expr::Int(3).into(),
        );
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn serialize_app() {
        let repr = "(foo bar)";
        let expr = Expr::App(
            Expr::Var("foo".into()).into(),
            Expr::Var("bar".into()).into(),
        );
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn serialize_switch() {
        let repr = "(switch 42 () ())";
        let expr = Expr::Switch(Expr::Int(42).into(), array![], array![], None);
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn serialize_switch_with_default() {
        let repr = "(switch 42 () () 123)";
        let expr = Expr::Switch(
            Expr::Int(42).into(),
            array![],
            array![],
            Some(Expr::Int(123).into()),
        );
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn serialize_switch_with_conreps() {
        let repr = "(switch 42 ((const 1) (tag 2) transparent) ())";
        let expr = Expr::Switch(
            Expr::Int(42).into(),
            array![ConRep::Constant(1), ConRep::Tagged(2), ConRep::Transparent],
            array![],
            None,
        );
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn serialize_switch_with_arms() {
        let repr = "(switch 42 () ((transparent 0) ((tag 4) 0) (7 1)))";
        let expr = Expr::Switch(
            Expr::Int(42).into(),
            array![],
            array![
                (Con::Data(ConRep::Transparent), Expr::Int(0).into()),
                (Con::Data(ConRep::Tagged(4)), Expr::Int(0).into()),
                (Con::Int(7), Expr::Int(1).into())
            ],
            None,
        );
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn serialize_con() {
        let repr = "(con transparent 5)";
        let expr = Expr::Con(ConRep::Transparent, Expr::Int(5).into());
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn serialize_decon() {
        let repr = "(decon transparent 5)";
        let expr = Expr::DeCon(ConRep::Transparent, Expr::Int(5).into());
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn serialize_record() {
        let repr = "(record 1 2)";
        let expr = Expr::Record(array![Expr::Int(1), Expr::Int(2)]);
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn serialize_select() {
        let repr = "(select 0 r)";
        let expr = Expr::Select(0, Ref::new(Expr::Var("r".into())));
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn serialize_primitive_op() {
        let repr = "(primitive call/cc)";
        let expr = Expr::Prim(PrimOp::CallCC);
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn serialize_panic() {
        let repr = "(panic! \"WAAAA!!\")";
        let expr = Expr::Panic("WAAAA!!".into());
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }
}
