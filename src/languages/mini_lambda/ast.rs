use crate::core::reference::Ref;
use crate::core::sexpr;
use crate::core::sexpr::S;
use crate::languages::common_primops::PrimOp;
use sexpr_parser::Parser;
use std::fmt::Formatter;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr<V: 'static> {
    Var(V),
    Fn(V, Ref<Expr<V>>),
    Fix(Ref<[V]>, Ref<[Expr<V>]>, Ref<Expr<V>>),
    App(Ref<Expr<V>>, Ref<Expr<V>>),
    Int(i64),
    Real(f64),
    String(Ref<String>),
    Switch(
        Ref<Expr<V>>,
        Ref<[ConRep]>,
        Ref<[(Con, Expr<V>)]>,
        Option<Ref<Expr<V>>>,
    ),
    Con(ConRep, Ref<Expr<V>>),
    DeCon(ConRep, Ref<Expr<V>>),
    Record(Ref<[Expr<V>]>),
    Select(isize, Ref<Expr<V>>),
    Prim(PrimOp),
    Panic(&'static str),
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
                let crs = S::list(conreps.iter().map(|cr|cr.to_sexpr()).collect());
                let arms = S::list(arms.iter().map(|(c, arm)|S::list(vec![c.to_sexpr(), arm.to_sexpr()])).collect());
                let mut out = vec![S::symbol("switch"), val.to_sexpr(), crs, arms];
                if let Some(x) = default {
                    out.push(x.to_sexpr());
                }
                S::list(out)
            }
            Expr::Con(conrep, value) => {
                S::list(vec![S::symbol("con"), conrep.to_sexpr(), value.to_sexpr()])
            }
            _ => todo!("{:?}", self),
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
            Con::String(v) => S::String(Ref::new(v.to_string()))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::list;

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
        let expr = Expr::Switch(Expr::Int(42).into(), list![], list![], None);
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn serialize_switch_with_default() {
        let repr = "(switch 42 () () 123)";
        let expr = Expr::Switch(
            Expr::Int(42).into(),
            list![],
            list![],
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
            list![ConRep::Constant(1), ConRep::Tagged(2), ConRep::Transparent],
            list![],
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
            list![],
            list![
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
        todo!()
    }
}
