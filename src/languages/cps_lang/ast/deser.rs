use super::{AccessPath as AP, Expr, Value};
use crate::core::reference::Ref;
use crate::core::sexpr::{S, SF};
use sexpr_parser::Parser;

impl std::fmt::Display for Expr<Ref<str>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_sexpr())
    }
}

impl Expr<Ref<str>> {
    pub fn from_str<'i>(src: &'i str) -> Result<Self, Error<'i>> {
        let sexpr = SF.parse(src)?;
        Self::from_sexpr(&sexpr)
    }

    pub fn from_sexpr(s: &S) -> Result<Self, Error<'static>> {
        use S::*;
        match s {
            List(Ref([Symbol(Ref("record")), List(Ref(fields)), Symbol(var), cnt])) => {
                let fields_out: Result<Vec<_>, _> = fields
                    .iter()
                    .map(|f| Value::from_sexpr(f).map(|f_| (f_, AP::Ref(0))))
                    .collect();
                Ok(Expr::Record(
                    Ref::array(fields_out?),
                    *var,
                    Ref::new(Self::from_sexpr(cnt)?),
                ))
            }

            List(Ref([Symbol(Ref("select")), Int(idx), rec, Symbol(var), cnt])) => {
                Ok(Expr::Select(
                    *idx as isize,
                    Value::from_sexpr(rec)?,
                    *var,
                    Ref::new(Self::from_sexpr(cnt)?),
                ))
            }

            List(Ref([Symbol(Ref("offset")), Int(idx), rec, Symbol(var), cnt])) => {
                Ok(Expr::Offset(
                    *idx as isize,
                    Value::from_sexpr(rec)?,
                    *var,
                    Ref::new(Self::from_sexpr(cnt)?),
                ))
            }

            List(Ref([Symbol(Ref("halt")), val])) => Ok(Expr::Halt(Value::from_sexpr(val)?)),

            List(Ref([rator, rands @ ..])) => {
                let rands_out: Result<Vec<_>, _> = rands.iter().map1(Value::from_sexpr).collect();
                Ok(Expr::App(Value::from_sexpr(rator)?, Ref::array(rands_out?)))
            }

            _ => todo!("{:?}", s),
        }
    }

    pub fn to_sexpr(&self) -> S {
        match self {
            Expr::Record(fields, var, cnt) => S::list(vec![
                S::symbol("record"),
                S::list(fields.iter().map(|(f, _)| f.to_sexpr()).collect()),
                S::Symbol(*var),
                cnt.to_sexpr(),
            ]),

            Expr::Select(idx, rec, var, cnt) => S::list(vec![
                S::symbol("select"),
                S::Int(*idx as i64),
                rec.to_sexpr(),
                S::Symbol(*var),
                cnt.to_sexpr(),
            ]),

            Expr::Offset(idx, rec, var, cnt) => S::list(vec![
                S::symbol("offset"),
                S::Int(*idx as i64),
                rec.to_sexpr(),
                S::Symbol(*var),
                cnt.to_sexpr(),
            ]),

            Expr::App(rator, rands) => {
                let mut items = vec![rator.to_sexpr()];
                items.extend(rands.iter().map(Value::to_sexpr));
                S::list(items)
            }

            Expr::Halt(val) => S::list(vec![S::symbol("halt"), val.to_sexpr()]),

            _ => todo!("{:?}", self),
        }
    }
}

impl Value<Ref<str>> {
    pub fn to_sexpr(&self) -> S {
        match self {
            Value::Var(v) => S::Symbol(*v),
            Value::Label(v) => S::list(vec![S::symbol("@"), S::Symbol(*v)]),
            Value::Int(v) => S::Int(*v),
            Value::Real(v) => S::Float(*v),
            Value::String(v) => S::String(*v),
        }
    }

    pub fn from_sexpr(s: &S) -> Result<Self, Error<'static>> {
        match s {
            S::Symbol(v) => Ok(Value::Var(*v)),
            S::List(Ref([S::Symbol(Ref("@")), S::Symbol(v)])) => Ok(Value::Label(*v)),
            S::Int(v) => Ok(Value::Int(*v)),
            S::Float(v) => Ok(Value::Real(*v)),
            S::String(v) => Ok(Value::String(*v)),
            _ => Err(Error::Syntax(s.clone())),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Error<'i> {
    ParseError(sexpr_parser::Error<'i>),
    Syntax(S),
}

impl<'i> From<sexpr_parser::Error<'i>> for Error<'i> {
    fn from(e: sexpr_parser::Error<'i>) -> Self {
        Error::ParseError(e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::list;

    #[test]
    fn record() {
        let repr = "(record (1 2) r (halt r))";
        let expr: Expr<Ref<str>> = Expr::Record(
            list![(Value::Int(1), AP::Ref(0)), (Value::Int(2), AP::Ref(0))],
            "r".into(),
            Expr::Halt(Value::Var("r".into())).into(),
        );
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn select() {
        let repr = "(select 0 r x (halt x))";
        let expr: Expr<Ref<str>> = Expr::Select(
            0,
            Value::Var("r".into()),
            "x".into(),
            Expr::Halt(Value::Var("x".into())).into(),
        );
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn offset() {
        let repr = "(offset 0 r x (halt x))";
        let expr: Expr<Ref<str>> = Expr::Offset(
            0,
            Value::Var("r".into()),
            "x".into(),
            Expr::Halt(Value::Var("x".into())).into(),
        );
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn app() {
        let repr = "(f x 1)";
        let expr: Expr<Ref<str>> = Expr::App(
            Value::Var("f".into()),
            list![Value::Var("x".into()), Value::Int(1)],
        );
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn fix() {
        todo!()
    }
}
