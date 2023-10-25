use super::{AccessPath as AP, AccessPath, Expr, Value};
use crate::core::reference::Ref;
use crate::core::sexpr::{S, SF};
use crate::languages::common_primops::PrimOp;
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
            List(Ref([Symbol(Ref("record")), List(Ref(faps)), Symbol(var), cnt])) => {
                let fields_out: Result<Vec<_>, _> =
                    faps.iter().map(Self::sexpr_to_fieldaccess).collect();
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

            List(Ref([Symbol(Ref("fix")), List(Ref(defs)), cnt])) => {
                let defs_out: Result<Vec<_>, _> = defs.iter().map(Self::sexpr_to_def).collect();
                Ok(Expr::Fix(
                    Ref::array(defs_out?),
                    Ref::new(Expr::from_sexpr(cnt)?),
                ))
            }

            List(Ref([Symbol(Ref("switch")), val, arms @ ..])) => {
                let arms_out: Result<Vec<_>, _> = arms
                    .iter()
                    .map(|x| Expr::from_sexpr(x).map(Ref::new))
                    .collect();
                Ok(Expr::Switch(Value::from_sexpr(val)?, Ref::array(arms_out?)))
            }

            List(Ref(
                [Symbol(Ref("primop")), sop @ Symbol(Ref(op)), List(args), List(vars), List(cnts)],
            )) => Ok(Expr::PrimOp(
                PrimOp::from_str(op).ok_or_else(|| Error::Syntax(sop.clone()))?,
                Ref::array(
                    args.iter()
                        .map(Value::from_sexpr)
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                Ref::array(
                    vars.iter()
                        .map(|s| s.try_symbol().ok_or_else(|| Error::Syntax(sop.clone())))
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                Ref::array(
                    cnts.iter()
                        .map(|c| Expr::from_sexpr(c).map(Ref::new))
                        .collect::<Result<Vec<_>, _>>()?,
                ),
            )),

            List(Ref([Symbol(Ref("halt")), val])) => Ok(Expr::Halt(Value::from_sexpr(val)?)),

            List(Ref([Symbol(Ref("panic")), String(msg)])) => {
                Ok(Expr::Panic(msg.to_string().into()))
            }

            List(Ref([rator, rands @ ..])) => {
                let rands_out: Result<Vec<_>, _> = rands.iter().map(Value::from_sexpr).collect();
                Ok(Expr::App(Value::from_sexpr(rator)?, Ref::array(rands_out?)))
            }

            _ => Err(Error::Syntax(s.clone())),
        }
    }

    fn sexpr_to_fieldaccess(fap: &S) -> Result<(Value<Ref<str>>, AccessPath), Error<'static>> {
        use S::*;
        match fap {
            List(Ref([f, ap])) => Ok((Value::from_sexpr(f)?, AccessPath::from_sexpr(ap)?)),
            f => Ok((Value::from_sexpr(f)?, AccessPath::Ref(0))),
            _ => Err(Error::Syntax(fap.clone())),
        }
    }

    fn sexpr_to_def(d: &S) -> Result<(Ref<str>, Ref<[Ref<str>]>, Ref<Self>), Error<'static>> {
        use S::*;
        match d {
            List(Ref([Symbol(fname), List(fargs), fbody])) => {
                let mut params = vec![];
                for p in fargs.iter() {
                    match p {
                        Symbol(s) => params.push(*s),
                        _ => return Err(Error::Syntax(p.clone())),
                    }
                }
                Ok((
                    *fname,
                    Ref::array(params),
                    Ref::new(Self::from_sexpr(fbody)?),
                ))
            }
            _ => Err(Error::Syntax(d.clone())),
        }
    }

    pub fn to_sexpr(&self) -> S {
        match self {
            Expr::Record(fields, var, cnt) => S::list(vec![
                S::symbol("record"),
                S::list(fields.iter().map(|(f, ap)| ap.to_sexpr(f)).collect()),
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

            Expr::Fix(defs, cnt) => {
                let defs_out: Vec<_> = defs
                    .iter()
                    .map(|(fname, fargs, fbody)| {
                        S::list(vec![
                            S::Symbol(*fname),
                            S::list(fargs.iter().copied().map(S::Symbol).collect()),
                            fbody.to_sexpr(),
                        ])
                    })
                    .collect();
                S::list(vec![S::symbol("fix"), S::list(defs_out), cnt.to_sexpr()])
            }

            Expr::Switch(val, arms) => {
                let mut items = vec![S::symbol("switch"), val.to_sexpr()];
                items.extend(arms.iter().map(|x| x.to_sexpr()));
                S::list(items)
            }

            Expr::PrimOp(op, args, vars, cnts) => S::list(vec![
                S::symbol("primop"),
                S::Symbol(Ref(op.to_str())),
                S::list(args.iter().map(Value::to_sexpr).collect()),
                S::list(vars.iter().copied().map(S::Symbol).collect()),
                S::list(cnts.iter().map(|c| c.to_sexpr()).collect()),
            ]),

            Expr::Halt(val) => S::list(vec![S::symbol("halt"), val.to_sexpr()]),

            Expr::Panic(msg) => {
                S::list(vec![S::symbol("panic"), S::String(msg.to_string().into())])
            }
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

impl AccessPath {
    pub fn to_sexpr(&self, val: &Value<Ref<str>>) -> S {
        match self {
            AccessPath::Ref(0) => val.to_sexpr(),
            _ => S::list(vec![val.to_sexpr(), self.to_sexpr_()]),
        }
    }

    fn to_sexpr_(&self) -> S {
        match self {
            AccessPath::Ref(i) => S::list(vec![S::symbol("ref"), S::Int(*i as i64)]),
            AccessPath::Sel(i, ap) => {
                S::list(vec![S::symbol("sel"), S::Int(*i as i64), ap.to_sexpr_()])
            }
        }
    }

    pub fn from_sexpr(s: &S) -> Result<Self, Error<'static>> {
        match s {
            S::List(Ref([S::Symbol(Ref("ref")), S::Int(i)])) => Ok(AccessPath::Ref(*i as isize)),
            S::List(Ref([S::Symbol(Ref("sel")), S::Int(i), ap])) => Ok(AccessPath::Sel(
                *i as isize,
                Ref::new(AccessPath::from_sexpr(ap)?),
            )),
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
    use crate::languages::common_primops::PrimOp;
    use crate::list;

    #[test]
    fn record() {
        let repr = "(record ((11 (ref 1)) (22 (ref 2))) r (halt r))";
        let expr: Expr<Ref<str>> = Expr::Record(
            list![(Value::Int(11), AP::Ref(1)), (Value::Int(22), AP::Ref(2))],
            "r".into(),
            Expr::Halt(Value::Var("r".into())).into(),
        );
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));

        let repr = "(record (11 22) r (halt r))";
        let expr: Expr<Ref<str>> = Expr::Record(
            list![(Value::Int(11), AP::Ref(0)), (Value::Int(22), AP::Ref(0))],
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
        let repr = "(fix ((foo (x y) (halt 1))) (halt 0))";
        let expr: Expr<Ref<str>> = Expr::Fix(
            list![(
                "foo".into(),
                list!["x".into(), "y".into()],
                Expr::Halt(Value::Int(1)).into()
            )],
            Expr::Halt(Value::Int(0)).into(),
        );
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn switch() {
        let repr = "(switch 0 (halt 1) (halt 0))";
        let expr: Expr<Ref<str>> = Expr::Switch(
            Value::Int(0),
            list![
                Expr::Halt(Value::Int(1)).into(),
                Expr::Halt(Value::Int(0)).into()
            ],
        );
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn primop() {
        let repr = "(primop + (1 2) (res) ((halt res)))";
        let expr: Expr<Ref<str>> = Expr::PrimOp(
            PrimOp::IAdd,
            list![Value::Int(1), Value::Int(2)],
            list!["res".into()],
            list![Ref::new(Expr::Halt(Value::Var("res".into())))],
        );
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn halt() {
        let repr = "(halt 42)";
        let expr: Expr<Ref<str>> = Expr::Halt(Value::Int(42));
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn panics() {
        let repr = "(panic \":(\")";
        let expr: Expr<Ref<str>> = Expr::Panic(":(".into());
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }
}
