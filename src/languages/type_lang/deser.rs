use crate::core::reference::Ref;
use crate::core::sexpr::{S, SF};
use crate::languages::type_lang::ast::{
    Def, EnumDef, EnumMatchArm, EnumVariant, EnumVariantPattern, Expr, FnDecl, IntDef, TyExpr,
};
use sexpr_parser::Parser;
use std::iter::once;
use std::rc::Rc;

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_sexpr())
    }
}

impl Expr {
    pub fn from_str<'i>(src: &'i str) -> Result<Self, Error<'i>> {
        let sexpr = SF.parse(src)?;
        Self::from_sexpr(&sexpr)
    }

    pub fn from_sexpr(s: &S) -> Result<Self, Error<'static>> {
        use S::*;
        match s {
            Int(x) => Ok(Expr::int(*x)),

            Float(x) => Ok(Expr::real(*x)),

            String(x) => Ok(Expr::string(&**x)),

            Symbol(x) => Ok(Expr::var(&**x)),

            List(Ref([Symbol(Ref("record")), fields @ ..])) => fields
                .iter()
                .map(|f| Self::from_sexpr(f))
                .collect::<Result<Vec<_>, _>>()
                .map(Expr::record),

            List(Ref([Symbol(Ref("select")), Int(idx), rec])) => {
                Self::from_sexpr(rec).map(|r| Self::select(*idx as usize, r))
            }

            List(Ref([enum_, Symbol(Ref(".")), Symbol(Ref(variant))])) => {
                let etx = TyExpr::from_sexpr(enum_)?;
                Ok(Expr::cons(etx, variant))
            }

            List(Ref([Symbol(Ref("match-enum")), val, arms @ ..])) => arms
                .iter()
                .map(|arm| match arm {
                    List(Ref([Symbol(v), Symbol(Ref("=>")), branch])) => {
                        Ok((EnumVariantPattern::constant(v), Self::from_sexpr(branch)?))
                    }
                    List(Ref([List(Ref([Symbol(v), xs @ ..])), Symbol(Ref("=>")), branch])) => {
                        Ok((
                            EnumVariantPattern::constructor(v, parse_symbol_list(xs)?),
                            Self::from_sexpr(branch)?,
                        ))
                    }
                    _ => Err(Error::Syntax(arm.clone())),
                })
                .map(|arm| arm.map(|(pattern, branch)| EnumMatchArm { pattern, branch }))
                .collect::<Result<Vec<_>, _>>()
                .and_then(|arms| Ok(Self::match_enum(Self::from_sexpr(val)?, arms))),

            List(Ref([Symbol(Ref("lambda")), List(Ref(vars)), body])) => parse_symbol_list(vars)
                .and_then(|vs| Self::from_sexpr(body).map(|b| Expr::lambda(vs, b))),

            List(Ref([Symbol(Ref("define")), List(defs), body])) => defs
                .iter()
                .map(Def::from_sexpr)
                .collect::<Result<Vec<_>, _>>()
                .and_then(|defs| Ok(Expr::defs(defs, Self::from_sexpr(body)?))),

            List(Ref([Symbol(Ref("begin")), seq @ ..])) => seq
                .iter()
                .map(Self::from_sexpr)
                .collect::<Result<Vec<_>, _>>()
                .map(Self::sequence),

            List(Ref([Symbol(Ref("+")), a, b])) => {
                Ok(Self::add(Self::from_sexpr(a)?, Self::from_sexpr(b)?))
            }

            List(Ref([Symbol(Ref("read"))])) => Ok(Self::Read()),

            List(Ref([Symbol(Ref("show")), x])) => Ok(Self::show(Self::from_sexpr(x)?)),

            List(Ref([f, a @ ..])) => Ok(Expr::apply(
                Self::from_sexpr(f)?,
                a.iter()
                    .map(Self::from_sexpr)
                    .collect::<Result<Vec<_>, _>>()?,
            )),

            _ => Err(Error::Syntax(s.clone())),
        }
    }

    pub fn to_sexpr(&self) -> S {
        match self {
            Expr::Int(x) => S::Int(*x),

            Expr::Real(x) => S::Float(*x),

            Expr::String(x) => S::String(x.into()),

            Expr::Ref(x) => S::Symbol(x.into()),

            Expr::Record(rec) => S::list(
                once(S::symbol("record"))
                    .chain(rec.iter().map(Self::to_sexpr))
                    .collect(),
            ),

            Expr::Select(sel) => S::list(vec![
                S::symbol("select"),
                S::Int(sel.0 as i64),
                sel.1.to_sexpr(),
            ]),

            Expr::MatchEnum(mat) => S::list(
                vec![S::symbol("match-enum"), mat.0.to_sexpr()]
                    .into_iter()
                    .chain(mat.1.iter().map(|arm| {
                        S::list(vec![
                            arm.pattern.to_sexpr(),
                            S::symbol("=>"),
                            arm.branch.to_sexpr(),
                        ])
                    }))
                    .collect(),
            ),

            Expr::Lambda(lam) => S::list(vec![
                S::symbol("lambda"),
                S::list(
                    lam.params
                        .iter()
                        .map(|p| S::Symbol(p.clone().into()))
                        .collect(),
                ),
                lam.body.to_sexpr(),
            ]),

            Expr::Defs(defs) => S::list(vec![
                S::symbol("define"),
                S::list(defs.0.iter().map(|d| d.to_sexpr()).collect()),
                defs.1.to_sexpr(),
            ]),

            Expr::Sequence(_) => {
                let mut tail = self;
                let mut seq = vec![S::symbol("begin")];
                while let Expr::Sequence(xs) = tail {
                    seq.push(xs.0.to_sexpr());
                    tail = &xs.1;
                }
                seq.push(tail.to_sexpr());
                S::list(seq)
            }

            Expr::Add(rands) => {
                S::list(vec![S::symbol("+"), rands.0.to_sexpr(), rands.1.to_sexpr()])
            }

            Expr::Read() => S::list(vec![S::symbol("read")]),

            Expr::Show(rand) => S::list(vec![S::symbol("show"), rand.to_sexpr()]),

            Expr::Apply(app) => S::list(once(&app.0).chain(&app.1).map(Self::to_sexpr).collect()),

            _ => todo!("{:?}", self),
        }
    }
}

impl Def {
    fn to_sexpr(&self) -> S {
        match self {
            Def::Enum(EnumDef {
                tname,
                tvars,
                variants,
            }) => cons(
                S::symbol("enum"),
                cons(
                    S::symbol_list(cons(tname, tvars)),
                    variants.iter().map(|va| match va {
                        EnumVariant { name: c, tyxs: xs } if xs.is_empty() => {
                            S::Symbol(c.clone().into())
                        }
                        EnumVariant { name: c, tyxs: xs } => {
                            cons(S::Symbol(c.clone().into()), xs.iter().map(TyExpr::to_sexpr))
                                .collect()
                        }
                    }),
                ),
            )
            .collect(),

            Def::Func(fndecl, body) => fndecl.to_sexpr(Some(body)),

            Def::Interface(IntDef {
                iname,
                tvars,
                funcs,
            }) => cons(
                S::symbol("interface"),
                cons(
                    S::symbol_list(cons(iname, tvars)),
                    funcs.iter().map(|decl| decl.to_sexpr(None)),
                ),
            )
            .collect(),

            Def::Impl(_) => todo!(),

            Def::InferredFunc(_) => unimplemented!(),
        }
    }

    fn from_sexpr(s: &S) -> Result<Self, Error> {
        match s {
            S::List(Ref(
                [S::Symbol(Ref("enum")), S::List(Ref([S::Symbol(Ref(tname)), tvars @ ..])), variants @ ..],
            )) => {
                let tname = tname.to_string();
                let tvars = parse_symbol_list(tvars)?;
                let variants = variants
                    .iter()
                    .map(|v| match v {
                        S::Symbol(name) => Ok(EnumVariant::constant(name.to_string())),
                        S::List(Ref([S::Symbol(name), tyxs @ ..])) => Ok(EnumVariant::constructor(
                            name.to_string(),
                            tyxs.iter()
                                .map(TyExpr::from_sexpr)
                                .collect::<Result<Vec<_>, _>>()?,
                        )),
                        _ => Err(Error::Syntax(v.clone())),
                    })
                    .collect::<Result<_, _>>()?;
                Ok(Def::Enum(EnumDef {
                    tname,
                    tvars,
                    variants: Rc::new(variants),
                }))
            }

            S::List(Ref([S::Symbol(Ref("func")), ..])) => {
                FnDecl::from_sexpr_with_body(s).map(|(decl, body)| Def::Func(decl, body))
            }

            S::List(Ref(
                [S::Symbol(Ref("interface")), S::List(Ref([S::Symbol(Ref(iname)), tvars @ ..])), funcs @ ..],
            )) => {
                let iname = iname.to_string();
                let tvars = parse_symbol_list(tvars)?;
                let funcs = funcs
                    .iter()
                    .map(FnDecl::from_sexpr_without_body)
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Def::Interface(IntDef {
                    iname,
                    tvars,
                    funcs: Rc::new(funcs),
                }))
            }

            _ => Err(Error::Syntax(s.clone())),
        }
    }
}

impl FnDecl {
    fn to_sexpr(&self, body: Option<&Expr>) -> S {
        S::list(
            vec![
                S::symbol("func"),
                S::list(
                    self.tvars
                        .iter()
                        .map(|v| S::Symbol(v.clone().into()))
                        .collect(),
                ),
                S::list(
                    once(S::Symbol(self.fname.clone().into()))
                        .chain(self.params.iter().zip(self.ptypes.iter()).map(|(p, t)| {
                            S::list(vec![
                                S::Symbol(p.clone().into()),
                                S::symbol(":"),
                                t.to_sexpr(),
                            ])
                        }))
                        .chain(vec![S::symbol("->"), self.rtype.to_sexpr()])
                        .collect(),
                ),
            ]
            .into_iter()
            .chain(body.into_iter().map(Expr::to_sexpr))
            .collect(),
        )
    }

    fn from_sexpr_with_body(s: &S) -> Result<(Self, Expr), Error> {
        match s {
            S::List(Ref([_, _, _, body])) => Ok((Self::from_sexpr(s)?, Expr::from_sexpr(body)?)),
            _ => Err(Error::Syntax(s.clone())),
        }
    }

    fn from_sexpr_without_body(s: &S) -> Result<Self, Error> {
        match s {
            S::List(Ref([_, _, _])) => Self::from_sexpr(s),
            _ => Err(Error::Syntax(s.clone())),
        }
    }

    fn from_sexpr(s: &S) -> Result<Self, Error> {
        match s {
            S::List(Ref(
                [S::Symbol(Ref("func")), S::List(Ref(tvars)), S::List(Ref([S::Symbol(Ref(fname)), sig @ ..])), ..],
            )) => {
                let mut params = vec![];
                let mut ptypes = vec![];
                let mut sig = sig;
                let rtype = loop {
                    match sig {
                        [S::Symbol(Ref("->")), rtype] => break TyExpr::from_sexpr(rtype)?,
                        [S::List(Ref([S::Symbol(Ref(var)), S::Symbol(Ref(":")), ptype])), rest @ ..] =>
                        {
                            params.push(var.to_string());
                            ptypes.push(TyExpr::from_sexpr(ptype)?);
                            sig = rest;
                        }
                        _ => return Err(Error::Syntax(s.clone())),
                    }
                };
                let fname = fname.to_string();
                let tvars = parse_symbol_list(tvars)?;
                Ok(FnDecl {
                    fname,
                    tvars,
                    params,
                    ptypes,
                    rtype,
                })
            }
            _ => Err(Error::Syntax(s.clone())),
        }
    }
}

fn parse_symbol_list(xs: &[S]) -> Result<Vec<String>, Error> {
    xs.iter()
        .map(|x| {
            if let S::Symbol(s) = x {
                Ok(s.to_string())
            } else {
                Err(Error::Syntax(x.clone()))
            }
        })
        .collect::<Result<Vec<_>, _>>()
}

impl TyExpr {
    fn to_sexpr(&self) -> S {
        match self {
            TyExpr::Unit => S::list(vec![]),
            TyExpr::Int => S::symbol("Int"),
            TyExpr::Real => S::symbol("Real"),
            TyExpr::String => S::symbol("String"),
            TyExpr::Named(v) => S::Symbol(v.clone().into()),
            TyExpr::Fn(f) => S::list(
                f.0.iter()
                    .map(Self::to_sexpr)
                    .chain(vec![S::symbol("->"), f.1.to_sexpr()])
                    .collect(),
            ),
            TyExpr::Record(fts) => S::list(fts.iter().map(|t| t.to_sexpr()).collect()),
            TyExpr::Construct(txs) => S::list(
                once(S::Symbol(txs.0.clone().into()))
                    .chain(txs.1.iter().map(Self::to_sexpr))
                    .collect(),
            ),
        }
    }

    fn from_sexpr(s: &S) -> Result<Self, Error> {
        match s {
            S::List(Ref([])) => Ok(TyExpr::Unit),
            S::Symbol(Ref("Int")) => Ok(TyExpr::Int),
            S::Symbol(Ref("Real")) => Ok(TyExpr::Real),
            S::Symbol(Ref("String")) => Ok(TyExpr::String),
            S::Symbol(Ref(v)) => Ok(TyExpr::Named(v.to_string())),
            S::List(Ref([f @ .., S::Symbol(Ref("->")), a])) => Ok(TyExpr::func(
                f.iter()
                    .map(|s| Self::from_sexpr(s))
                    .collect::<Result<Vec<_>, _>>()?,
                Self::from_sexpr(a)?,
            )),
            S::List(Ref([S::Symbol(Ref("Record")), fts @ ..])) => fts
                .iter()
                .map(|s| Self::from_sexpr(s))
                .collect::<Result<Vec<_>, _>>()
                .map(Rc::new)
                .map(Self::Record),

            S::List(Ref([S::Symbol(Ref(t0)), txs @ ..])) => txs
                .iter()
                .map(Self::from_sexpr)
                .collect::<Result<Vec<_>, _>>()
                .map(|targs| (t0.to_string(), targs))
                .map(Rc::new)
                .map(TyExpr::Construct),
            _ => Err(Error::Syntax(s.clone())),
        }
    }
}

impl EnumVariantPattern {
    pub fn to_sexpr(&self) -> S {
        match self {
            EnumVariantPattern { name, vars } if vars.is_empty() => S::Symbol(name.clone().into()),
            EnumVariantPattern { name, vars } => S::list(
                once(S::Symbol(name.clone().into()))
                    .chain(vars.iter().map(Ref::from).map(S::Symbol))
                    .collect(),
            ),
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

fn cons<T>(x: T, xs: impl IntoIterator<Item = T>) -> impl Iterator<Item = T> {
    once(x).chain(xs.into_iter())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_literals() {
        let repr = "123";
        let expr = Expr::int(123);
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));

        let repr = "12.34";
        let expr = Expr::real(12.34);
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));

        let repr = "\"hello, world!\"";
        let expr = Expr::string("hello, world!");
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn test_variable_ref() {
        let repr = "foo";
        let expr = Expr::var("foo");
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn test_application() {
        let repr = "((foo bar) (f 4 2))";
        let expr = Expr::apply(Expr::apply("foo", ["bar"]), [Expr::apply("f", (4, 2, ()))]);
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn test_record() {
        let repr = "(record 1 x 2)";
        let expr = Expr::record((1, "x", 2, ()));
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn test_select() {
        let repr = "(select 1 r)";
        let expr = Expr::select(1, "r");
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn test_match_enum() {
        let repr = "(match-enum foo ((Bar x) => x) (Baz => 42))";
        let expr = Expr::match_enum(
            "foo",
            [
                (
                    EnumVariantPattern::constructor("Bar", ["x"]),
                    Expr::var("x"),
                ),
                (EnumVariantPattern::constant("Baz"), Expr::int(42)),
            ],
        );
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn test_lambda() {
        let repr = "(lambda (x) 42)";
        let expr = Expr::lambda(["x"], 42);
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));

        let repr = "(lambda (x y z) 42)";
        let expr = Expr::lambda(["x", "y", "z"], 42);
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn test_defs() {
        let repr = "(define ((enum (Option T) None (Some T Int)) (func (T) (foo (x : T) -> Int) 42) (func (T) (bar (x : T) (y : T) -> Int) 123)) 0)";
        let expr = Expr::defs(
            vec![
                Def::enum_(
                    "Option",
                    ["T"],
                    ("None", ("Some", ("T", TyExpr::Int, ())), ()),
                ),
                Def::func("foo", ["T"], ["T"], TyExpr::Int, ["x"], 42),
                Def::func("bar", ["T"], ["T", "T"], TyExpr::Int, ["x", "y"], 123),
            ],
            0,
        );
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn test_primitives() {
        let repr = "(+ x y)";
        let expr = Expr::add("x", "y");
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));

        let repr = "(read)";
        let expr = Expr::Read();
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));

        let repr = "(show this)";
        let expr = Expr::show("this");
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn sequence() {
        let repr = "(begin 1 2 3)";
        let expr = Expr::sequence(vec![1.into(), 2.into(), 3.into()]);
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }

    #[test]
    fn define_interface() {
        let repr = "(define ((interface (Foo T) (func () (bar (x : T) -> T)))) 0)";
        let expr = Expr::defs(
            vec![Def::interface(
                "Foo",
                ["T"],
                vec![FnDecl::new("bar", [] as [&str; 0], ["T"], "T", ["x"])],
            )],
            0,
        );
        assert_eq!(expr.to_string(), repr);
        assert_eq!(Expr::from_str(repr), Ok(expr));
    }
}
