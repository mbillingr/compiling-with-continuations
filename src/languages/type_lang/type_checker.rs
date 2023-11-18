use crate::languages::type_lang::ast::{Def, EnumDef, EnumType, EnumVariant, Expr, TyExpr, Type};
use std::collections::HashMap;
use std::fmt::Debug;
use std::rc::Rc;

pub struct Checker {
    substitutions: Vec<Option<Type>>,
}

impl Checker {
    fn new() -> Self {
        Checker {
            substitutions: vec![],
        }
    }
    pub fn check_program(expr: &Expr) -> Result<Expr, String> {
        let mut checker = Checker::new();
        let expr_ = checker.infer(expr, &HashMap::new(), &HashMap::new())?;

        checker.resolve_expr(&expr_)
    }

    fn check_expr(
        &mut self,
        expr: &Expr,
        ty: &Type,
        env: &HashMap<String, Type>,  // types of variables
        tenv: &HashMap<String, Type>, // defined types
    ) -> Result<Expr, String> {
        match expr {
            _ => {
                let typed = self.infer(expr, env, tenv)?;
                self.unify(typed.get_type(), ty)?;
                Ok(typed)
            }
        }
    }

    fn infer(
        &mut self,
        expr: &Expr,
        env: &HashMap<String, Type>,
        tenv: &HashMap<String, Type>,
    ) -> Result<Expr, String> {
        match expr {
            Expr::Int(x) => Ok(Expr::Int(*x)),
            Expr::Real(x) => Ok(Expr::Real(*x)),
            Expr::String(x) => Ok(Expr::String(x.clone())),

            Expr::Ref(var) => match env.get(var) {
                None => Err(format!("unbound {var}")),
                Some(Type::Generic(g)) => Ok((g.instantiate_fresh(self, tenv), Expr::var(var))),
                Some(t) => Ok((t.clone(), Expr::var(var))),
            }
            .map(|(t, x)| Rc::new((t, x)))
            .map(Expr::Annotation),

            Expr::Record(fields) => {
                let fields_: Vec<_> = fields
                    .iter()
                    .map(|f| self.infer(f, env, tenv))
                    .collect::<Result<_, _>>()?;
                let field_types: Vec<_> = fields_.iter().map(Expr::get_type).cloned().collect();
                Ok(Expr::annotate(
                    Type::Record(field_types.into()),
                    Expr::record(fields_),
                ))
            }

            Expr::Cons(cons) => {
                let (ety, variant, args) = &**cons;
                let t = self.lookup_concrete_type(ety, tenv)?;
                match &t {
                    Type::Enum(enum_) => {
                        let var = enum_.variants.get(variant).ok_or_else(|| {
                            format!("Unknown variant: {} {variant}", enum_.template.get_name())
                        })?;
                        if args.len() != var.len() {
                            return Err(format!(
                                "Wrong number of arguments: {} {variant}",
                                enum_.template.get_name()
                            ));
                        }
                        for (v, a) in var.iter().zip(args) {
                            self.check_expr(a, v, env, tenv)?;
                        }
                        let targs: Result<Vec<_>, _> = args
                            .iter()
                            .zip(var)
                            .map(|(a, v)| self.check_expr(a, v, env, tenv))
                            .collect();
                        Ok(Expr::annotate(t, Expr::cons(ety, variant, targs?)))
                    }
                    _ => Err(format!("Not an enum - {ety} is a {t:?}")),
                }
            }

            Expr::Cons2(cons) => {
                let enum_t = self.teval(&cons.0, tenv);
                let variant = &cons.1;
                match enum_t {
                    Type::Enum(enum_) => {
                        let var = enum_.variants.get(variant).ok_or_else(|| {
                            format!("Unknown variant: {} {variant}", enum_.template.get_name())
                        })?;

                        let t = match var.as_slice() {
                            [] => Type::Enum(enum_),
                            [x] => Type::func(x.clone(), Type::Enum(enum_)),
                            _ => panic!("Multiple enum variant values are not supported"),
                        };
                        Ok(Expr::annotate(t, Expr::cons2(cons.0.clone(), &cons.1)))
                    }
                    t => panic!("Not an enum - {:?} is a {t:?}", cons.0),
                }
            }

            Expr::Decons(de) => {
                let (value, variant, vars, matches, mismatch) = &**de;

                let value_ = self.infer(value, env, tenv)?;
                let enum_ = &**match value_.get_type() {
                    Type::Enum(enum_) => enum_,
                    _ => return Err(format!("Not an enum: {value_:?}")),
                };

                let constructor = enum_.variants.get(variant).ok_or_else(|| {
                    format!("Unknown variant: {} {variant}", enum_.template.get_name())
                })?;
                if vars.len() != constructor.len() {
                    return Err(format!(
                        "Wrong number of bindings: {} {variant}",
                        enum_.template.get_name()
                    ));
                }

                let mut match_env = env.clone();
                match_env.extend(vars.iter().cloned().zip(constructor.iter().cloned()));

                let tma = self.infer(matches, &match_env, tenv)?;
                let tmi = self.infer(mismatch, env, tenv)?;

                // not sure if it's ok like this. maybe need to return a fresh typevar that's unified with both.
                let (t1, t2) = (tma.get_type(), tmi.get_type());
                self.unify(&t1, &t2)?;
                let t = t1.clone();

                Ok(Expr::annotate(
                    t,
                    Expr::decons(value_, variant, vars.to_vec(), tma, tmi),
                ))
            }

            Expr::Apply(app) => {
                let r_ = self.fresh();
                let f_ = self.infer(&app.0, env, tenv)?;
                let a_ = self.infer(&app.1, env, tenv)?;
                let ty = Type::Fn(Rc::new((a_.get_type().clone(), r_.clone())));
                self.unify(f_.get_type(), &ty)?;
                Ok(Expr::annotate(r_, Expr::apply(f_, a_)))
            }

            Expr::Lambda(lam) => {
                let at = self.fresh();
                let rt = self.fresh();

                let mut env_ = env.clone();
                env_.insert(lam.param.clone(), at.clone());
                let body_ = self.check_expr(&lam.body, &rt, &env_, &tenv)?;

                Ok(Expr::annotate(
                    Type::Fn(Rc::new((at, rt))),
                    Expr::lambda(&lam.param, body_),
                ))
            }

            Expr::Defs(defs) => {
                let (defs, body) = &**defs;
                let mut def_env = env.clone();
                let mut def_tenv = tenv.clone();

                for def in defs {
                    match def {
                        Def::Func(def) => {
                            let signature = Type::Generic(Rc::new(GenericType::GenericFn {
                                tvars: def.tvars.clone(),
                                ptype: def.ptype.clone(),
                                rtype: def.rtype.clone(),
                            }));
                            def_env.insert(def.fname.clone(), signature);
                        }
                        Def::Enum(def) => {
                            let type_constructor =
                                Type::Generic(Rc::new(GenericType::GenericEnum(def.clone())));

                            def_tenv.insert(def.tname.clone(), type_constructor);
                        }
                        Def::InferredFunc(_) => unreachable!(),
                    }
                }

                let mut defs_ = vec![];

                for def in defs {
                    match def {
                        Def::Func(def) => {
                            let mut tenv_ = def_tenv.clone();
                            tenv_.extend(
                                def.tvars
                                    .iter()
                                    .map(|tv| (tv.to_string(), Type::Opaque(tv.to_string()))),
                            );

                            let rt = self.teval(&def.rtype, &tenv_);
                            let pt = self.teval(&def.ptype, &tenv_);
                            let ft = Type::Fn(Rc::new((pt.clone(), rt.clone())));

                            let mut env_ = env.clone();
                            env_.insert(def.fname.clone(), ft);
                            env_.insert(def.param.clone(), pt);

                            let body_ = self.check_expr(&def.body, &rt, &env_, &tenv_)?;

                            let signature = def_env[&def.fname].clone();

                            defs_
                                .push(Def::inferred_func(signature, &def.fname, &def.param, body_));
                        }
                        Def::Enum(def) => {
                            let type_constructor =
                                Type::Generic(Rc::new(GenericType::GenericEnum(def.clone())));

                            def_tenv.insert(def.tname.clone(), type_constructor);
                        }
                        Def::InferredFunc(_) => unreachable!(),
                    }
                }

                let body_ = self.infer(body, &def_env, &def_tenv)?;
                Ok(Expr::defs(defs_, body_))
            }

            Expr::Add(ops) => {
                let (a, b) = &**ops;
                let a_ = self.infer(a, env, tenv)?;
                let b_ = self.infer(b, env, tenv)?;
                self.unify(a_.get_type(), b_.get_type())?;
                Ok(Expr::annotate(a_.get_type().clone(), Expr::add(a_, b_)))
            }

            Expr::Read() => Ok(Expr::annotate(self.fresh(), Expr::Read())),

            Expr::Show(arg) => self.infer(arg, env, tenv).map(Expr::show),

            Expr::Annotation(ann) => {
                let (ty, ex) = &**ann;
                let ex_ = self.check_expr(ex, ty, env, tenv)?;
                Ok(Expr::annotate(ty.clone(), ex_))
            }
        }
    }

    /// resolve remaining type variables in the annotations
    fn resolve_expr(&self, expr: &Expr) -> Result<Expr, String> {
        match expr {
            Expr::Int(x) => Ok(Expr::Int(*x)),
            Expr::Real(x) => Ok(Expr::Real(*x)),
            Expr::String(x) => Ok(Expr::String(x.clone())),
            Expr::Ref(x) => Ok(Expr::Ref(x.clone())),

            Expr::Apply(app) => Ok(Expr::apply(
                self.resolve_expr(&app.0)?,
                self.resolve_expr(&app.1)?,
            )),

            Expr::Record(fields) => fields
                .iter()
                .map(|f| self.resolve_expr(f))
                .collect::<Result<Vec<_>, _>>()
                .map(Expr::record),

            Expr::Cons(cons) => Ok(Expr::cons(
                &cons.0,
                &cons.1,
                cons.2
                    .iter()
                    .map(|x| self.resolve_expr(x))
                    .collect::<Result<Vec<_>, _>>()?,
            )),

            Expr::Cons2(_) => Ok(expr.clone()),

            Expr::Decons(deco) => Ok(Expr::decons(
                self.resolve_expr(&deco.0)?,
                &deco.1,
                deco.2.to_vec(),
                self.resolve_expr(&deco.3)?,
                self.resolve_expr(&deco.4)?,
            )),

            Expr::Lambda(lam) => Ok(Expr::lambda(&lam.param, self.resolve_expr(&lam.body)?)),

            Expr::Defs(defs) => {
                let mut defs_ = vec![];

                for d in &defs.0 {
                    match d {
                        Def::Func(_) => unreachable!(),
                        Def::Enum(_) => unreachable!(),
                        Def::InferredFunc(fun) => defs_.push(Def::inferred_func(
                            self.resolve_fully(&fun.signature)?,
                            &fun.fname,
                            &fun.param,
                            self.resolve_expr(&fun.body)?,
                        )),
                    }
                }

                Ok(Expr::defs(defs_, self.resolve_expr(&defs.1)?))
            }

            Expr::Add(add) => Ok(Expr::add(
                self.resolve_expr(&add.0)?,
                self.resolve_expr(&add.1)?,
            )),

            Expr::Read() => Ok(Expr::Read()),

            Expr::Show(x) => Ok(Expr::show(self.resolve_expr(x)?)),

            Expr::Annotation(ann) => Ok(Expr::annotate(
                self.resolve_fully(&ann.0)?,
                self.resolve_expr(&ann.1)?,
            )),
        }
    }

    fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), String> {
        use crate::languages::type_lang::ast::Type::*;
        let t1_ = self.resolve(t1);
        let t2_ = self.resolve(t2);
        match (t1_, t2_) {
            (Generic(g), _) | (_, Generic(g)) => Err(format!("Uninstantiated generic: {g:?}")),

            (Var(v), t) | (t, Var(v)) => {
                assert!(self.substitutions[v].is_none());
                self.substitutions[v] = Some(t);
                Ok(())
            }

            (Fn(a), Fn(b)) => {
                let (pa, ra) = &*a;
                let (pb, rb) = &*b;
                self.unify(pa, pb)?;
                self.unify(ra, rb)
            }

            (Enum(a), Enum(b)) => {
                if Rc::ptr_eq(&a.template, &b.template) {
                    for (va, ats) in &a.variants {
                        let bts = &b.variants[va];
                        for (a_, b_) in ats.iter().zip(bts) {
                            self.unify(a_, b_)?;
                        }
                    }
                    Ok(())
                } else {
                    Err(format!("different enums {a:?} != {b:?}"))
                }
            }

            (Opaque(a), Opaque(b)) if a == b => Ok(()),
            (Unit, Unit) | (Int, Int) | (Real, Real) => Ok(()),

            (a, b) => Err(format!("{a:?} != {b:?}")),
        }
    }

    fn resolve<'a>(&'a self, mut t: &'a Type) -> Type {
        while let Type::Var(nr) = t {
            match &self.substitutions[*nr] {
                None => break,
                Some(t_) => t = t_,
            }
        }
        t.clone()
    }

    fn resolve_fully<'a>(&'a self, t: &'a Type) -> Result<Type, String> {
        match t {
            Type::Unit | Type::Int | Type::Real | Type::String | Type::Opaque(_) => Ok(t.clone()),

            Type::Var(_) => match self.resolve(t) {
                t_ @ Type::Var(_) => Err(format!("{t:?} resolves to {t_:?}")),
                t_ => self.resolve_fully(&t_),
            },

            Type::Fn(fun) => Ok(Type::func(
                self.resolve_fully(&fun.0)?,
                self.resolve_fully(&fun.1)?,
            )),

            Type::Generic(_) => Ok(t.clone()),

            Type::Record(fields) => fields
                .iter()
                .map(|f| self.resolve_fully(f))
                .collect::<Result<Vec<_>, _>>()
                .map(Rc::new)
                .map(Type::Record),

            Type::Enum(enu) => enu
                .variants
                .iter()
                .map(|(v, args)| {
                    args.iter()
                        .map(|a| self.resolve_fully(a))
                        .collect::<Result<Vec<_>, _>>()
                        .map(|r| (v.clone(), r))
                })
                .collect::<Result<HashMap<_, _>, _>>()
                .map(|variants| EnumType {
                    template: enu.template.clone(),
                    variants,
                })
                .map(Rc::new)
                .map(Type::Enum),
        }
    }

    fn fresh(&mut self) -> Type {
        let nr = self.substitutions.len();
        self.substitutions.push(None);
        Type::Var(nr)
    }

    fn lookup_concrete_type(
        &mut self,
        name: &str,
        tenv: &HashMap<String, Type>,
    ) -> Result<Type, String> {
        match tenv.get(name) {
            None => Err(format!("Unknown type: {name}")),
            Some(Type::Generic(tc)) => Ok(tc.instantiate_fresh(self, tenv)),
            Some(t) => Ok(t.clone()),
        }
    }

    fn teval(&mut self, tx: &TyExpr, tenv: &HashMap<String, Type>) -> Type {
        let t = match tx {
            TyExpr::Int => Type::Int,
            TyExpr::Real => Type::Real,
            TyExpr::String => Type::String,
            TyExpr::Named(v) => tenv
                .get(v)
                .cloned()
                .unwrap_or_else(|| panic!("Unknown {v}")),
            TyExpr::Fn(sig) => Type::Fn(Rc::new((
                self.teval(&sig.0, tenv),
                self.teval(&sig.1, tenv),
            ))),
            TyExpr::Construct(con) => match tenv.get(&con.0) {
                None => panic!("Unknown {}", con.0),
                Some(Type::Generic(tc)) => {
                    let args = con.1.iter().map(|t| self.teval(t, tenv)).collect();
                    tc.instantiate_with(args, self, tenv)
                }
                Some(t) => {
                    panic!("Not a type constructor: {t:?}")
                }
            },
        };
        match t {
            Type::Generic(g) => g.instantiate_fresh(self, tenv),
            _ => t,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum GenericType {
    GenericFn {
        tvars: Vec<String>,
        ptype: TyExpr,
        rtype: TyExpr,
    },

    GenericEnum(EnumDef),
}

impl GenericType {
    pub fn get_name(&self) -> &str {
        match self {
            GenericType::GenericFn { .. } => todo!(),
            GenericType::GenericEnum(ed) => &ed.tname,
        }
    }

    fn instantiate_fresh(self: &Rc<Self>, ctx: &mut Checker, tenv: &HashMap<String, Type>) -> Type {
        match &**self {
            GenericType::GenericFn { tvars, .. } => {
                let args = tvars.iter().map(|_| ctx.fresh()).collect();
                self.instantiate_with(args, ctx, tenv)
            }
            GenericType::GenericEnum(ed) => {
                let args = ed.tvars.iter().map(|_| ctx.fresh()).collect();
                self.instantiate_with(args, ctx, tenv)
            }
        }
    }

    fn instantiate_with(
        self: &Rc<Self>,
        args: Vec<Type>,
        ctx: &mut Checker,
        tenv: &HashMap<String, Type>,
    ) -> Type {
        match &**self {
            GenericType::GenericFn {
                tvars,
                ptype,
                rtype,
            } => {
                assert_eq!(tvars.len(), args.len());
                let mut tenv = tenv.clone();
                tenv.extend(tvars.iter().zip(args).map(|(tv, t)| (tv.to_string(), t)));

                let rt = ctx.teval(rtype, &tenv);
                let pt = ctx.teval(ptype, &tenv);
                Type::Fn(Rc::new((pt.clone(), rt.clone())))
            }
            GenericType::GenericEnum(ed) => {
                assert_eq!(ed.tvars.len(), args.len());
                let mut tenv = tenv.clone();
                tenv.extend(ed.tvars.iter().zip(args).map(|(tv, t)| (tv.to_string(), t)));

                let mut variants = HashMap::new();
                for v in &**ed.variants {
                    match v {
                        EnumVariant::Constant(vn) => {
                            variants.insert(vn.clone(), vec![]);
                        }
                        EnumVariant::Constructor(vn, tx) => {
                            variants.insert(vn.clone(), vec![ctx.teval(tx, &tenv)]);
                        }
                    }
                }

                Type::Enum(Rc::new(EnumType {
                    template: self.clone(),
                    variants,
                }))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolve_substitution() {
        assert_eq!(
            Checker {
                substitutions: vec![],
            }
            .resolve(&Type::Real),
            Type::Real
        );

        assert_eq!(
            Checker {
                substitutions: vec![Some(Type::Int)],
            }
            .resolve(&Type::Var(0)),
            Type::Int
        );

        assert_eq!(
            Checker {
                substitutions: vec![Some(Type::Var(1)), Some(Type::Int)],
            }
            .resolve(&Type::Var(0)),
            Type::Int
        );
    }

    #[test]
    fn check_primitives() {
        assert_eq!(Checker::check_program(&Expr::int(42)), Ok(Expr::int(42)));
        assert_eq!(
            Checker::check_program(&Expr::real(4.2)),
            Ok(Expr::real(4.2))
        );
    }

    #[test]
    fn check_annotations() {
        let x = Expr::defs(
            [Def::func(
                "fn",
                vec![] as Vec<&str>,
                TyExpr::Int,
                TyExpr::Int,
                "x",
                "x",
            )],
            Expr::apply("fn", 0),
        );

        let y = Expr::defs(
            [Def::inferred_func(
                Type::Generic(Rc::new(GenericType::GenericFn {
                    tvars: vec![],
                    ptype: TyExpr::Int,
                    rtype: TyExpr::Int,
                })),
                "fn",
                "x",
                Expr::annotate(Type::Int, "x"),
            )],
            Expr::annotate(
                Type::Int,
                Expr::apply(Expr::annotate(Type::func(Type::Int, Type::Int), "fn"), 0),
            ),
        );

        assert_eq!(Checker::check_program(&x), Ok(y));
    }

    #[test]
    fn check_lambdas() {
        let x = Expr::apply(Expr::lambda("x", "x"), Expr::int(0));
        let y = Expr::annotate(
            Type::Int,
            Expr::apply(
                Expr::annotate(
                    Type::func(Type::Int, Type::Int),
                    Expr::lambda("x", Expr::annotate(Type::Int, "x")),
                ),
                Expr::int(0),
            ),
        );
        assert_eq!(Checker::check_program(&x), Ok(y));

        let x = Expr::apply(Expr::lambda("x", "x"), Expr::Real(0.0));
        let y = Expr::annotate(
            Type::Real,
            Expr::apply(
                Expr::annotate(
                    Type::func(Type::Real, Type::Real),
                    Expr::lambda("x", Expr::annotate(Type::Real, "x")),
                ),
                Expr::real(0.0),
            ),
        );
        assert_eq!(Checker::check_program(&x), Ok(y));
    }

    #[test]
    fn check_generic() {
        let x = Expr::defs(
            [Def::func("fn", vec!["T"], "T", "T", "x", "x")],
            Expr::apply("fn", 0),
        );
        assert!(Checker::check_program(&x).is_ok());
    }

    #[test]
    fn fail_generic_def() {
        let x = Expr::defs(
            [Def::func("fn", vec!["T"], "T", "T", "x", 0)],
            Expr::apply("fn", 0),
        );
        assert!(Checker::check_program(&x).is_err());
    }

    #[test]
    fn check_generic_different_uses() {
        // (let ((id (lambda (x) x))) ((id id) 42))
        let x = Expr::defs(
            [Def::func("id", vec!["T"], "T", "T", "x", "x")],
            Expr::apply(Expr::apply("id", "id"), 42),
        );

        let y = Expr::defs(
            [Def::inferred_func(
                Type::Generic(Rc::new(GenericType::GenericFn {
                    tvars: vec!["T".into()],
                    ptype: TyExpr::Named("T".into()),
                    rtype: TyExpr::Named("T".into()),
                })),
                "id",
                "x",
                Expr::annotate(Type::Opaque("T".into()), "x"),
            )],
            Expr::annotate(
                Type::Int,
                Expr::apply(
                    Expr::annotate(
                        Type::func(Type::Int, Type::Int),
                        Expr::apply(
                            Expr::annotate(
                                Type::func(
                                    Type::func(Type::Int, Type::Int),
                                    Type::func(Type::Int, Type::Int),
                                ),
                                "id",
                            ),
                            Expr::annotate(Type::func(Type::Int, Type::Int), "id"),
                        ),
                    ),
                    42,
                ),
            ),
        );

        assert_eq!(Checker::check_program(&x), Ok(y));

        let x = Expr::defs(
            [
                Def::func("twice", vec!["T"], "T", "T", "x", Expr::add("x", "x")),
                Def::func("swallow", vec!["T"], "T", TyExpr::Int, "x", 0),
            ],
            Expr::apply(
                "swallow",
                Expr::record([Expr::apply("twice", 21), Expr::apply("twice", 1.23)]),
            ),
        );

        Checker::check_program(&x).unwrap();
    }

    #[test]
    fn check_outer_generic() {
        let x = Expr::defs(
            [Def::func(
                "f",
                vec!["T", "S"],
                "T",
                TyExpr::func("S", "T"),
                "x",
                Expr::lambda("y", "x"),
            )],
            Expr::apply(Expr::apply("f", 42), 1.2),
        );
        assert!(Checker::check_program(&x).is_ok());
    }

    #[test]
    fn check_record() {
        assert_eq!(
            Checker::new().infer(
                &Expr::record([] as [&str; 0]),
                &Default::default(),
                &Default::default()
            ),
            Ok(Expr::annotate(
                Type::Record(Rc::new(vec![])),
                Expr::record([] as [&str; 0])
            ))
        );

        assert_eq!(
            Checker::new().infer(
                &Expr::record([1, 2, 3]),
                &Default::default(),
                &Default::default()
            ),
            Ok(Expr::annotate(
                Type::Record(Rc::new(vec![Type::Int, Type::Int, Type::Int])),
                Expr::record([1, 2, 3])
            ))
        );
    }

    #[test]
    fn check_enum() {
        let x = Expr::defs(
            [Def::enum_(
                "Foo",
                [] as [&str; 0],
                ("A", ("B", TyExpr::Int), ()),
            )],
            Expr::defs(
                [Def::func(
                    "f",
                    vec![] as Vec<&str>,
                    ("Foo",),
                    TyExpr::Int,
                    "x",
                    Expr::Int(0),
                )],
                Expr::apply("f", Expr::cons("Foo", "B", [1])),
            ),
        );
        Checker::check_program(&x).unwrap();
    }

    #[test]
    fn check_generic_enum() {
        let x = Expr::defs(
            [
                Def::enum_("Foo", ["T"], ("A", ("B", "T"), ())),
                Def::func(
                    "f",
                    vec!["T"] as Vec<&str>,
                    ("Foo", "T"),
                    TyExpr::Int,
                    "x",
                    Expr::Int(0),
                ),
            ],
            Expr::apply("f", Expr::cons("Foo", "B", [1])),
        );

        let foo = Rc::new(GenericType::GenericEnum(EnumDef {
            tname: "Foo".to_string(),
            tvars: vec!["T".into()],
            variants: Rc::new(vec![
                EnumVariant::Constant("A".into()),
                EnumVariant::Constructor("B".into(), "T".into()),
            ]),
        }));

        let foo_int = Type::enum_(
            foo,
            [
                ("A".to_string(), vec![]),
                ("B".to_string(), vec![Type::Int]),
            ],
        );

        let y = Expr::defs(
            [Def::inferred_func(
                Type::Generic(Rc::new(GenericType::GenericFn {
                    tvars: vec!["T".into()],
                    ptype: ("Foo", "T").into(),
                    rtype: TyExpr::Int,
                })),
                "f",
                "x",
                Expr::Int(0),
            )],
            Expr::annotate(
                Type::Int,
                Expr::apply(
                    Expr::annotate(Type::func(foo_int.clone(), Type::Int), "f"),
                    Expr::annotate(foo_int, Expr::cons("Foo", "B", [1])),
                ),
            ),
        );

        assert_eq!(Checker::check_program(&x), Ok(y));
    }

    #[test]
    fn check_enum_deconstruction() {
        let x = Expr::defs(
            [Def::enum_::<&str>("Foo", [], ("A", ("B", TyExpr::Int), ()))],
            Expr::decons(Expr::cons("Foo", "B", [1]), "B", ["x"], "x", 0),
        );
        assert!(Checker::check_program(&x).is_ok());
    }

    #[test]
    fn check_add() {
        assert_eq!(
            Checker::new().infer(&Expr::add(1, 2), &HashMap::new(), &HashMap::new()),
            Ok(Expr::annotate(Type::Int, Expr::add(1, 2)))
        );

        assert_eq!(
            Checker::new().infer(&Expr::add(1.0, 2.0), &HashMap::new(), &HashMap::new()),
            Ok(Expr::annotate(Type::Real, Expr::add(1.0, 2.0)))
        );

        assert_eq!(
            Checker::new().infer(&Expr::add(1, 2.0), &HashMap::new(), &HashMap::new()),
            Err("Int != Real".into())
        );
    }

    #[test]
    fn check_generic_with_primitive() {
        let x = Expr::defs(
            [Def::func(
                "double",
                vec!["T"],
                "T",
                "T",
                "x",
                Expr::add("x", "x"),
            )],
            Expr::apply("double", 21),
        );
        assert!(Checker::check_program(&x).is_ok());
    }

    #[test]
    fn cant_infer() {
        let x = Expr::defs(
            [Def::func("foo", vec!["T"], "T", TyExpr::Int, "x", 0)],
            Expr::apply("foo", Expr::Read()),
        );
        assert_eq!(
            Checker::check_program(&x),
            Err("'1 resolves to '2".to_string())
        );
    }
}
