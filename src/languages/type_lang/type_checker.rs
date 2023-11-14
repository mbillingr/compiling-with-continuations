use crate::languages::type_lang::ast::{Def, EnumVariant, Expr, TyExpr, Type};
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
    fn check_program(expr: &Expr) -> Result<Expr, String> {
        let mut checker = Checker::new();
        let expr_ = checker.check_expr(expr, &Type::Int, &HashMap::new(), &HashMap::new())?;
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

            Expr::Ref(var) => match env.get(var) {
                None => Err(format!("unbound {var}")),
                Some(Type::Generic(g)) => Ok((g.instantiate(self, tenv), Expr::var(var))),
                Some(t) => Ok((t.clone(), Expr::var(var))),
            }
            .map(|(t, x)| Rc::new((t, x)))
            .map(Expr::Annotation),

            Expr::Cons(cons) => {
                let (ety, variant, args) = &**cons;
                let t = tenv
                    .get(ety)
                    .ok_or_else(|| format!("Unknown type: {ety}"))?;
                match t {
                    Type::Enum(enum_) => {
                        let (name, variants) = &**enum_;
                        let var = variants
                            .get(variant)
                            .ok_or_else(|| format!("Unknown variant: {name} {variant}"))?;
                        if args.len() != var.len() {
                            return Err(format!("Wrong number of argumnts: {name} {variant}"));
                        }
                        for (v, a) in var.iter().zip(args) {
                            self.check_expr(a, v, env, tenv)?;
                        }
                        let targs: Result<Vec<_>, _> = args
                            .iter()
                            .zip(var)
                            .map(|(a, v)| self.check_expr(a, v, env, tenv))
                            .collect();
                        Ok(Expr::annotate(t.clone(), Expr::cons(ety, variant, targs?)))
                    }
                    _ => Err(format!("Not an enum: {ety}")),
                }
            }

            Expr::Decons(de) => {
                let (value, variant, vars, matches, mismatch) = &**de;

                let value_ = self.infer(value, env, tenv)?;
                let (name, variants) = &**match value_.get_type() {
                    Type::Enum(enum_) => enum_,
                    _ => return Err(format!("Not an enum: {value_:?}")),
                };

                let constructor = variants
                    .get(variant)
                    .ok_or_else(|| format!("Unknown variant: {name} {variant}"))?;
                if vars.len() != constructor.len() {
                    return Err(format!("Wrong number of bindings: {name} {variant}"));
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

                let mut defs_ = vec![];

                for def in defs {
                    match def {
                        Def::Func(def) => {
                            let mut tenv_ = tenv.clone();
                            tenv_.extend(
                                def.tvars
                                    .iter()
                                    .map(|tv| (tv.to_string(), Type::Opaque(tv.to_string()))),
                            );

                            let rt = teval(&def.rtype, &tenv_);
                            let pt = teval(&def.ptype, &tenv_);
                            let ft = Type::Fn(Rc::new((pt.clone(), rt.clone())));

                            let mut env_ = env.clone();
                            env_.insert(def.fname.clone(), ft);
                            env_.insert(def.param.clone(), pt);

                            let signature = Type::Generic(Rc::new(GenericType::GenericFn {
                                tvars: def.tvars.clone(),
                                ptype: def.ptype.clone(),
                                rtype: def.rtype.clone(),
                            }));

                            let body_ = self.check_expr(&def.body, &rt, &env_, &tenv_)?;
                            defs_.push(Def::inferred_func(
                                signature.clone(),
                                &def.fname,
                                &def.param,
                                body_,
                            ));

                            def_env.insert(def.fname.clone(), signature);
                        }
                        Def::Enum(def) => {
                            let mut variants = HashMap::new();
                            for v in &def.variants {
                                match v {
                                    EnumVariant::Constant(vn) => {
                                        variants.insert(vn.clone(), vec![]);
                                    }
                                    EnumVariant::Constructor(vn, tx) => {
                                        variants.insert(vn.clone(), vec![teval(tx, tenv)]);
                                    }
                                }
                            }

                            def_tenv.insert(
                                def.tname.clone(),
                                Type::Enum(Rc::new((def.tname.clone(), variants))),
                            );
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
            Expr::Ref(x) => Ok(Expr::Ref(x.clone())),

            Expr::Apply(app) => Ok(Expr::apply(
                self.resolve_expr(&app.0)?,
                self.resolve_expr(&app.1)?,
            )),

            Expr::Cons(cons) => Ok(Expr::cons(
                &cons.0,
                &cons.1,
                cons.2
                    .iter()
                    .map(|x| self.resolve_expr(x))
                    .collect::<Result<Vec<_>, _>>()?,
            )),

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
                if Rc::ptr_eq(&a, &b) {
                    Ok(())
                } else {
                    Err(format!("different enums"))
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
            Type::Unit | Type::Int | Type::Real | Type::Opaque(_) => Ok(t.clone()),

            Type::Var(_) => match self.resolve(t) {
                t_ @ Type::Var(_) => Err(format!("{t:?} resolves to {t_:?}")),
                t_ => Ok(t_),
            },

            Type::Fn(fun) => Ok(Type::func(
                self.resolve_fully(&fun.0)?,
                self.resolve_fully(&fun.1)?,
            )),

            Type::Generic(_) => Ok(t.clone()),

            Type::Enum(enu) => enu
                .1
                .iter()
                .map(|(v, args)| {
                    args.iter()
                        .map(|a| self.resolve_fully(a))
                        .collect::<Result<Vec<_>, _>>()
                        .map(|r| (v.clone(), r))
                })
                .collect::<Result<HashMap<_, _>, _>>()
                .map(|vars| (enu.0.to_string(), vars))
                .map(Rc::new)
                .map(Type::Enum),
        }
    }

    fn fresh(&mut self) -> Type {
        let nr = self.substitutions.len();
        self.substitutions.push(None);
        Type::Var(nr)
    }
}

fn teval(tx: &TyExpr, tenv: &HashMap<String, Type>) -> Type {
    match tx {
        TyExpr::Int => Type::Int,
        TyExpr::Real => Type::Real,
        TyExpr::Var(v) => tenv
            .get(v)
            .cloned()
            .unwrap_or_else(|| panic!("Unknown {v}")),
        TyExpr::Fn(sig) => Type::Fn(Rc::new((teval(&sig.0, tenv), teval(&sig.1, tenv)))),
    }
}

#[derive(Debug, PartialEq)]
pub enum GenericType {
    GenericFn {
        tvars: Vec<String>,
        ptype: TyExpr,
        rtype: TyExpr,
    },
}

impl GenericType {
    fn instantiate(&self, ctx: &mut Checker, tenv: &HashMap<String, Type>) -> Type {
        match self {
            GenericType::GenericFn {
                tvars,
                ptype,
                rtype,
            } => {
                let mut tenv = tenv.clone();
                tenv.extend(tvars.iter().map(|tv| (tv.to_string(), ctx.fresh())));

                let rt = teval(rtype, &tenv);
                let pt = teval(ptype, &tenv);
                Type::Fn(Rc::new((pt.clone(), rt.clone())))
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
                substitutions: vec![]
            }
            .resolve(&Type::Real),
            Type::Real
        );

        assert_eq!(
            Checker {
                substitutions: vec![Some(Type::Int)]
            }
            .resolve(&Type::Var(0)),
            Type::Int
        );

        assert_eq!(
            Checker {
                substitutions: vec![Some(Type::Var(1)), Some(Type::Int)]
            }
            .resolve(&Type::Var(0)),
            Type::Int
        );
    }

    #[test]
    fn check_primitives() {
        assert_eq!(Checker::check_program(&Expr::int(42)), Ok(Expr::int(42)));
        assert!(Checker::check_program(&Expr::real(4.2)).is_err());
        assert_eq!(
            Checker::new().check_expr(
                &Expr::real(4.2),
                &Type::Real,
                &HashMap::new(),
                &HashMap::new()
            ),
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
        assert!(Checker::check_program(&x).is_ok());

        let x = Expr::apply(Expr::lambda("x", "x"), Expr::Real(0.0));
        assert!(Checker::check_program(&x).is_err());
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
    fn fail_generic_use() {
        let x = Expr::defs(
            [Def::func("fn", vec!["T"], "T", "T", "x", "x")],
            Expr::apply("fn", 1.2),
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
        assert!(Checker::check_program(&x).is_ok());
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
    fn check_enum() {
        let x = Expr::defs(
            [Def::enum_("Foo", ("A", ("B", TyExpr::Int), ()))],
            Expr::defs(
                [Def::func(
                    "f",
                    vec![] as Vec<&str>,
                    "Foo",
                    TyExpr::Int,
                    "x",
                    Expr::Int(0),
                )],
                Expr::apply("f", Expr::cons("Foo", "B", [1])),
            ),
        );
        assert!(Checker::check_program(&x).is_ok());
    }

    #[test]
    fn check_enum_deconstruction() {
        let x = Expr::defs(
            [Def::enum_("Foo", ("A", ("B", TyExpr::Int), ()))],
            Expr::decons(Expr::cons("Foo", "B", [1]), "B", ["x"], "x", 0),
        );
        assert!(Checker::check_program(&x).is_ok());
    }

    #[test]
    fn check_add() {
        assert!(Checker::new()
            .check_expr(
                &Expr::add(1, 2),
                &Type::Int,
                &HashMap::new(),
                &HashMap::new()
            )
            .is_ok());

        assert!(Checker::new()
            .check_expr(
                &Expr::add(1.0, 2.0),
                &Type::Real,
                &HashMap::new(),
                &HashMap::new()
            )
            .is_ok());
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
