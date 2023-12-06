use crate::languages::type_lang::ast::{
    Def, EnumDef, EnumMatchArm, EnumType, EnumVariant, EnumVariantPattern, Expr, GenericInstance,
    TyExpr, Type,
};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
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
                self.unify(&typed.get_type(), ty)?;
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
        //println!("infer {expr:?}");
        match expr {
            Expr::Unit => Ok(Expr::Unit),
            Expr::Int(x) => Ok(Expr::Int(*x)),
            Expr::Real(x) => Ok(Expr::Real(*x)),
            Expr::String(x) => Ok(Expr::String(x.clone())),

            Expr::Ref(var) => match env.get(var) {
                None => Err(format!("unbound {var}")),
                Some(Type::Generic(g)) => Ok((g.instantiate_fresh(self), Expr::var(var))),
                Some(t) => Ok((t.clone(), Expr::var(var))),
            }
            .map(|(t, x)| Rc::new((t, x)))
            .map(Expr::Annotation),

            Expr::Record(fields) => Ok(if fields.is_empty() {
                Expr::Unit
            } else {
                let fields_: Vec<_> = fields
                    .iter()
                    .map(|f| self.infer(f, env, tenv))
                    .collect::<Result<_, _>>()?;
                let field_types: Vec<_> = fields_.iter().map(Expr::get_type).collect();
                Expr::annotate(Type::Record(field_types.into()), Expr::record(fields_))
            }),

            Expr::Select(sel) => {
                let r = self.infer(&sel.1, env, tenv)?;
                match r.get_type() {
                    Type::Record(field_types) => Ok(Expr::annotate(
                        field_types[sel.0].clone(),
                        Expr::select(sel.0, r),
                    )),
                    _ => Err(format!("expected record: {:?}", sel.1)),
                }
            }

            Expr::Cons(cons) => {
                let tx = &cons.0;
                let enum_t = self.teval(tx, tenv);
                let variant = &cons.1;

                match enum_t.check_enum(self) {
                    None => Err(format!("Not an enum - {:?} is a {enum_t:?}", cons.0)),
                    Some(enum_) => {
                        let var = enum_.variants.get(variant).ok_or_else(|| {
                            format!("Unknown variant: {} {variant}", enum_.template.get_name())
                        })?;

                        let t = match var.as_slice() {
                            [] => enum_t,
                            _ => Type::func(var.clone(), enum_t),
                        };
                        Ok(Expr::annotate(t, Expr::cons(cons.0.clone(), &cons.1)))
                    }
                }
            }

            Expr::MatchEnum(mat) => {
                let (val, arms) = &**mat;

                let val_ = self.infer(val, env, tenv)?;
                let enum_ = &*match self.resolve(&val_.get_type()).check_enum(self) {
                    None => return Err(format!("Not an enum - {val_:?}")),
                    Some(enum_) => enum_,
                };

                let ty = self.fresh();

                let mut arms_ = vec![];
                for arm in arms {
                    let constructor = enum_.variants.get(&arm.pattern.name).ok_or_else(|| {
                        format!(
                            "Unknown variant: {} {}",
                            enum_.template.get_name(),
                            arm.pattern.name
                        )
                    })?;

                    if constructor.len() != arm.pattern.vars.len() {
                        return Err(format!(
                            "Length of Variant pattern {} {} does not match constructor",
                            enum_.template.get_name(),
                            arm.pattern.name,
                        ));
                    }

                    let mut branch_env = env.clone();
                    for (var, t) in arm.pattern.vars.iter().zip(constructor) {
                        branch_env.insert(var.clone(), t.clone());
                    }

                    let branch_ = self.infer(&arm.branch, &branch_env, tenv)?;
                    self.unify(&ty, &branch_.get_type())?;
                    arms_.push(EnumMatchArm {
                        pattern: arm.pattern.clone(),
                        branch: branch_,
                    });
                }

                Ok(Expr::annotate(ty, Expr::match_enum(val_, arms_)))
            }

            Expr::Apply(app) => {
                let r_ = self.fresh();
                let f_ = self.infer(&app.0, env, tenv)?;
                let a_: Vec<_> = app
                    .1
                    .iter()
                    .map(|a| self.infer(a, env, tenv))
                    .collect::<Result<_, _>>()?;
                let atys = a_.iter().map(Expr::get_type).collect();
                let ty = Type::Fn(Rc::new((atys, r_.clone())));
                self.unify(&f_.get_type(), &ty)?;
                Ok(Expr::annotate(r_, Expr::apply(f_, a_)))
            }

            Expr::Lambda(lam) => {
                let rt = self.fresh();

                let mut ats = vec![];
                let mut env_ = env.clone();
                for p in &lam.params {
                    let at = self.fresh();
                    ats.push(at.clone());
                    env_.insert(p.clone(), at);
                }
                let body_ = self.check_expr(&lam.body, &rt, &env_, &tenv)?;

                Ok(Expr::annotate(
                    Type::Fn(Rc::new((ats, rt))),
                    Expr::lambda(lam.params.clone(), body_),
                ))
            }

            Expr::Defs(defs) => {
                let (defs, body) = &**defs;
                let mut def_env = env.clone();
                let def_tenv = Rc::new(RefCell::new(tenv.clone()));

                for def in defs {
                    match def {
                        Def::Func(def) => {
                            let signature = Type::Generic(Rc::new(GenericType::GenericFn {
                                tvars: def.tvars.clone(),
                                ptypes: def.ptypes.clone(),
                                rtype: def.rtype.clone(),
                                tenv: def_tenv.clone(),
                            }));
                            def_env.insert(def.fname.clone(), signature);
                        }
                        Def::Enum(def) => {
                            let type_constructor = Type::Generic(Rc::new(
                                GenericType::GenericEnum(def.clone(), def_tenv.clone()),
                            ));

                            def_tenv
                                .borrow_mut()
                                .insert(def.tname.clone(), type_constructor);
                        }
                        Def::InferredFunc(_) => unreachable!(),
                    }
                }

                let mut defs_ = vec![];

                for def in defs {
                    match def {
                        Def::Func(def) => {
                            let mut tenv_ = def_tenv.borrow().clone();
                            tenv_.extend(
                                def.tvars
                                    .iter()
                                    .map(|tv| (tv.to_string(), Type::Opaque(tv.to_string()))),
                            );

                            let tx = &def.rtype;
                            let rt = self.teval(tx, &tenv_);
                            let pts: Vec<_> =
                                def.ptypes.iter().map(|tx| self.teval(tx, &tenv_)).collect();
                            let ft = Type::Fn(Rc::new((pts.clone(), rt.clone())));

                            let mut env_ = def_env.clone();
                            env_.insert(def.fname.clone(), ft);
                            for (pn, pt) in def.params.iter().zip(pts) {
                                env_.insert(pn.clone(), pt);
                            }

                            let body_ = self.check_expr(&def.body, &rt, &env_, &tenv_)?;

                            let signature = def_env[&def.fname].clone();

                            defs_.push(Def::inferred_func(
                                signature,
                                &def.fname,
                                def.params.clone(),
                                body_,
                            ));
                        }
                        Def::Enum(_) => {}
                        Def::InferredFunc(_) => unreachable!(),
                    }
                }

                let body_ = self.infer(body, &def_env, &*def_tenv.borrow())?;
                Ok(Expr::defs(defs_, body_))
            }

            Expr::Impl(_) => todo!(),

            Expr::Sequence(xs) => {
                let (first, next) = &**xs;
                let first_ = self.check_expr(first, &Type::Unit, env, tenv)?;
                let next_ = self.infer(next, env, tenv)?;
                Ok(Expr::sequence([first_, next_]))
            }

            Expr::Add(ops) => {
                let (a, b) = &**ops;
                let a_ = self.infer(a, env, tenv)?;
                let b_ = self.infer(b, env, tenv)?;
                self.unify(&a_.get_type(), &b_.get_type())?;
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
            Expr::Unit => Ok(Expr::Unit),
            Expr::Int(x) => Ok(Expr::Int(*x)),
            Expr::Real(x) => Ok(Expr::Real(*x)),
            Expr::String(x) => Ok(Expr::String(x.clone())),
            Expr::Ref(x) => Ok(Expr::Ref(x.clone())),

            Expr::Apply(app) => Ok(Expr::apply(
                self.resolve_expr(&app.0)?,
                app.1
                    .iter()
                    .map(|f| self.resolve_expr(f))
                    .collect::<Result<Vec<_>, _>>()?,
            )),

            Expr::Record(fields) => fields
                .iter()
                .map(|f| self.resolve_expr(f))
                .collect::<Result<Vec<_>, _>>()
                .map(Expr::record),

            Expr::Select(sel) => Ok(Expr::select(sel.0, self.resolve_expr(&sel.1)?)),

            Expr::Cons(_) => Ok(expr.clone()),

            Expr::MatchEnum(mat) => Ok(Expr::match_enum(
                self.resolve_expr(&mat.0)?,
                mat.1
                    .iter()
                    .map(|arm| {
                        self.resolve_expr(&arm.branch)
                            .map(|br| (arm.pattern.clone(), br).into())
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            )),

            Expr::Lambda(lam) => Ok(Expr::lambda(
                lam.params.clone(),
                self.resolve_expr(&lam.body)?,
            )),

            Expr::Defs(defs) => {
                let mut defs_ = vec![];

                for d in &defs.0 {
                    match d {
                        Def::Func(_) => unreachable!(),
                        Def::Enum(_) => unreachable!(),
                        Def::InferredFunc(fun) => defs_.push(Def::inferred_func(
                            self.resolve_fully(&fun.signature)?,
                            &fun.fname,
                            fun.params.clone(),
                            self.resolve_expr(&fun.body)?,
                        )),
                    }
                }

                Ok(Expr::defs(defs_, self.resolve_expr(&defs.1)?))
            }

            Expr::Impl(_) => todo!(),

            Expr::Sequence(xs) => Ok(Expr::sequence([
                self.resolve_expr(&xs.0)?,
                self.resolve_expr(&xs.1)?,
            ])),

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
        //println!("unify {t1:?} = {t2:?} : {t1_:?} = {t2_:?}");
        match (t1_, t2_) {
            (Generic(g), _) | (_, Generic(g)) => Err(format!("Uninstantiated generic: {g:?}")),

            (Var(v), t) | (t, Var(v)) => {
                assert!(self.substitutions[v].is_none());
                self.substitutions[v] = Some(t);
                Ok(())
            }

            (Fn(a), Fn(b)) => {
                let (psa, ra) = &*a;
                let (psb, rb) = &*b;
                for (pa, pb) in psa.iter().zip(psb) {
                    self.unify(pa, pb)?;
                }
                self.unify(ra, rb)
            }

            (Record(a), Record(b)) if a.len() == b.len() => {
                for (a_, b_) in a.iter().zip(b.iter()) {
                    self.unify(a_, b_)?;
                }
                Ok(())
            }

            (Enum(a), Enum(b)) if Rc::ptr_eq(&a, &b) => panic!(),
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

            (GenericInstance(a), GenericInstance(b)) if Rc::ptr_eq(&a.generic, &b.generic) => {
                assert_eq!(a.targs.len(), b.targs.len());
                for (ta, tb) in a.targs.iter().zip(b.targs.iter()) {
                    self.unify(ta, tb)?
                }
                Ok(())
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
        let mut resolved_lazies = HashMap::new();
        self.resolve_fully_(t, &mut resolved_lazies)
    }

    fn resolve_fully_<'a>(
        &'a self,
        t: &'a Type,
        resolved_lazies: &mut HashMap<*const RefCell<Option<Type>>, Rc<RefCell<Option<Type>>>>,
    ) -> Result<Type, String> {
        match t {
            Type::Unit | Type::Int | Type::Real | Type::String | Type::Opaque(_) => Ok(t.clone()),

            Type::Var(_) => match self.resolve(t) {
                t_ @ Type::Var(_) => Err(format!("{t:?} resolves to {t_:?}")),
                t_ => self.resolve_fully_(&t_, resolved_lazies),
            },

            Type::Fn(fun) => Ok(Type::func(
                fun.0
                    .iter()
                    .map(|f| self.resolve_fully_(f, resolved_lazies))
                    .collect::<Result<Vec<_>, _>>()?,
                self.resolve_fully_(&fun.1, resolved_lazies)?,
            )),

            Type::Generic(_) => Ok(t.clone()),

            Type::Record(fields) => fields
                .iter()
                .map(|f| self.resolve_fully_(f, resolved_lazies))
                .collect::<Result<Vec<_>, _>>()
                .map(Rc::new)
                .map(Type::Record),

            Type::Enum(enu) => enu
                .variants
                .iter()
                .map(|(v, args)| {
                    args.iter()
                        .map(|a| self.resolve_fully_(a, resolved_lazies))
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

            Type::GenericInstance(gi) => Ok(Type::GenericInstance(Rc::new(GenericInstance {
                generic: gi.generic.clone(),
                targs: gi
                    .targs
                    .iter()
                    .map(|t| self.resolve_fully_(t, resolved_lazies))
                    .collect::<Result<_, _>>()?,
                actual_t: gi
                    .actual_t
                    .borrow()
                    .as_ref()
                    .map(|t| self.resolve_fully_(&t, resolved_lazies))
                    .transpose()
                    .map(RefCell::new)?,
            }))),
        }
    }

    fn fresh(&mut self) -> Type {
        let nr = self.substitutions.len();
        self.substitutions.push(None);
        Type::Var(nr)
    }

    fn teval(&mut self, tx: &TyExpr, tenv: &HashMap<String, Type>) -> Type {
        //println!("teval {tx:?}");
        match tx {
            TyExpr::Unit => Type::Unit,
            TyExpr::Int => Type::Int,
            TyExpr::Real => Type::Real,
            TyExpr::String => Type::String,
            TyExpr::Named(v) => {
                let t = tenv
                    .get(v)
                    .cloned()
                    .unwrap_or_else(|| panic!("Unknown {v}"));
                match t {
                    Type::Generic(generic) => {
                        let targs = (0..generic.n_type_args()).map(|_| self.fresh()).collect();
                        Type::GenericInstance(Rc::new(GenericInstance {
                            generic,
                            targs,
                            actual_t: RefCell::new(None),
                        }))
                    }
                    _ => t,
                }
            }
            TyExpr::Fn(sig) => Type::Fn(Rc::new((
                sig.0.iter().map(|tx| self.teval(tx, tenv)).collect(),
                self.teval(&sig.1, tenv),
            ))),
            TyExpr::Record(fts) => {
                Type::Record(Rc::new(fts.iter().map(|tx| self.teval(tx, tenv)).collect()))
            }
            TyExpr::Construct(con) => match tenv.get(&con.0) {
                None => panic!("Unknown {}", con.0),
                Some(Type::Generic(tc)) => {
                    assert_eq!(con.1.len(), tc.n_type_args());
                    let targs = con.1.iter().map(|t| self.teval(t, tenv)).collect();
                    Type::GenericInstance(Rc::new(GenericInstance {
                        generic: tc.clone(),
                        targs,
                        actual_t: RefCell::new(None),
                    }))
                }
                Some(t) => {
                    panic!("Not a type constructor: {:?}", t)
                }
            },
        }
    }
}

pub enum GenericType {
    GenericFn {
        tvars: Vec<String>,
        ptypes: Vec<TyExpr>,
        rtype: TyExpr,
        tenv: Rc<RefCell<HashMap<String, Type>>>,
    },

    GenericEnum(EnumDef, Rc<RefCell<HashMap<String, Type>>>),
}

impl Debug for GenericType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            GenericType::GenericFn { .. } => write!(f, "<generic fn>"),
            GenericType::GenericEnum(_, _) => write!(f, "<generic enum>"),
        }
    }
}

impl PartialEq for GenericType {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                GenericType::GenericFn {
                    tvars: atv,
                    ptypes: atps,
                    rtype: atr,
                    ..
                },
                GenericType::GenericFn {
                    tvars: btv,
                    ptypes: btps,
                    rtype: btr,
                    ..
                },
            ) => atv == btv && atps == btps && atr == btr,

            (GenericType::GenericEnum(a, _), GenericType::GenericEnum(b, _)) => a == b,
            _ => false,
        }
    }
}

impl GenericType {
    pub fn get_name(&self) -> &str {
        match self {
            GenericType::GenericFn { .. } => todo!(),
            GenericType::GenericEnum(ed, _) => &ed.tname,
        }
    }

    pub fn n_type_args(&self) -> usize {
        match self {
            GenericType::GenericFn { tvars, .. } => tvars.len(),
            GenericType::GenericEnum(EnumDef { tvars, .. }, _) => tvars.len(),
        }
    }

    pub fn to_enum(self: &Rc<Self>, targs: Vec<Type>, ctx: &mut Checker) -> Option<Rc<EnumType>> {
        match &**self {
            GenericType::GenericEnum(_, _) => match self.instantiate_with(targs, ctx) {
                Type::Enum(enum_) => Some(enum_),
                _ => None,
            },
            _ => None,
        }
    }

    fn instantiate_fresh(self: &Rc<Self>, ctx: &mut Checker) -> Type {
        match &**self {
            GenericType::GenericFn { tvars, .. } => {
                let args = tvars.iter().map(|_| ctx.fresh()).collect();
                self.instantiate_with(args, ctx)
            }
            GenericType::GenericEnum(ed, _) => {
                let args = ed.tvars.iter().map(|_| ctx.fresh()).collect();
                self.instantiate_with(args, ctx)
            }
        }
    }

    fn instantiate_with(self: &Rc<Self>, args: Vec<Type>, ctx: &mut Checker) -> Type {
        //println!("instantiate {self:?} {args:?}");
        match &**self {
            GenericType::GenericFn {
                tvars,
                ptypes,
                rtype,
                tenv,
            } => {
                assert_eq!(tvars.len(), args.len());
                let mut tenv = tenv.borrow().clone();
                tenv.extend(tvars.iter().zip(args).map(|(tv, t)| (tv.to_string(), t)));

                let rt = ctx.teval(rtype, &tenv);
                let pts = ptypes.iter().map(|pt| ctx.teval(pt, &tenv)).collect();
                Type::Fn(Rc::new((pts, rt)))
            }
            GenericType::GenericEnum(ed, tenv) => {
                assert_eq!(ed.tvars.len(), args.len());
                let mut tenv = tenv.borrow().clone();
                tenv.extend(ed.tvars.iter().zip(args).map(|(tv, t)| (tv.to_string(), t)));

                let mut variants = HashMap::new();
                for v in &**ed.variants {
                    variants.insert(
                        v.name.clone(),
                        v.tyxs.iter().map(|tx| ctx.teval(tx, &tenv)).collect(),
                    );
                }

                Type::Enum(Rc::new(EnumType {
                    template: self.clone(),
                    variants,
                }))
            }
        }
    }
}

impl Type {
    pub fn check_enum(&self, ctx: &mut Checker) -> Option<Rc<EnumType>> {
        match self {
            Type::Enum(et) => Some(et.clone()),
            Type::GenericInstance(gi) => {
                let mut act = gi.actual_t.borrow_mut();
                match act.as_mut() {
                    None => {
                        let t = gi.generic.to_enum(gi.targs.to_vec(), ctx)?;
                        *act = Some(Type::Enum(t.clone()));
                        Some(t)
                    }
                    Some(Type::Enum(e)) => Some(e.clone()),
                    _ => panic!("invalid instance type"),
                }
            }
            _ => None,
        }
    }

    pub fn expect_enum(&self) -> Option<Rc<EnumType>> {
        match self {
            Type::Enum(et) => Some(et.clone()),
            Type::GenericInstance(gi) => match &*gi.actual_t.borrow() {
                None => None,
                Some(Type::Enum(e)) => Some(e.clone()),
                Some(_) => panic!("invalid instance type"),
            },
            _ => None,
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
                [TyExpr::Int],
                TyExpr::Int,
                ["x"],
                "x",
            )],
            Expr::apply("fn", [0]),
        );

        let y = Expr::defs(
            [Def::inferred_func(
                Type::Generic(Rc::new(GenericType::GenericFn {
                    tvars: vec![],
                    ptypes: vec![TyExpr::Int],
                    rtype: TyExpr::Int,
                    tenv: Default::default(),
                })),
                "fn",
                ["x"],
                Expr::annotate(Type::Int, "x"),
            )],
            Expr::annotate(
                Type::Int,
                Expr::apply(
                    Expr::annotate(Type::func([Type::Int], Type::Int), "fn"),
                    [0],
                ),
            ),
        );

        assert_eq!(Checker::check_program(&x), Ok(y));
    }

    #[test]
    fn check_lambdas() {
        let x = Expr::apply(Expr::lambda(["x"], "x"), [0]);
        let y = Expr::annotate(
            Type::Int,
            Expr::apply(
                Expr::annotate(
                    Type::func([Type::Int], Type::Int),
                    Expr::lambda(["x"], Expr::annotate(Type::Int, "x")),
                ),
                [0],
            ),
        );
        assert_eq!(Checker::check_program(&x), Ok(y));

        let x = Expr::apply(Expr::lambda(["x"], "x"), [Expr::Real(0.0)]);
        let y = Expr::annotate(
            Type::Real,
            Expr::apply(
                Expr::annotate(
                    Type::func([Type::Real], Type::Real),
                    Expr::lambda(["x"], Expr::annotate(Type::Real, "x")),
                ),
                [Expr::real(0.0)],
            ),
        );
        assert_eq!(Checker::check_program(&x), Ok(y));
    }

    #[test]
    fn check_generic() {
        let x = Expr::defs(
            [Def::func("fn", vec!["T"], ["T"], "T", ["x"], "x")],
            Expr::apply("fn", [0]),
        );
        assert!(Checker::check_program(&x).is_ok());
    }

    #[test]
    fn fail_generic_def() {
        let x = Expr::defs(
            [Def::func("fn", vec!["T"], ["T"], "T", ["x"], 0)],
            Expr::apply("fn", [0]),
        );
        assert!(Checker::check_program(&x).is_err());
    }

    #[test]
    fn check_generic_different_uses() {
        // (let ((id (lambda (x) x))) ((id id) 42))
        let x = Expr::defs(
            [Def::func("id", vec!["T"], ["T"], "T", ["x"], "x")],
            Expr::apply(Expr::apply("id", ["id"]), [42]),
        );

        let y = Expr::defs(
            [Def::inferred_func(
                Type::Generic(Rc::new(GenericType::GenericFn {
                    tvars: vec!["T".into()],
                    ptypes: vec![TyExpr::Named("T".into())],
                    rtype: TyExpr::Named("T".into()),
                    tenv: Default::default(),
                })),
                "id",
                ["x"],
                Expr::annotate(Type::Opaque("T".into()), "x"),
            )],
            Expr::annotate(
                Type::Int,
                Expr::apply(
                    Expr::annotate(
                        Type::func([Type::Int], Type::Int),
                        Expr::apply(
                            Expr::annotate(
                                Type::func(
                                    [Type::func([Type::Int], Type::Int)],
                                    Type::func([Type::Int], Type::Int),
                                ),
                                "id",
                            ),
                            [Expr::annotate(Type::func([Type::Int], Type::Int), "id")],
                        ),
                    ),
                    [42],
                ),
            ),
        );

        assert_eq!(Checker::check_program(&x), Ok(y));

        let x = Expr::defs(
            [
                Def::func("twice", vec!["T"], ["T"], "T", ["x"], Expr::add("x", "x")),
                Def::func("swallow", vec!["T"], ["T"], TyExpr::Int, ["x"], 0),
            ],
            Expr::apply(
                "swallow",
                [Expr::record([
                    Expr::apply("twice", [21]),
                    Expr::apply("twice", [1.23]),
                ])],
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
                ["T"],
                TyExpr::func(["S"], "T"),
                ["x"],
                Expr::lambda(["y"], "x"),
            )],
            Expr::apply(Expr::apply("f", [42]), [1.2]),
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
            Ok(Expr::Unit)
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
                ("A", ("B", [TyExpr::Int]), ()),
            )],
            Expr::defs(
                [Def::func(
                    "f",
                    vec![] as Vec<&str>,
                    [("Foo",)],
                    TyExpr::Int,
                    ["x"],
                    Expr::Int(0),
                )],
                Expr::apply("f", [Expr::apply(Expr::cons("Foo", "B"), [1])]),
            ),
        );
        Checker::check_program(&x).unwrap();
    }

    #[test]
    fn check_generic_enum() {
        let x = Expr::defs(
            [
                Def::enum_("Foo", ["T"], ("A", ("B", ["T"]), ())),
                Def::func(
                    "f",
                    vec!["T"] as Vec<&str>,
                    [("Foo", "T")],
                    TyExpr::Int,
                    ["x"],
                    Expr::Int(0),
                ),
            ],
            Expr::apply("f", [Expr::apply(Expr::cons("Foo", "B"), [1])]),
        );

        let foo = Rc::new(GenericType::GenericEnum(
            EnumDef {
                tname: "Foo".to_string(),
                tvars: vec!["T".into()],
                variants: Rc::new(vec![
                    EnumVariant::constant("A"),
                    EnumVariant::constructor("B", ["T"]),
                ]),
            },
            Default::default(),
        ));

        let foo_int = Type::GenericInstance(Rc::new(GenericInstance {
            generic: foo,
            targs: vec![Type::Int],
            actual_t: Default::default(),
        }));

        let y = Expr::defs(
            [Def::inferred_func(
                Type::Generic(Rc::new(GenericType::GenericFn {
                    tvars: vec!["T".into()],
                    ptypes: vec![("Foo", "T").into()],
                    rtype: TyExpr::Int,
                    tenv: Default::default(),
                })),
                "f",
                ["x"],
                Expr::Int(0),
            )],
            Expr::annotate(
                Type::Int,
                Expr::apply(
                    Expr::annotate(Type::func([foo_int.clone()], Type::Int), "f"),
                    [Expr::annotate(
                        foo_int.clone(),
                        Expr::apply(
                            Expr::annotate(
                                Type::func([Type::Int], foo_int.clone()),
                                Expr::cons("Foo", "B"),
                            ),
                            [1],
                        ),
                    )],
                ),
            ),
        );

        assert_eq!(Checker::check_program(&x), Ok(y));
    }

    #[test]
    fn check_enum_deconstruction() {
        let x = Expr::defs(
            [Def::enum_::<&str>(
                "Foo",
                [],
                ("A", ("B", [TyExpr::Int]), ()),
            )],
            Expr::match_enum(
                Expr::apply(Expr::cons("Foo", "B"), [1]),
                [(EnumVariantPattern::constructor("B", ["x"]), Expr::var("x"))],
            ),
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
                ["T"],
                "T",
                ["x"],
                Expr::add("x", "x"),
            )],
            Expr::apply("double", [21]),
        );
        assert!(Checker::check_program(&x).is_ok());
    }

    #[test]
    fn cant_infer() {
        let x = Expr::defs(
            [Def::func("foo", vec!["T"], ["T"], TyExpr::Int, ["x"], 0)],
            Expr::apply("foo", [Expr::Read()]),
        );
        assert_eq!(
            Checker::check_program(&x),
            Err("'1 resolves to '2".to_string())
        );
    }

    #[test]
    fn infer_recursive_enum() {
        let x = Expr::from_str(
            "(define ((enum (Nat) Z (S Nat)))
                    (Nat . Z))",
        )
        .unwrap();

        Checker::new()
            .infer(&x, &Default::default(), &Default::default())
            .unwrap();
    }

    #[test]
    fn check_recursive_enum() {
        let x = Expr::from_str(
            "(define ((enum (Nat) Z (S Nat)))
                    (Nat . Z))",
        )
        .unwrap();

        Checker::check_program(&x).unwrap();
    }

    #[test]
    fn check_recursive_enum_usage() {
        let x = Expr::from_str(
            "(define ((enum (Peano) Z (S Peano))
                               (func () (peano->int (n : Peano) -> Int)
                                 0))
                    (peano->int (Peano . Z)))",
        )
        .unwrap();

        Checker::check_program(&x).unwrap();
    }

    #[ignore]
    #[test]
    fn check_impl_blocks() {
        todo!()
    }
}
