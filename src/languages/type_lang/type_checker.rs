use crate::languages::type_lang::ast::{Expr, TyExpr};
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::rc::Rc;

struct Checker {
    substitutions: Vec<Option<Type>>,
}

impl Checker {
    fn new() -> Self {
        Checker {
            substitutions: vec![],
        }
    }
    fn check_program(expr: &Expr) -> Result<(), String> {
        Checker::new().check_expr(expr, Type::Int, &HashMap::new(), &HashMap::new())
    }

    fn check_expr(
        &mut self,
        expr: &Expr,
        ty: Type,
        env: &HashMap<String, Type>,  // types of variables
        tenv: &HashMap<String, Type>, // defined types
    ) -> Result<(), String> {
        match expr {
            _ => {
                let t = self.infer(expr, env, tenv)?;
                self.unify(t, ty)
            }
        }
    }

    fn infer(
        &mut self,
        expr: &Expr,
        env: &HashMap<String, Type>,
        tenv: &HashMap<String, Type>,
    ) -> Result<Type, String> {
        match expr {
            Expr::Int(_) => Ok(Type::Int),
            Expr::Real(_) => Ok(Type::Real),

            Expr::Ref(var) => match env.get(var) {
                None => Err(format!("unbound {var}")),
                Some(Type::Generic(g)) => Ok(g.instantiate(self)),
                Some(t) => Ok(t.clone()),
            },

            Expr::Apply(app) => {
                let tr = self.fresh();
                let t = self.infer(&app.0, env, tenv)?;
                let ta = self.infer(&app.1, env, tenv)?;
                self.unify(t, Type::Fn(Rc::new((ta, tr.clone()))))?;
                Ok(tr)
            }

            Expr::Lambda(lam) => {
                let at = self.fresh();
                let rt = self.fresh();

                let mut env_ = env.clone();
                env_.insert(lam.param.clone(), at.clone());
                self.check_expr(&lam.body, rt.clone(), &env_, &tenv)?;

                Ok(Type::Fn(Rc::new((at, rt))))
            }

            Expr::Fix(fix) => {
                let (def, body) = &**fix;
                {
                    let mut tenv_ = tenv.clone();
                    tenv_.extend(
                        def.tvars
                            .iter()
                            .map(|tv| (tv.to_string(), Type::Named(tv.to_string()))),
                    );

                    let rt = teval(&def.rtype, &tenv_);
                    let pt = teval(&def.ptype, &tenv_);
                    let ft = Type::Fn(Rc::new((pt.clone(), rt.clone())));

                    let mut env_ = env.clone();
                    env_.insert(def.fname.clone(), ft);
                    env_.insert(def.param.clone(), pt);

                    self.check_expr(&def.body, rt, &env_, &tenv_)?;
                }
                {
                    let ft = Type::Generic(Rc::new(GenericFn {
                        tvars: def.tvars.clone(),
                        ptype: def.ptype.clone(),
                        rtype: def.rtype.clone(),
                    }));

                    let mut env_ = env.clone();
                    env_.insert(def.fname.clone(), ft);

                    self.infer(body, &env_, tenv)
                }
            }
        }
    }

    fn unify(&mut self, t1: Type, t2: Type) -> Result<(), String> {
        use Type::*;
        let t1_ = self.resolve(t1);
        let t2_ = self.resolve(t2);
        match (t1_, t2_) {
            (Var(v), t) | (t, Var(v)) => {
                assert!(self.substitutions[v].is_none());
                self.substitutions[v] = Some(t);
                Ok(())
            }

            (Fn(a), Fn(b)) => {
                let (pa, ra) = (*a).clone();
                let (pb, rb) = (*b).clone();
                self.unify(pa, pb)?;
                self.unify(ra, rb)
            }

            (a, b) if a == b => Ok(()),
            (a, b) => Err(format!("{a:?} != {b:?}")),
        }
    }

    fn resolve(&self, t: Type) -> Type {
        match t {
            Type::Var(nr) => self.substitutions[nr].clone().unwrap_or(Type::Var(nr)),
            _ => t,
        }
    }

    fn fresh(&mut self) -> Type {
        let nr = self.substitutions.len();
        self.substitutions.push(None);
        Type::Var(nr)
    }
}

#[derive(Clone)]
enum Type {
    Int,
    Real,
    Named(String),
    Var(usize),
    Fn(Rc<(Type, Type)>),
    Generic(Rc<dyn GenericType>),
}

impl Debug for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Real => write!(f, "Real"),
            Type::Named(name) => write!(f, "{name}"),
            Type::Var(nr) => write!(f, "'{nr}"),
            Type::Fn(sig) => write!(f, "({:?} -> {:?})", sig.0, sig.1),
            Type::Generic(g) => write!(f, "{g:?}"),
        }
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Int, Type::Int) => true,
            (Type::Real, Type::Real) => true,
            (Type::Named(a), Type::Named(b)) => a == b,
            (Type::Var(a), Type::Var(b)) => a == b,
            (Type::Fn(a), Type::Fn(b)) => a == b,
            _ => false,
        }
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

trait GenericType: Debug {
    fn instantiate(&self, ctx: &mut Checker) -> Type;
}

#[derive(Debug)]
struct GenericFn {
    tvars: Vec<String>,
    ptype: TyExpr,
    rtype: TyExpr,
}

impl GenericType for GenericFn {
    fn instantiate(&self, ctx: &mut Checker) -> Type {
        let tenv: HashMap<_, _> = self
            .tvars
            .iter()
            .map(|tv| (tv.to_string(), ctx.fresh()))
            .collect();

        let rt = teval(&self.rtype, &tenv);
        let pt = teval(&self.ptype, &tenv);
        Type::Fn(Rc::new((pt.clone(), rt.clone())))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::type_lang::ast::FixDef;

    #[test]
    fn check_primitives() {
        assert_eq!(Checker::check_program(&Expr::int(42)), Ok(()));
        assert!(Checker::check_program(&Expr::real(4.2)).is_err());
        assert_eq!(
            Checker::new().check_expr(
                &Expr::real(4.2),
                Type::Real,
                &HashMap::new(),
                &HashMap::new()
            ),
            Ok(())
        );
    }

    #[test]
    fn check_lambdas() {
        let x = Expr::apply(Expr::lambda("x", "x"), Expr::int(0));
        assert_eq!(Checker::check_program(&x), Ok(()));

        let x = Expr::apply(Expr::lambda("x", "x"), Expr::Real(0.0));
        assert!(Checker::check_program(&x).is_err());
    }

    #[test]
    fn check_generic() {
        let x = Expr::fix(
            FixDef::new("fn", vec!["T"], "T", "T", "x", "x"),
            Expr::apply("fn", 0),
        );
        assert_eq!(Checker::check_program(&x), Ok(()));
    }

    #[test]
    fn fail_generic_def() {
        let x = Expr::fix(
            FixDef::new("fn", vec!["T"], "T", "T", "x", 0),
            Expr::apply("fn", 0),
        );
        assert!(Checker::check_program(&x).is_err());
    }

    #[test]
    fn fail_generic_use() {
        let x = Expr::fix(
            FixDef::new("fn", vec!["T"], "T", "T", "x", "x"),
            Expr::apply("fn", 1.2),
        );
        assert!(Checker::check_program(&x).is_err());
    }

    #[test]
    fn check_generic_different_uses() {
        // (let ((id (lambda (x) x))) ((id id) 42))
        let x = Expr::fix(
            FixDef::new("id", vec!["T"], "T", "T", "x", "x"),
            Expr::apply(Expr::apply("id", "id"), 42),
        );
        assert_eq!(Checker::check_program(&x), Ok(()));
    }

    #[test]
    fn check_outer_generic() {
        let x = Expr::fix(
            FixDef::new(
                "f",
                vec!["T", "S"],
                "T",
                TyExpr::func("S", "T"),
                "x",
                Expr::lambda("y", "x"),
            ),
            Expr::apply(Expr::apply("f", 42), 1.2),
        );
        assert_eq!(Checker::check_program(&x), Ok(()));
    }
}
