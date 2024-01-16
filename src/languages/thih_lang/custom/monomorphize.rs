use crate::core::lists::snoc_vec;
use crate::core::persistent::{PersistentMap, PersistentSet};
use crate::languages::thih_lang::custom::my_inference::{MethodImpl, Module};
use crate::languages::thih_lang::haskell_specific::inference::Expr::Annotate;
use crate::languages::thih_lang::haskell_specific::inference::{Alt, BindGroup, Expl, Expr};
use crate::languages::thih_lang::thih_core::instantiate::Instantiate;
use crate::languages::thih_lang::thih_core::qualified::Qual;
use crate::languages::thih_lang::thih_core::scheme::Scheme;
use crate::languages::thih_lang::thih_core::substitutions::Types;
use crate::languages::thih_lang::thih_core::type_inference::TI;
use crate::languages::thih_lang::thih_core::types::{Tycon, Type};
use crate::languages::thih_lang::Id;

fn mangle(name: &str, t: &Type) -> Id {
    format!("{name}@{}", mangle_type(t))
}

fn mangle_type(t: &Type) -> String {
    match t {
        Type::TCon(Tycon(tc, _)) => tc.to_string(),
        Type::TApp(rc) => format!("{}{}", mangle_type(&rc.0), mangle_type(&rc.1)),
        _ => panic!("unexpected type being mangled"),
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Context {
    functions: PersistentMap<Id, Function>,
    usage: PersistentSet<(Id, Type)>,
}

impl Context {
    fn empty() -> Self {
        Context {
            functions: Default::default(),
            usage: PersistentSet::empty(),
        }
    }
    pub fn new(module: &Module) -> Self {
        let mut ctx = Context::empty();

        let BindGroup(expls, imp) = &module.free_bindings;
        assert!(
            imp.is_empty(),
            "After type inference it should be possible to convert implicits to explicits."
        );

        for expl in expls {
            ctx = ctx.bind_expl(expl);
        }

        for mipl in &module.impls {
            ctx = ctx.bind_method(mipl);
        }

        ctx
    }

    /// A program consists of an expression and some definitions in form of a module
    pub fn monomorphize_standalone(expr: &Expr, module: &Module) -> Expr {
        let ctx = Context::new(&module);
        let (ctx, expr_) = ctx.monomorphize_expr(expr);

        let mut expls = vec![];
        for (fname, ty) in ctx.usage.iter() {
            let mname = mangle(fname, ty);

            let fun = ctx.functions.get(fname).unwrap();

            if !fun.specializations.is_empty() {
                todo!("find correct specialized function impl for type")
            }

            let mut ti = TI::new();
            let Qual(_, tf) = ti.fresh_inst(&fun.sc);
            ti.unify(ty, &tf).unwrap();

            let ts: Vec<_> = tf.tv().into_iter().map(Type::TVar).collect();
            let impl_ = fun.default_impl.inst(&ts);

            let alts = ti.get_subst().apply(&impl_);
            expls.push(Expl(mname, ty.clone().to_scheme(), alts));
        }
        Expr::Let(BindGroup(expls, vec![]), expr_.into())
    }

    fn monomorphize_expr(&self, expr: &Expr) -> (Self, Expr) {
        match expr {
            Expr::Var(x) => panic!("unannotated variable"),

            Expr::Lit(_) | Expr::Const(_, _) => (self.clone(), expr.clone()),

            Expr::App(f, a) => {
                let (ctx_, f_) = self.monomorphize_expr(f);
                let (ctx__, a_) = ctx_.monomorphize_expr(a);
                (ctx__, Expr::App(f_.into(), a_.into()))
            }

            Expr::Let(BindGroup(expls, impls), _) => todo!(),

            Expr::Annotate(ty, x) => match &**x {
                Expr::Var(v) => match self.functions.get(v) {
                    None => (self.clone(), expr.clone()),
                    Some(f) => {
                        let mut ti = TI::new();
                        let Qual(_, tf) = ti.fresh_inst(&f.sc);
                        ti.unify(&tf, ty).unwrap();
                        let t_ = ti.get_subst().apply(&tf);

                        if !t_.tv().is_empty() {
                            panic!("unset type variable");
                        }

                        let ctx_ = self.mark_usage(v, ty.clone());
                        (
                            ctx_,
                            Expr::Annotate(ty.clone(), Expr::Var(mangle(v, ty)).into()),
                        )
                    }
                },

                _ => {
                    let (ctx_, x_) = self.monomorphize_expr(x);
                    (ctx_, Annotate(ty.clone(), x_.into()))
                }
            },
        }
    }
    fn bind_expl(&self, Expl(id, sc, alts): &Expl) -> Self {
        Context {
            functions: self
                .functions
                .insert(id.clone(), Function::free(sc.clone(), alts.clone())),
            usage: self.usage.clone(),
        }
    }
    fn bind_method(
        &self,
        MethodImpl {
            method,
            sc,
            ty,
            alts,
        }: &MethodImpl,
    ) -> Self {
        Context {
            functions: self.functions.upsert(
                method.clone(),
                |f| f.update_method(ty.clone(), alts.clone()),
                || Function::new_method(sc.clone(), ty.clone(), alts.clone()),
            ),
            usage: self.usage.clone(),
        }
    }

    fn mark_usage(&self, id: impl Into<Id>, t: Type) -> Self {
        Context {
            functions: self.functions.clone(),
            usage: self.usage.insert((id.into(), t.into())),
        }
    }
}

#[derive(Debug, PartialEq)]
struct Function {
    sc: Scheme,
    default_impl: Vec<Alt>,
    specializations: Vec<(Type, Vec<Alt>)>,
}

impl Function {
    pub fn free(sc: Scheme, default_impl: Vec<Alt>) -> Self {
        Function {
            sc,
            default_impl,
            specializations: vec![],
        }
    }

    pub fn new_method(sc: Scheme, ty: Type, alts: Vec<Alt>) -> Self {
        Function {
            sc: sc,
            default_impl: vec![],
            specializations: vec![(ty, alts)],
        }
    }

    pub fn update_method(&self, ty: Type, alts: Vec<Alt>) -> Self {
        assert!(self
            .specializations
            .iter()
            .filter(|(t, _)| t == &ty)
            .next()
            .is_none());

        Function {
            sc: self.sc.clone(),
            default_impl: self.default_impl.clone(),
            specializations: snoc_vec(self.specializations.clone(), (ty, alts)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::thih_lang::custom::my_inference::ti_standalone;
    use crate::languages::thih_lang::haskell_specific::assumptions::Assumptions;
    use crate::languages::thih_lang::haskell_specific::classes::ClassEnv;
    use crate::languages::thih_lang::haskell_specific::inference::Expr::{App, Let, Lit, Var};
    use crate::languages::thih_lang::haskell_specific::inference::Literal;
    use crate::languages::thih_lang::haskell_specific::inference::Literal::Char;
    use crate::languages::thih_lang::haskell_specific::inference::Pat::PVar;
    use crate::languages::thih_lang::haskell_specific::types::{func, t_char};
    use crate::languages::thih_lang::thih_core::kinds::Kind::Star;
    use crate::languages::thih_lang::thih_core::qualified::Qual;
    use crate::languages::thih_lang::thih_core::scheme::Scheme::Forall;
    use crate::languages::thih_lang::thih_core::types::Type::TGen;
    use crate::list;

    #[test]
    fn monomorphize_simple_expr() {
        let x = Lit(Literal::Int(0));
        assert_eq!(
            Context::empty().monomorphize_expr(&x),
            (Context::empty(), x)
        );
    }

    #[test]
    fn monomorphize_identity_function() {
        let module = Module {
            impls: vec![],
            free_bindings: BindGroup(
                vec![Expl(
                    "ident".into(),
                    Forall(list![Star], Qual(vec![], func(TGen(0), TGen(0)))),
                    vec![Alt(vec![PVar("x".into())], Var("x".into()))],
                )],
                vec![],
            ),
        };

        let x = App(
            App(Var("ident".into()).into(), Var("ident".into()).into()).into(),
            Lit(Char('z')).into(),
        );

        let (x_, module_) =
            ti_standalone(&ClassEnv::default(), &Assumptions::empty(), &x, &module).unwrap();

        let ident1 = "ident@->CharChar";
        let ident2 = "ident@->->CharChar->CharChar";
        let fcc = func(t_char(), t_char());
        let ffccfcc = func(fcc.clone(), fcc.clone());

        let y = Let(
            BindGroup(
                vec![
                    Expl(
                        ident2.into(),
                        Forall(list![], Qual(vec![], ffccfcc.clone())),
                        vec![Alt(
                            vec![PVar("x".into())],
                            Annotate(fcc.clone(), Var("x".into()).into()),
                        )],
                    ),
                    Expl(
                        ident1.into(),
                        Forall(list![], Qual(vec![], fcc.clone())),
                        vec![Alt(
                            vec![PVar("x".into())],
                            Annotate(t_char(), Var("x".into()).into()),
                        )],
                    ),
                ],
                vec![],
            ),
            Annotate(
                t_char(),
                App(
                    Annotate(
                        fcc.clone(),
                        App(
                            Annotate(ffccfcc, Var(ident2.into()).into()).into(),
                            Annotate(fcc, Var(ident1.into()).into()).into(),
                        )
                        .into(),
                    )
                    .into(),
                    Annotate(t_char(), Lit(Char('z')).into()).into(),
                )
                .into(),
            )
            .into(),
        );

        assert_eq!(Context::monomorphize_standalone(&x_, &module_), y);
    }
}
