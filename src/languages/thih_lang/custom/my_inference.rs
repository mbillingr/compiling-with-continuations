use super::super::haskell_specific::assumptions::{find, Assumptions};
use super::super::haskell_specific::classes::ClassEnv;
use super::super::haskell_specific::inference::{
    ti_expl, ti_program, Alt, BindGroup, Expl, Program,
};
use super::super::thih_core::kinds::HasKind;
use super::super::thih_core::scheme::Scheme;
use super::super::thih_core::substitutions::Types;
use super::super::thih_core::type_inference::TI;
use super::super::thih_core::types::{Type, Tyvar};
use super::super::{Id, Result};
use crate::languages::thih_lang::haskell_specific::inference::{ti_expr, Expr};

#[derive(Debug)]
pub struct MethodImpl {
    pub method: Id,
    pub sc: Scheme,
    pub ty: Type,
    pub alts: Vec<Alt>,
}

#[derive(Debug)]
pub struct Module {
    pub impls: Vec<MethodImpl>,
    pub free_bindings: BindGroup,
}

pub fn ti_module(
    ce: &ClassEnv,
    ass: &Assumptions,
    Module {
        impls,
        free_bindings,
    }: &Module,
) -> Result<(Module, Assumptions)> {
    let pg = Program(vec![free_bindings.clone()]);
    let (bg_, mut ass_) = match ti_program(ce, ass, &pg)? {
        (Program(mut bgs), ass_) => (bgs.pop().unwrap(), ass_),
    };
    let ass_ = ass.extend(&ass_);

    let mut impls_ = vec![];
    for MethodImpl {
        method,
        sc,
        ty,
        alts,
    } in impls
    {
        let (mut ti, sc_) = method_context(&ty, sc)?;

        let expl = Expl(method.clone(), sc_, alts.clone());
        let (Expl(_, _, alts_), _) = ti_expl(&mut ti, ce, &ass_, &expl)?;

        println!("{:?}", alts_);
        impls_.push(MethodImpl {
            method: method.clone(),
            sc: sc.clone(),
            ty: ty.clone(),
            alts: alts_,
        })
    }

    Ok((
        Module {
            impls: impls_,
            free_bindings: bg_,
        },
        ass_,
    ))
}

/// Partially instantiate the first type variable in a type scheme.
/// The scheme is assumed to be a method signature, and the type is assumed to be the
/// argument to the class's type parameter.
/// The result can be used to check the method body.
fn method_context(ty: &Type, sc: &Scheme) -> Result<(TI, Scheme)> {
    let mut ti = TI::new();

    let q = ti.fresh_inst(sc);

    // This is super hacky and relies on the following assumptions:
    //   - the first fresh variable is named `v0`
    //   - the first fresh variable created by fresh_inst above is the class type parameter
    //   - subsequent unifications will detect if ty has the wrong kind, which we simply force here
    ti.unify(&Type::TVar(Tyvar("v0".into(), ty.kind()?.clone())), ty)?;
    let q_ = ti.get_subst().apply(&q);

    let sc = Scheme::quantify(&q.tv(), &q_);

    Ok((ti, sc))
}

pub fn ti_standalone(
    ce: &ClassEnv,
    ass: &Assumptions,
    expr: &Expr,
    module: &Module,
) -> Result<(Expr, Module)> {
    let (module_, ass_) = ti_module(ce, ass, &module)?;

    let mut ti = TI::new();
    let (x_, _, _) = ti_expr(&mut ti, ce, &ass_, expr)?;
    let x_ = ti.get_subst().apply(&x_);

    Ok((x_, module_))
}
