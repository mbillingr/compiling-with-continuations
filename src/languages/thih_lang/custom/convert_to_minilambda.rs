use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::Expr;
use crate::languages::thih_lang::haskell_specific::inference::{Alt, BindGroup, Expl, Literal};

pub type LExp = crate::languages::mini_lambda::ast::Expr<Ref<str>>;
pub type HExp = crate::languages::thih_lang::haskell_specific::inference::Expr;

fn to_mini_lambda(x: &HExp) -> LExp {
    match x {
        HExp::Var(x) => LExp::var(x),
        HExp::Lit(Literal::Int(x)) => LExp::Int(*x),
        HExp::Lit(Literal::Rat(x)) => LExp::Real(*x),
        HExp::Lit(Literal::Char(c)) => LExp::Int(*c as i64),
        HExp::Lit(Literal::Str(s)) => LExp::string(s.to_string()),
        HExp::Const(_, _) => todo!(),
        HExp::App(f, a) => LExp::apply(to_mini_lambda(f), to_mini_lambda(a)),
        HExp::Let(bg, body) => convert_let(bg, body),
        HExp::Annotate(_, x_) => to_mini_lambda(x_),
    }
}

fn convert_let(BindGroup(expls, impls): &BindGroup, body: &HExp) -> LExp {
    assert!(impls.is_empty());

    let funcs: Vec<_> = expls
        .iter()
        .filter(|Expl(_, sc, alts)| !alts[0].0.is_empty())
        .collect();

    let fnames: Vec<Ref<str>> = funcs
        .iter()
        .map(|Expl(id, sc, alts)| id.to_string().into())
        .collect();

    let func_defs: Vec<LExp> = funcs
        .iter()
        .map(|Expl(id, sc, alts)| convert_func(alts))
        .collect();

    let body_ = to_mini_lambda(body);

    let mut res = LExp::Fix(fnames.into(), func_defs.into(), body_.into());

    // todo: this is too simple! constants and functions might use each other.
    //       maybe delegate this problem to the higher level language?

    let constants = expls
        .iter()
        .filter(|Expl(_, sc, alts)| alts[0].0.is_empty());

    for Expl(id, sc, alts) in constants {
        assert_eq!(alts.len(), 1);
        let val = to_mini_lambda(&alts[0].1);
        res = LExp::Let(id.into(), val.into(), res.into())
    }

    res
}

fn convert_func(alts: &[Alt]) -> LExp {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::thih_lang::custom::monomorphize::Context;
    use crate::languages::thih_lang::custom::my_inference::{ti_standalone, Module};
    use crate::languages::thih_lang::haskell_specific::assumptions::Assumptions;
    use crate::languages::thih_lang::haskell_specific::classes::ClassEnv;
    use crate::languages::thih_lang::haskell_specific::inference::Alt;
    use crate::languages::thih_lang::haskell_specific::inference::Expr::{
        Annotate, App, Let, Lit, Var,
    };
    use crate::languages::thih_lang::haskell_specific::inference::Literal;
    use crate::languages::thih_lang::haskell_specific::inference::Literal::Char;
    use crate::languages::thih_lang::haskell_specific::inference::Pat::PVar;
    use crate::languages::thih_lang::haskell_specific::types::t_int;
    use crate::languages::thih_lang::haskell_specific::types::{func, t_char};
    use crate::languages::thih_lang::thih_core::kinds::Kind::Star;
    use crate::languages::thih_lang::thih_core::qualified::Qual;
    use crate::languages::thih_lang::thih_core::scheme::Scheme::Forall;
    use crate::languages::thih_lang::thih_core::types::Type::TGen;
    use crate::list;

    #[test]
    fn convert_var() {
        assert_eq!(to_mini_lambda(&HExp::Var("foo".into())), LExp::var("foo"));
    }

    #[test]
    fn convert_lit() {
        assert_eq!(to_mini_lambda(&HExp::Lit(Literal::Int(42))), LExp::int(42));
        assert_eq!(
            to_mini_lambda(&HExp::Lit(Literal::Rat(1.2))),
            LExp::real(1.2)
        );
        assert_eq!(
            to_mini_lambda(&HExp::Lit(Literal::Char('x'))),
            LExp::int('x' as i64)
        );
        assert_eq!(
            to_mini_lambda(&HExp::Lit(Literal::Str("foo".into()))),
            LExp::string("foo")
        );
    }

    #[test]
    fn convert_app() {
        assert_eq!(
            to_mini_lambda(&HExp::App(
                HExp::Var("foo".into()).into(),
                HExp::Lit(Literal::Int(42)).into()
            )),
            LExp::apply("foo", 42)
        );
    }

    #[test]
    fn convert_annotate() {
        assert_eq!(
            to_mini_lambda(&HExp::Annotate(t_int(), HExp::Var("foo".into()).into())),
            LExp::var("foo")
        );
    }

    #[test]
    fn convert_identity_function() {
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

        let x__ = Context::monomorphize_standalone(&x_, &module_);

        let l_ = to_mini_lambda(&x__);
        assert_eq!(l_, LExp::var(""))
    }
}
