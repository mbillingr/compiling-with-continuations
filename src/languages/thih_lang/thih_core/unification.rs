use super::kinds::HasKind;
use super::substitutions::{Subst, Types};
use super::types::{Type, Tyvar};
use super::Result;

pub fn mgu(a: &Type, b: &Type) -> Result<Subst> {
    use Type::*;
    match (a, b) {
        (TApp(app1), TApp(app2)) => {
            let s1 = mgu(&app1.0, &app2.0)?;
            let s2 = mgu(&s1.apply(&app1.1), &s1.apply(&app2.1))?;
            Ok(s2.compose(&s1))
        }

        (t, TVar(u)) => var_bind(u, t),

        (TVar(u), t) => var_bind(u, t),

        (TCon(tc1), TCon(tc2)) if tc1 == tc2 => Ok(Subst::null_subst()),

        _ => Err(format!("types do not unify: {a:?}, {b:?}"))?,
    }
}

fn var_bind(u: &Tyvar, t: &Type) -> Result<Subst> {
    if let Type::TVar(v) = t {
        if u == v {
            return Ok(Subst::null_subst());
        }
    }

    if t.tv().contains(u) {
        Err("occurs check failed")?
    }

    if u.kind() != t.kind() {
        Err("kinds do not match")?
    }

    Ok(Subst::single(u.clone(), t.clone()))
}

pub fn matches(a: &Type, b: &Type) -> Result<Subst> {
    use Type::*;
    match (a, b) {
        (TApp(app1), TApp(app2)) => {
            let sl = matches(&app1.0, &app2.0)?;
            let sr = matches(&app1.1, &app2.1)?;
            sl.merge(&sr)
        }

        (TVar(u), t) if u.kind() == t.kind() => Ok(Subst::single(u.clone(), t.clone())),

        (TCon(tc1), TCon(tc2)) if tc1 == tc2 => Ok(Subst::null_subst()),

        _ => Err("types do not match")?,
    }
}

#[cfg(test)]
mod tests {
    use super::super::kinds::Kind::Star;
    use super::*;
    use crate::languages::thih_lang::thih_core::kinds::Kind;

    #[test]
    fn mgu_cases() {
        assert_eq!(
            mgu(&Type::tcon("Int"), &Type::tcon("Int")),
            Ok(Subst::null_subst())
        );
        assert!(mgu(&Type::tcon("Int"), &Type::tcon("Bool")).is_err());

        assert_eq!(
            mgu(&Type::tvar("A", Star), &Type::tvar("B", Star)),
            Ok(Subst::single(Tyvar::new("B", Star), Type::tvar("A", Star)))
        );

        let f1 = Type::tapp(Type::tvar("A", Star), Type::tcon("Bool"));
        let f2 = Type::tapp(Type::tcon("Int"), Type::tvar("B", Star));
        assert_eq!(
            mgu(&f1, &f2),
            Ok(Subst::single(Tyvar::new("A", Star), Type::tcon("Int"))
                .merge(&Subst::single(Tyvar::new("B", Star), Type::tcon("Bool")))
                .unwrap())
        );
    }

    #[test]
    fn var_bind_cases() {
        let atv = Tyvar::new("A", Star);
        let at = Type::TVar(atv.clone());
        let btv = Tyvar::new("B", Kind::kfun(Star, Star));

        assert_eq!(var_bind(&atv, &at), Ok(Subst::null_subst()));

        assert_eq!(
            var_bind(&atv, &Type::tapp(at.clone(), at.clone())),
            Err("occurs check failed".into())
        );

        assert_eq!(var_bind(&btv, &at), Err("kinds do not match".into()));

        assert_eq!(
            var_bind(&atv, &Type::tcon("Int")),
            Ok(Subst::single(atv, Type::tcon("Int")))
        );
    }

    #[test]
    fn match_cases() {
        assert_eq!(
            matches(&Type::tcon("Int"), &Type::tcon("Int")),
            Ok(Subst::null_subst())
        );
        assert!(matches(&Type::tcon("Int"), &Type::tcon("Bool")).is_err());

        assert_eq!(
            matches(&Type::tvar("A", Star), &Type::tvar("B", Star)),
            Ok(Subst::single(Tyvar::new("A", Star), Type::tvar("B", Star)))
        );

        let f1 = Type::tapp(Type::tvar("A", Star), Type::tvar("B", Star));
        let f2 = Type::tapp(Type::tcon("Int"), Type::tcon("Bool"));
        assert_eq!(
            matches(&f1, &f2),
            Ok(Subst::single(Tyvar::new("A", Star), Type::tcon("Int"))
                .merge(&Subst::single(Tyvar::new("B", Star), Type::tcon("Bool")))
                .unwrap())
        );

        assert_eq!(
            matches(&Type::tcon("Int"), &Type::tvar("A", Star)),
            Err("types do not match".into())
        );
    }
}
