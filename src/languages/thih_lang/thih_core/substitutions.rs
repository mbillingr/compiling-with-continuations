/*!
Substitutions associate type variables with types.
!*/

use super::types::{Type, Tyvar};
use crate::core::lists::{eq_intersect, eq_union, List};
use crate::core::persistent::PersistentMap;
use crate::languages::thih_lang::{Id, Int, Result};

/// A substitution that associates type variables with types.
#[derive(Debug, PartialEq)]
pub struct Subst(SubstImpl);

/// Implementation of substitution as association list
#[derive(Clone, Debug, PartialEq)]
struct SubstImpl(PersistentMap<Tyvar, Type>);

impl Subst {
    pub fn null_subst() -> Self {
        Subst(SubstImpl::empty())
    }

    pub fn single(u: Tyvar, t: Type) -> Self {
        Subst(SubstImpl::empty().assoc(u, t))
    }

    pub fn from_rev_iter(it: impl IntoIterator<Item = (Tyvar, Type)>) -> Self {
        let mut out = SubstImpl::empty();

        for (u, t) in it {
            out = out.assoc(u, t);
        }

        Subst(out)
    }

    pub fn lookup(&self, u: &Tyvar) -> Option<&Type> {
        self.0.lookup(u)
    }

    /// like lookup but ignores kind
    pub fn lookup_by_name(&self, name: &Id) -> Option<&Type> {
        self.0.lookup_by_name(name)
    }

    pub fn apply<U, T: Types<U> + ?Sized>(&self, this: &T) -> U {
        this.apply_subst(self)
    }

    pub fn keys(&self) -> Vec<Tyvar> {
        self.0.keys()
    }

    /// @@ operator
    pub fn compose(&self, other: &Self) -> Self {
        return Subst(other.0.append_map(self.0.clone(), |t| self.apply(t)));
    }

    pub fn merge(&self, other: &Self) -> Result<Self> {
        let a = self.keys();
        let b = other.keys();
        for v in eq_intersect(a, b) {
            if self.apply(&Type::TVar(v.clone())) != other.apply(&Type::TVar(v)) {
                Err("merge fails")?
            }
        }

        Ok(Subst(self.0.append(other.0.clone())))
    }
}

impl SubstImpl {
    fn empty() -> Self {
        SubstImpl(PersistentMap::new())
    }

    pub fn keys(&self) -> Vec<Tyvar> {
        self.0.keys().cloned().collect()
    }

    fn assoc(self, v: Tyvar, t: Type) -> Self {
        SubstImpl(self.0.insert(v, t))
    }

    pub fn lookup(&self, u: &Tyvar) -> Option<&Type> {
        self.0.get(u)
    }

    /// like lookup but ignores kind
    pub fn lookup_by_name(&self, name: &Id) -> Option<&Type> {
        self.0
            .iter()
            .filter(|(tv, _)| &tv.0 == name)
            .map(|(_, ty)| ty)
            .next()
    }

    pub fn append(&self, other: Self) -> Self {
        self.append_map(other, Clone::clone)
    }

    pub fn append_map(&self, other: Self, f: impl Fn(&Type) -> Type) -> Self {
        SubstImpl(other.0.merge(&self.0.map(&|_, t| f(t))))
    }
}

/// Interface for applying substitutions to types and other things
pub trait Types<T: ?Sized = Self> {
    /// apply substitution
    fn apply_subst(&self, s: &Subst) -> T;

    /// get type vars
    fn tv(&self) -> Vec<Tyvar>;
}

impl Types for Type {
    fn apply_subst(&self, s: &Subst) -> Self {
        match self {
            Type::TVar(u) => match s.lookup(u) {
                Some(t) => t.clone(),
                None => Type::TVar(u.clone()),
            },
            Type::TApp(app) => Type::tapp(s.apply(&app.0), s.apply(&app.1)),
            _ => self.clone(),
        }
    }

    fn tv(&self) -> Vec<Tyvar> {
        match self {
            Type::TVar(u) => vec![u.clone()],
            Type::TApp(app) => eq_union(app.0.tv(), app.1.tv()),
            _ => vec![],
        }
    }
}

impl<T: Types> Types for Vec<T> {
    fn apply_subst(&self, s: &Subst) -> Self {
        self.iter().map(|x| s.apply(x)).collect()
    }

    fn tv(&self) -> Vec<Tyvar> {
        let mut tvs = vec![];
        for x in self {
            for u in x.tv() {
                if !tvs.contains(&u) {
                    tvs.push(u)
                }
            }
        }
        tvs
    }
}

impl<T: Types> Types<Vec<T>> for [T] {
    fn apply_subst(&self, s: &Subst) -> Vec<T> {
        self.iter().map(|x| s.apply(x)).collect()
    }

    fn tv(&self) -> Vec<Tyvar> {
        let mut tvs = vec![];
        for x in self {
            for u in x.tv() {
                if !tvs.contains(&u) {
                    tvs.push(u)
                }
            }
        }
        tvs
    }
}

impl<T: Types> Types for List<T> {
    fn apply_subst(&self, s: &Subst) -> Self {
        self.iter().map(|x| s.apply(x)).collect()
    }

    fn tv(&self) -> Vec<Tyvar> {
        let mut tvs = vec![];
        for x in self {
            for u in x.tv() {
                if !tvs.contains(&u) {
                    tvs.push(u)
                }
            }
        }
        tvs
    }
}

#[cfg(test)]
mod tests {
    use super::super::kinds::Kind;
    use super::*;

    #[test]
    fn lookup_in_subst() {
        let foo = Tyvar("foo".into(), Kind::Star);
        let bar = Tyvar("bar".into(), Kind::Star);

        let s = Subst::single(foo.clone(), Type::tcon("Int"));

        assert_eq!(s.lookup(&foo), Some(&Type::tcon("Int")));
        assert_eq!(s.lookup(&bar), None);
    }

    #[test]
    fn from_rev_iter_last_takes_precedence() {
        let foo = Tyvar("foo".into(), Kind::Star);
        let s = Subst::from_rev_iter(vec![
            (foo.clone(), Type::tcon("Int")),
            (foo.clone(), Type::tcon("Char")),
        ]);
        assert_eq!(s.lookup(&foo), Some(&Type::tcon("Char")));
    }

    #[test]
    fn composition() {
        let foo = Tyvar("foo".into(), Kind::Star);
        let tfoo = Type::TVar(foo.clone());
        let s1 = Subst::single(foo.clone(), Type::tcon("Int"));
        let bar = Tyvar("bar".into(), Kind::Star);
        let tbar = Type::TVar(bar.clone());
        let s2 = Subst::single(bar.clone(), tfoo);

        let s = Subst::compose(&s1, &s2);
        let app_s = s.apply(&tbar);

        let app_ref = s1.apply(&s2.apply(&tbar));

        assert_eq!(app_ref, Type::tcon("Int"));
        assert_eq!(app_s, app_ref);
        assert_eq!(app_s, Type::tcon("Int"));
    }

    #[test]
    fn composition_allows_access_to_vars_from_both() {
        let foo = Tyvar("foo".into(), Kind::Star);
        let s1 = Subst::single(foo.clone(), Type::tcon("Int"));
        let bar = Tyvar("bar".into(), Kind::Star);
        let s2 = Subst::single(bar.clone(), Type::tcon("Char"));

        let s = Subst::compose(&s1, &s2);

        assert_eq!(s.lookup(&foo), Some(&Type::tcon("Int")));
        assert_eq!(s.lookup(&bar), Some(&Type::tcon("Char")));
    }

    #[test]
    fn composition_second_takes_precedence() {
        let foo = Tyvar("foo".into(), Kind::Star);
        let s1 = Subst::single(foo.clone(), Type::tcon("Int"));
        let s2 = Subst::single(foo.clone(), Type::tcon("Char"));

        let s = Subst::compose(&s1, &s2);

        assert_eq!(s.lookup(&foo), Some(&Type::tcon("Char")));
    }

    #[test]
    fn merge_allows_access_to_vars_from_both() {
        let foo = Tyvar("foo".into(), Kind::Star);
        let s1 = Subst::single(foo.clone(), Type::tcon("Int"));
        let bar = Tyvar("bar".into(), Kind::Star);
        let s2 = Subst::single(bar.clone(), Type::tcon("Char"));

        let s = Subst::compose(&s1, &s2);

        assert_eq!(s.lookup(&foo), Some(&Type::tcon("Int")));
        assert_eq!(s.lookup(&bar), Some(&Type::tcon("Char")));
    }

    #[test]
    fn merge_substitions_must_agree() {
        let foo = Tyvar("foo".into(), Kind::Star);
        let s1 = Subst::single(foo.clone(), Type::tcon("Int"));
        let s2 = Subst::single(foo.clone(), Type::tcon("Char"));

        let s = Subst::merge(&s1, &s2);

        assert!(s.is_err());

        let foo = Tyvar("foo".into(), Kind::Star);
        let s1 = Subst::single(foo.clone(), Type::tcon("Int"));
        let s2 = Subst::single(foo.clone(), Type::tcon("Int"));

        let s = Subst::merge(&s1, &s2);

        assert!(s.is_ok());
    }
}
