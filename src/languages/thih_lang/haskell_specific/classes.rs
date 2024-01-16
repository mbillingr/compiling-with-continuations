use super::super::thih_core::predicates::{match_pred, mgu_pred, Pred};
use super::super::thih_core::qualified::Qual;
use super::super::thih_core::types::Type;
use crate::core::lists::List;
use crate::languages::thih_lang::haskell_specific::types;
use crate::languages::thih_lang::{Id, Result};
use crate::list;
use std::rc::Rc;

/// A Type class (Interface) contains a list of super classes and a list of instances.
#[derive(Debug, Clone)]
struct Class(Rc<Vec<Id>>, List<Inst>);

/// An instance is a type that implements a certain class (interface)
pub type Inst = Qual<Pred>;

/// The class environment captures information about defined classes and instances
/// in a given program.
pub struct ClassEnv {
    classes: Rc<dyn Fn(&Id) -> Result<Class>>,
    defaults: List<Type>,
}

impl Default for ClassEnv {
    fn default() -> Self {
        ClassEnv {
            classes: Rc::new(|i| Err(format!("class {i} not defined"))?),
            defaults: list![types::t_int(), types::t_double()],
        }
    }
}

impl ClassEnv {
    /// get super classes for a defined class
    pub fn supers(&self, name: &Id) -> Rc<Vec<Id>> {
        (self.classes)(name).unwrap().0
    }

    /// get instances for a defined class
    pub fn insts(&self, name: &Id) -> List<Inst> {
        (self.classes)(name).unwrap().1
    }

    /// iterate over defaultable types
    pub fn defaults(&self) -> impl Iterator<Item = &Type> {
        self.defaults.iter()
    }

    /// test if a class is defined
    pub fn is_defined(&self, name: &Id) -> bool {
        (self.classes)(name).is_ok()
    }

    /// add a new or updated class definition
    fn modify(&self, name: Id, cls: Class) -> Self {
        let next = self.classes.clone();
        ClassEnv {
            classes: Rc::new(move |j| if j == &name { Ok(cls.clone()) } else { next(j) }),
            defaults: self.defaults.clone(),
        }
    }

    pub fn by_super(&self, p: Pred) -> List<Pred> {
        match &p {
            Pred::IsIn(i, t) => List::concat(
                self.supers(i)
                    .iter()
                    .map(|i_| self.by_super(Pred::IsIn(i_.clone(), t.clone()))),
            )
            .cons(p),
        }
    }

    pub fn by_inst(&self, p: &Pred) -> Result<List<Pred>> {
        match p {
            Pred::IsIn(i, _) => self
                .insts(i)
                .iter()
                .map(|Qual(ps, h)| {
                    let u = match_pred(h, p)?;
                    Ok(ps.iter().map(|p_| u.apply(p_)).collect())
                })
                .filter(Result::is_ok)
                .map(Result::unwrap)
                .next()
                .ok_or_else(|| "no matching instance".to_string()),
        }
    }

    pub fn entail(&self, ps: &[Pred], p: &Pred) -> bool {
        ps.iter()
            .cloned()
            .map(|p_| self.by_super(p_))
            .any(|sup| sup.contains(p))
            || match self.by_inst(p) {
                Err(_) => false,
                Ok(qs) => qs.iter().all(|_| self.entail(ps, p)),
            }
    }

    pub fn to_hnfs<'a>(&self, ps: impl IntoIterator<Item = &'a Pred>) -> Result<Vec<Pred>> {
        let tmp: Result<Vec<_>> = ps.into_iter().map(|p| self.to_hnf(&p)).collect();
        Ok(tmp?.into_iter().flatten().collect())
    }

    pub fn to_hnf(&self, p: &Pred) -> Result<Vec<Pred>> {
        if p.in_hnf() {
            Ok(vec![p.clone()])
        } else {
            match self.by_inst(p) {
                Err(e) => Err(format!("context reduction ({e}): {p:?}"))?,
                Ok(ps) => self.to_hnfs(&ps),
            }
        }
    }

    pub fn simplify(&self, mut ps: Vec<Pred>) -> Vec<Pred> {
        let mut rs = vec![];

        while let Some(p) = ps.pop() {
            let mut rsps = rs.clone();
            rsps.extend(ps.clone());
            if !self.entail(&rsps, &p) {
                rs.push(p)
            }
        }

        rs
    }

    pub fn reduce(&self, ps: &[Pred]) -> Result<Vec<Pred>> {
        let qs = self.to_hnfs(ps)?;
        Ok(self.simplify(qs))
    }
}

pub struct EnvTransformer(Rc<dyn Fn(&ClassEnv) -> Result<ClassEnv>>);

impl EnvTransformer {
    pub fn apply(&self, ce: &ClassEnv) -> Result<ClassEnv> {
        self.0(ce)
    }

    pub fn compose(self, other: Self) -> Self {
        EnvTransformer(Rc::new(move |ce| {
            let ce_ = self.0(ce)?;
            other.0(&ce_)
        }))
    }

    pub fn add_class(i: Id, sis: Vec<Id>) -> Self {
        let sis = Rc::new(sis);
        EnvTransformer(Rc::new(move |ce| {
            if ce.is_defined(&i) {
                Err("class {i} already defined")?
            }
            for j in sis.iter() {
                if !ce.is_defined(j) {
                    Err("superclass {j} not defined")?
                }
            }
            Ok(ce.modify(i.clone(), Class(sis.clone(), list![])))
        }))
    }

    pub fn add_inst(ps: Vec<Pred>, p: Pred) -> Self {
        EnvTransformer(Rc::new(move |ce| match &p {
            Pred::IsIn(i, _) => {
                if !ce.is_defined(&i) {
                    Err("no class for instance")?
                }
                let its = ce.insts(&i);
                let mut qs = its.iter().map(|Qual(_, q)| q);
                if qs.any(|q| overlap(&p, q)) {
                    Err("overlapping instance")?
                }
                let c = Class(ce.supers(i), its.cons(Qual(ps.clone(), p.clone())));
                Ok(ce.modify(i.clone(), c))
            }
        }))
    }
}

fn overlap(p: &Pred, q: &Pred) -> bool {
    mgu_pred(p, q).is_ok()
}
