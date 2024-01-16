use super::instantiate::Instantiate;
use super::kinds::Kind;
use super::qualified::Qual;
use super::scheme::Scheme;
use super::substitutions::Subst;
use super::types::{Type, Tyvar};
use super::unification::mgu;
use crate::languages::thih_lang::{Id, Int, Result};

/// The type inference state
#[derive(Debug)]
pub struct TI {
    subst: Subst,
    count: Int,
}

impl TI {
    pub fn new() -> Self {
        TI {
            subst: Subst::null_subst(),
            count: 0,
        }
    }

    pub fn get_subst(&self) -> &Subst {
        &self.subst
    }

    pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<()> {
        let u = mgu(&self.subst.apply(t1), &self.subst.apply(t2))?;
        Ok(self.ext_subst(u))
    }

    pub fn new_tvar(&mut self, k: Kind) -> Type {
        let v = Tyvar(enum_id(self.count), k);
        self.count += 1;
        Type::TVar(v)
    }

    pub fn fresh_inst(&mut self, sc: &Scheme) -> Qual<Type> {
        match sc {
            Scheme::Forall(ks, qt) => {
                let ts: Vec<_> = ks.iter().map(|k| self.new_tvar(k.clone())).collect();
                qt.inst(&ts)
            }
        }
    }

    fn ext_subst(&mut self, s: Subst) {
        self.subst = s.compose(&self.subst); // todo: is the order of composition correct?
    }
}

fn enum_id(n: Int) -> Id {
    format!("v{n}")
}
