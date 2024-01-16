use super::predicates::Pred;
use super::qualified::Qual;
use super::types::Type;
use crate::core::lists::List;

pub trait Instantiate {
    fn inst(&self, ts: &[Type]) -> Self;
}

impl Instantiate for Type {
    fn inst(&self, ts: &[Type]) -> Self {
        match self {
            Type::TApp(app) => Type::tapp(app.0.inst(ts), app.1.inst(ts)),
            Type::TGen(n) => ts[*n].clone(),
            t => t.clone(),
        }
    }
}

impl<T: Instantiate> Instantiate for Vec<T> {
    fn inst(&self, ts: &[Type]) -> Self {
        self.iter().map(|t| t.inst(ts)).collect()
    }
}

impl<T: Instantiate> Instantiate for List<T> {
    fn inst(&self, ts: &[Type]) -> Self {
        self.iter().map(|t| t.inst(ts)).collect()
    }
}

impl<T: Instantiate> Instantiate for Qual<T> {
    fn inst(&self, ts: &[Type]) -> Self {
        let t = &self.1;
        let t1 = &self.0;
        Qual(t1.inst(ts), t.inst(ts))
    }
}

impl Instantiate for Pred {
    fn inst(&self, ts: &[Type]) -> Self {
        match self {
            Pred::IsIn(c, t) => Pred::IsIn(c.clone(), t.inst(ts)),
        }
    }
}
