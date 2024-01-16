use crate::core::lists::eq_diff;
use crate::languages::thih_lang::haskell_specific::inference::{
    Alt, BindGroup, Expl, Expr, Impl, Pat,
};
use crate::languages::thih_lang::thih_core::instantiate::Instantiate;
use crate::languages::thih_lang::thih_core::substitutions::Types;
use crate::languages::thih_lang::thih_core::types::Type;

impl Instantiate for Alt {
    fn inst(&self, ts: &[Type]) -> Self {
        Alt(self.0.inst(ts), self.1.inst(ts))
    }
}

impl Instantiate for Pat {
    fn inst(&self, _: &[Type]) -> Self {
        self.clone()
    }
}

impl Instantiate for Expr {
    fn inst(&self, ts: &[Type]) -> Self {
        match self {
            Expr::App(f, a) => Expr::App(f.inst(ts).into(), a.inst(ts).into()),
            Expr::Let(bg, x) => Expr::Let(bg.inst(ts), x.inst(ts).into()),
            Expr::Annotate(ty, x) => Expr::Annotate(ty.inst(ts), x.inst(ts).into()),
            _ => self.clone(),
        }
    }
}

impl Instantiate for BindGroup {
    fn inst(&self, ts: &[Type]) -> Self {
        BindGroup(self.0.inst(ts), self.1.inst(ts))
    }
}

impl Instantiate for Expl {
    fn inst(&self, ts: &[Type]) -> Self {
        todo!("I'm not sure how to determine which variables should be further inastiantiated and which not");
        let Expl(id, sc, alts) = self;

        let ts_ = eq_diff(
            ts.iter().cloned(),
            sc.tv().into_iter().map(Type::TVar).collect(),
        );

        Expl(id.clone(), sc.clone(), alts.inst(&ts_))
    }
}

impl Instantiate for Impl {
    fn inst(&self, ts: &[Type]) -> Self {
        todo!("I'm not sure how to determine which variables should be further inastiantiated and which not");
        let Impl(id, alts) = self;
        Impl(id.clone(), alts.inst(ts))
    }
}
