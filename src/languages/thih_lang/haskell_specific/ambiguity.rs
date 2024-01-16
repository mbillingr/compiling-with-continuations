use super::super::thih_core::predicates::Pred;
use super::super::thih_core::substitutions::{Subst, Types};
use super::super::thih_core::types::{Type, Tyvar};
use super::classes::ClassEnv;
use crate::core::lists::eq_diff;
use crate::languages::thih_lang::{Id, Int, Result};

#[derive(Debug)]
pub struct Ambiguity(pub Tyvar, pub Vec<Pred>);

fn ambiguities(vs: Vec<Tyvar>, ps: &[Pred]) -> Vec<Ambiguity> {
    let mut out = vec![];
    for v in eq_diff(ps.tv(), vs) {
        let ps_ = ps.iter().filter(|p| p.tv().contains(&v)).cloned().collect();
        out.push(Ambiguity(v, ps_))
    }
    out
}

const NUM_CLASSES: [&str; 7] = [
    "Num",
    "Integral",
    "Floating",
    "Fractional",
    "Real",
    "RealFloat",
    "RealFrac",
];
const STD_CLASSES: [&str; 17] = [
    "Eq",
    "Ord",
    "Show",
    "Read",
    "Bounded",
    "Enum",
    "Ix",
    "Functor",
    "Monad",
    "MonadPlus",
    "Num",
    "Integral",
    "Floating",
    "Fractional",
    "Real",
    "RealFloat",
    "RealFrac",
];

fn candidates(ce: &ClassEnv, Ambiguity(v, qs): &Ambiguity) -> Vec<Type> {
    let is_ = || qs.iter().map(|Pred::IsIn(i, _)| i);
    let ts_: Vec<_> = qs.iter().map(|Pred::IsIn(_, t)| t).collect();

    if !ts_
        .into_iter()
        .all(|t| if let Type::TVar(u) = t { u == v } else { false })
    {
        return vec![];
    }

    if !is_().any(|i| NUM_CLASSES.contains(&i.as_str())) {
        return vec![];
    }

    if !is_().all(|i| STD_CLASSES.contains(&i.as_str())) {
        return vec![];
    }

    let mut out = vec![];
    for t_ in ce.defaults() {
        if is_()
            .map(|i| Pred::IsIn(i.clone(), t_.clone()))
            .all(|p| ce.entail(&[], &p))
        {
            out.push(t_.clone());
        }
    }

    out
}

fn with_defaults<T>(
    f: impl Fn(Vec<Ambiguity>, Vec<Type>) -> T,
    ce: &ClassEnv,
    vs: Vec<Tyvar>,
    ps: &[Pred],
) -> Result<T> {
    let vps = ambiguities(vs, ps);
    let tss = vps.iter().map(|vp| candidates(ce, vp));

    let mut heads = Vec::with_capacity(vps.len());
    for ts in tss {
        heads.push(
            ts.into_iter()
                .next()
                .ok_or_else(|| format!("cannot resolve ambiguity {vps:?}"))?,
        )
    }

    Ok(f(vps, heads))
}

pub fn defaulted_preds(ce: &ClassEnv, vs: Vec<Tyvar>, ps: &[Pred]) -> Result<Vec<Pred>> {
    with_defaults(
        |vps, _| vps.into_iter().map(|Ambiguity(_, p)| p).flatten().collect(),
        ce,
        vs,
        ps,
    )
}

pub fn default_subst(ce: &ClassEnv, vs: Vec<Tyvar>, ps: &[Pred]) -> Result<Subst> {
    with_defaults(
        |vps, ts| Subst::from_rev_iter(vps.into_iter().map(|Ambiguity(v, _)| v).zip(ts).rev()),
        ce,
        vs,
        ps,
    )
}
