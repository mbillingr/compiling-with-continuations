use crate::languages::cps_lang::ast::Expr;
use std::collections::HashSet;
use std::hash::Hash;

impl<V: Clone + PartialEq + Eq + Hash + std::fmt::Debug> Expr<V> {
    pub fn check_all_bindings_unique(&self) -> Bindings<V> {
        match self {
            Expr::Record(_, var, cnt)
            | Expr::Select(_, _, var, cnt)
            | Expr::Offset(_, _, var, cnt) => cnt.check_all_bindings_unique().add(var),

            Expr::Fix(defs, cnt) => {
                let mut bindings = cnt.check_all_bindings_unique();
                for (f, p, b) in defs.iter() {
                    bindings = bindings.add(f);
                    bindings = bindings.add_more(p);
                    bindings = bindings.merge(b.check_all_bindings_unique());
                }
                bindings
            }

            Expr::Switch(_, cnts) => cnts
                .iter()
                .map(|c| c.check_all_bindings_unique())
                .reduce(Bindings::merge)
                .unwrap_or(Default::default()),

            Expr::PrimOp(_, _, vars, cnts) => cnts
                .iter()
                .map(|c| c.check_all_bindings_unique())
                .reduce(Bindings::merge)
                .unwrap_or(Default::default())
                .add_more(vars),

            Expr::App(_, _) | Expr::Halt(_) | Expr::Panic(_) => Default::default(),
        }
    }
}

pub struct Bindings<V> {
    pub all_bindings: HashSet<V>,
    pub duplicates: HashSet<V>,
}

impl<V> Default for Bindings<V> {
    fn default() -> Self {
        Bindings {
            all_bindings: Default::default(),
            duplicates: Default::default(),
        }
    }
}

impl<V: Clone + Eq + Hash> Bindings<V> {
    fn add(mut self, var: &V) -> Self {
        if self.all_bindings.contains(var) {
            self.duplicates.insert(var.clone());
        } else {
            self.all_bindings.insert(var.clone());
        }
        self
    }

    pub fn add_more(self, vars: &[V]) -> Self {
        vars.iter().fold(self, |b, v| b.add(v))
    }

    pub fn merge(mut self, other: Self) -> Self {
        self.duplicates
            .extend(self.all_bindings.intersection(&other.all_bindings).cloned());
        self.duplicates.extend(other.duplicates);
        self.all_bindings.extend(other.all_bindings);
        self
    }
}
