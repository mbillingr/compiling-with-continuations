use crate::languages::cps_lang::ast::{Expr, Value};
use std::iter::once;

impl<V> Expr<V> {
    pub fn continuation_exprs(&self) -> Vec<&Expr<V>> {
        match self {
            Expr::Record(_, _, cnt)
            | Expr::Select(_, _, _, cnt)
            | Expr::Offset(_, _, _, cnt)
            | Expr::Fix(_, cnt) => vec![&**cnt],
            Expr::Switch(_, cnts) | Expr::PrimOp(_, _, _, cnts) => {
                cnts.iter().map(|cnt| &**cnt).collect()
            }
            Expr::App(_, _) | Expr::Halt(_) | Expr::Panic(_) => vec![],
        }
    }

    pub fn operands(&self) -> Vec<&Value<V>> {
        match self {
            Expr::Record(fields, _, _) => fields.iter().map(|(f, _)| f).collect(),
            Expr::Select(_, v, _, _) | Expr::Offset(_, v, _, _) => vec![v],
            Expr::App(f, args) => args.iter().chain(once(f)).collect(),
            Expr::Fix(_, _) => vec![],
            Expr::Switch(v, _) => vec![v],
            Expr::PrimOp(_, args, _, _) => args.iter().collect(),
            Expr::Halt(v) => vec![v],
            Expr::Panic(_) => vec![],
        }
    }

    pub fn operand_vars(&self) -> Vec<&V> {
        self.operands()
            .into_iter()
            .filter_map(|val| {
                if let Value::Var(v) = val {
                    Some(v)
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn bound_vars(&self) -> Vec<&V> {
        match self {
            Expr::Record(_, v, _) | Expr::Select(_, _, v, _) | Expr::Offset(_, _, v, _) => vec![v],
            Expr::App(_, _) | Expr::Fix(_, _) | Expr::Switch(_, _) => vec![],
            Expr::PrimOp(_, _, vs, _) => vs.iter().collect(),
            Expr::Halt(_) | Expr::Panic(_) => vec![],
        }
    }
}
