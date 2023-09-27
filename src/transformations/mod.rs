use crate::core::reference::Ref;
use std::sync::atomic::{AtomicUsize, Ordering};

pub mod cps_eta_reduction;
pub mod label_fixrefs;
pub mod mini_lambda_to_cps_lang;

pub struct GensymContext {
    sym_ctr: AtomicUsize,
    sym_delim: &'static str,
}

impl GensymContext {
    pub fn new(sym_delim: &'static str) -> Self {
        GensymContext {
            sym_ctr: AtomicUsize::new(0),
            sym_delim,
        }
    }

    fn gensym(&self, name: &str) -> Ref<str> {
        let n = self.sym_ctr.fetch_add(1, Ordering::Relaxed);
        Ref::from(format!("{name}{}{}", self.sym_delim, n))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::core::answer::Answer;
    use crate::languages::cps_lang;
    use crate::languages::cps_lang::ast as cps;
    use crate::languages::mini_lambda::ast as ml;
    use crate::{list, make_testsuite_for_mini_lambda};

    unsafe fn run_in_optimized_cps(mini_lambda_expr: &ml::Expr<Ref<str>>) -> Answer {
        let expr = mini_lambda_expr.clone();

        let cps_expr = Box::leak(Box::new(mini_lambda_to_cps_lang::Context::new("__"))).convert(
            &expr,
            Box::new(|x| cps::Expr::App(cps::Value::Halt, list![x])),
        );

        let cps_expr = label_fixrefs::Context::new().convert_labels(&cps_expr);

        println!("{:?}", cps_expr);

        let cps_expr =
            Box::leak(Box::new(cps_eta_reduction::Context::new("__"))).eta_reduce(&cps_expr);

        println!("{:?}", cps_expr);

        cps_lang::interpreter::exec(&cps_expr)
    }

    make_testsuite_for_mini_lambda!(run_in_optimized_cps continuation_tests);
}
