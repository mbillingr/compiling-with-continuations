use crate::core::reference::Ref;
use std::ops::Deref;
use std::sync::atomic::{AtomicUsize, Ordering};

pub mod closure_conversion;
pub mod cps_eta_reduction;
pub mod label_fixrefs;
mod labels_to_vars;
pub mod lambda_lifting;
pub mod make_all_names_unique;
pub mod mini_lambda_to_cps_lang;
pub mod spill_phase;

#[derive(Debug)]
pub struct GensymContext {
    sym_ctr: AtomicUsize,
    sym_delim: String,
}

impl GensymContext {
    pub fn new(sym_delim: impl ToString) -> Self {
        GensymContext {
            sym_ctr: AtomicUsize::new(0),
            sym_delim: sym_delim.to_string(),
        }
    }

    fn gensym<V: GenSym>(&self, name: &str) -> V {
        let n = self.sym_ctr.fetch_add(1, Ordering::Relaxed);
        V::gensym(name, &self.sym_delim, n)
    }

    fn resetsym<V: GenSym>(&self, name: &str) -> V {
        let name = name.split(&self.sym_delim).next().unwrap();
        let n = self.sym_ctr.fetch_add(1, Ordering::Relaxed);
        V::gensym(name, &self.sym_delim, n)
    }
}

pub trait GenSym: Deref<Target = str> {
    fn gensym(name: &str, delim: &str, unique: impl std::fmt::Display) -> Self;
}

impl GenSym for Ref<str> {
    fn gensym(name: &str, delim: &str, unique: impl std::fmt::Display) -> Self {
        Ref::from(format!("{name}{}{}", delim, unique))
    }
}

impl GenSym for String {
    fn gensym(name: &str, delim: &str, unique: impl std::fmt::Display) -> Self {
        format!("{name}{}{}", delim, unique)
    }
}

impl GenSym for &'static str {
    fn gensym(name: &str, delim: &str, unique: impl std::fmt::Display) -> Self {
        Box::leak(format!("{name}{}{}", delim, unique).into_boxed_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    use crate::core::answer::Answer;
    use crate::languages::cps_lang;
    use crate::languages::cps_lang::ast as cps;
    use crate::languages::cps_lang::ast::Transform;
    use crate::languages::mini_lambda::ast as ml;
    use crate::make_testsuite_for_mini_lambda;
    use crate::transformations::labels_to_vars::LabelsToVars;
    use crate::transformations::spill_phase::Spill;

    unsafe fn run_in_optimized_cps(mini_lambda_expr: &ml::Expr<Ref<str>>) -> Answer {
        let expr = mini_lambda_expr.clone();

        let cps_expr = Box::leak(Box::new(mini_lambda_to_cps_lang::Context::new(
            "__".to_string(),
        )))
        .convert(&expr, Box::new(|x| cps::Expr::Halt(x)));

        let cps_expr = make_all_names_unique::Context::new_context("__").rename_all(&cps_expr);

        let cps_expr = label_fixrefs::Context::new().convert_labels(&cps_expr);

        cps_expr.pretty_print();
        println!("\n");

        let cps_expr = Box::leak(Box::new(cps_eta_reduction::Context::new("__".to_string())))
            .eta_reduce(&cps_expr);

        cps_expr.pretty_print();
        println!("\n");

        //let cps_expr = LabelsToVars.transform_expr(&cps_expr);

        let cps_expr = Box::leak(Box::new(closure_conversion::Context::new("__".to_string())))
            .convert_closures(&cps_expr);

        let cps_expr = make_all_names_unique::Context::new_context("__").rename_all(&cps_expr);
        cps_expr.pretty_print();
        println!("\n");

        let cps_expr = lambda_lifting::lift_lambdas(&cps_expr);

        // Spilling does not work for less than 3 registers in some tests. Not sure if there is a bug
        // or if it simply can't work with that few registers...
        let cps_expr =
            spill_phase::spill_toplevel(&cps_expr, 4, Arc::new(GensymContext::new("__")));

        // finally, get rid of multiple __ parts
        let cps_expr = make_all_names_unique::Context::new_context("__").rename_all(&cps_expr);
        cps_expr.pretty_print();
        println!("\n");

        cps_lang::interpreter::exec(&cps_expr)
    }

    make_testsuite_for_mini_lambda!(run_in_optimized_cps continuation_tests);
}
