use crate::core::reference::Ref;
use std::ops::Deref;
use std::sync::atomic::{AtomicUsize, Ordering};

pub mod closure_conversion;
pub mod cps_eta_reduction;
pub mod cps_lang_to_c;
pub mod cps_uncurrying;
pub mod label_fixrefs;
mod labels_to_vars;
pub mod lambda_lifting;
pub mod limit_args;
pub mod make_all_names_unique;
pub mod mini_lambda_to_cps_lang;
pub mod register_allocation;
pub mod restrictions;
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
    use std::io::Write;
    use std::process::{Command, Stdio};
    use std::sync::Arc;
    use uuid::Uuid;

    use crate::core::answer::Answer;
    use crate::languages::cps_lang::ast as cps;
    use crate::languages::cps_lang::ast::Transform;
    use crate::languages::mini_lambda::ast as ml;
    use crate::make_testsuite_for_mini_lambda;
    use crate::transformations::labels_to_vars::LabelsToVars;
    use crate::transformations::restrictions::RestrictedAst;

    unsafe fn run_in_optimized_cps(
        mini_lambda_expr: &ml::Expr<Ref<str>>,
        out: &mut impl Write,
    ) -> Answer {
        let expr = mini_lambda_expr.clone();

        println!("Source:");
        println!("{}", expr.to_string());
        println!("\n");

        let cps_expr = Box::leak(Box::new(mini_lambda_to_cps_lang::Context::new(
            "__".to_string(),
        )))
        .convert(&expr, Box::new(|x| cps::Expr::Halt(x)));

        let cps = RestrictedAst::new(cps_expr);
        let cps = cps.rename_uniquely("__");
        let cps = cps.ensure_funcref_labels();

        println!("Initial CPS:");
        cps.expr().pretty_print();
        println!("\n");

        let cps = cps.eta_reduce();
        let cps = cps.uncurry();

        println!("η Reduced:");
        cps.clone().rename_uniquely("__").expr().pretty_print();
        println!("\n");

        let (cps_expr, gs) = cps.deconstruct();

        let n_registers = 5;
        let max_args = n_registers - 2; // reserve two registers for closure and continuation

        let cps_expr = limit_args::LimitArgs::new(max_args, gs.clone()).transform_expr(&cps_expr);

        let cps_expr = LabelsToVars.transform_expr(&cps_expr);

        let cps_expr = closure_conversion::Context::new(gs.clone()).convert_closures(&cps_expr);

        let cps_expr = lambda_lifting::lift_lambdas(&cps_expr);

        println!("Closure Conversion & Lambda Lifting:");
        make_all_names_unique::Context::new_context("__")
            .rename_all(&cps_expr)
            .pretty_print();
        println!("\n");

        // Spilling does not work for less than 3 registers in some tests. Not sure if there is a bug
        // or if it simply can't work with that few registers...
        let cps_expr =
            spill_phase::spill_toplevel(&cps_expr, n_registers, Arc::new(GensymContext::new("__")));

        // finally, get rid of multiple __ parts
        let cps_expr = make_all_names_unique::Context::new_context("__").rename_all(&cps_expr);
        println!("Final:");
        cps_expr.pretty_print();
        println!("\n");

        let cps_expr = register_allocation::allocate(n_registers, &cps_expr);
        println!("Registers:");
        cps_expr.pretty_print();
        println!("\n");

        let c_code = cps_lang_to_c::program_to_c(n_registers, &cps_expr).join("\n");

        println!("C:");
        println!("{}", c_code);
        println!("\n");

        let bin = compile_c(c_code);
        let result = String::from_utf8(Command::new(bin).output().unwrap().stdout).unwrap();
        let result = result.trim();
        write!(out, "{}", result).unwrap();

        //cps_lang::interpreter::exec(&cps_expr, out)
        Answer::from_usize(0)
    }

    fn compile_c(src: String) -> String {
        let binary = format!("/tmp/{}", Uuid::new_v4());
        let mut gcc = Command::new("gcc")
            .arg("-xc")
            .arg("-o")
            .arg(&binary)
            .arg("-")
            .stdin(Stdio::piped())
            .spawn()
            .unwrap();
        write!(gcc.stdin.as_mut().unwrap(), "{}", src).unwrap();
        let output = gcc.wait_with_output().unwrap();
        println!("{:?}", output);
        binary
    }

    make_testsuite_for_mini_lambda!(run_in_optimized_cps continuation_tests);
}
