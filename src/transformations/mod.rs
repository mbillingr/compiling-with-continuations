use crate::core::reference::Ref;
use std::fmt::Display;
use std::ops::Deref;
use std::sync::atomic::{AtomicUsize, Ordering};

pub mod closure_conversion;
pub mod closure_conversion_advanced;
pub mod constant_folding;
pub mod cps_eta_reduction;
pub mod cps_eta_splitting;
pub mod cps_lang_to_abstract_machine;
pub mod cps_lang_to_c;
pub mod cps_uncurrying;
pub mod dead_function_removal;
pub mod function_inlining;
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

    fn gensym<V: GenSym>(&self, name: impl Display) -> V {
        let n = self.sym_ctr.fetch_add(1, Ordering::Relaxed);
        V::gensym(name, &self.sym_delim, n)
    }

    fn resetsym<V: GenSym>(&self, name: impl Display) -> V {
        let name = name.to_string();
        let name = name.split(&self.sym_delim).next().unwrap();
        let n = self.sym_ctr.fetch_add(1, Ordering::Relaxed);
        V::gensym(name, &self.sym_delim, n)
    }

    fn gensym2<V: GenSym>(&self, prefix: impl Display, suffix: impl Display) -> V {
        let n = self.sym_ctr.fetch_add(1, Ordering::Relaxed);
        V::gensym2(prefix, &self.sym_delim, n, suffix)
    }
}

pub trait GenSym: Deref<Target = str> {
    fn gensym(name: impl Display, delim: impl Display, unique: impl Display) -> Self;
    fn gensym2(
        name: impl Display,
        delim: impl Display,
        unique: impl Display,
        suffix: impl Display,
    ) -> Self;
}

impl GenSym for Ref<str> {
    fn gensym(name: impl Display, delim: impl Display, unique: impl Display) -> Self {
        Ref::from(format!("{name}{}{}", delim, unique))
    }
    fn gensym2(
        name: impl Display,
        delim: impl Display,
        unique: impl Display,
        suffix: impl Display,
    ) -> Self {
        Ref::from(format!("{name}{delim}{unique}{delim}{suffix}"))
    }
}

impl GenSym for String {
    fn gensym(name: impl Display, delim: impl Display, unique: impl Display) -> Self {
        format!("{name}{}{}", delim, unique)
    }
    fn gensym2(
        name: impl Display,
        delim: impl Display,
        unique: impl Display,
        suffix: impl Display,
    ) -> Self {
        format!("{name}{delim}{unique}{delim}{suffix}")
    }
}

impl GenSym for &'static str {
    fn gensym(name: impl Display, delim: impl Display, unique: impl Display) -> Self {
        Box::leak(format!("{name}{}{}", delim, unique).into_boxed_str())
    }
    fn gensym2(
        name: impl Display,
        delim: impl Display,
        unique: impl Display,
        suffix: impl Display,
    ) -> Self {
        Box::leak(format!("{name}{delim}{unique}{delim}{suffix}").into_boxed_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use std::process::{Command, Stdio};
    use uuid::Uuid;

    use crate::core::answer::Answer;
    use crate::languages::cps_lang::ast as cps;
    use crate::languages::mini_lambda::ast as ml;
    use crate::make_testsuite_for_mini_lambda;
    use crate::transformations::cps_lang_to_abstract_machine::Op;
    use crate::transformations::register_allocation::R;
    use crate::transformations::restrictions::RestrictedAst;

    unsafe fn run_in_unoptimized_cps(
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

        println!("Initial CPS:");
        cps.expr().pretty_print();
        println!("\n");

        let n_registers = 5;
        let max_args = n_registers - 1; // reserve one more register for the closure

        let cps = cps.limit_args(max_args);
        //let cps = cps.analyze_refs();
        //let cps = cps.convert_closures2();
        let cps = cps.reset_refs();
        let cps = cps.convert_closures();
        println!("DBG:");
        cps.expr().pretty_print();
        println!("\n");
        let cps = cps.lift_lambdas();

        println!("Closure Conversion & Lambda Lifting:");
        cps.clone().rename_uniquely("__").expr().pretty_print();
        println!("\n");

        let cps = cps.spill(n_registers);

        let cps = cps.rename_uniquely("__");

        println!("Final:");
        cps.expr().pretty_print();
        println!("\n");

        /*let (cps_expr, _) = cps.deconstruct();
        //return crate::languages::cps_lang::interpreter::exec(&cps_expr, out);
        crate::languages::cps_lang::safe_interpreter::exec(&cps_expr, out);
        return Answer::from_usize(0);*/

        let cps = cps.allocate_registers();

        println!("Registers:");
        cps.expr().pretty_print();
        println!("\n");

        /*let (cps_expr, _) = cps.deconstruct();
        //return crate::languages::cps_lang::interpreter::exec(&cps_expr, out);
        crate::languages::cps_lang::safe_interpreter::exec(&cps_expr, out);
        return Answer::from_usize(0);*/

        let byte_code = cps.clone().generate_linear_code([R(0), R(1), R(2)]);

        println!("Linear:");
        for op in byte_code {
            match op {
                Op::Label(l) => println!("{l}:"),
                _ => println!("  {op:?}"),
            }
        }
        println!("\n");

        let c_code = cps.clone().generate_c_code();

        println!("C:");
        println!("{}", c_code);
        println!("\n");

        let bin = compile_c(c_code);
        let result = String::from_utf8(Command::new(bin).output().unwrap().stdout).unwrap();
        let result = result.trim();
        write!(out, "{}", result).unwrap();
        Answer::from_usize(0)
    }

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

        println!("Initial CPS:");
        cps.expr().pretty_print();
        println!("\n");

        let cps = cps.eta_reduce();
        let cps = cps.uncurry();
        let cps = cps.analyze_refs();

        println!("η Reduced:");
        cps.clone().rename_uniquely("__").expr().pretty_print();
        println!("\n");

        let cps = cps.purge_dead_functions();
        let cps = cps.beta_contract();

        let mut cps = cps;
        for _ in 0..10 {
            cps = cps.inline_functions();
            cps = cps.rename_uniquely("__");
            cps = cps.purge_dead_functions();
            cps = cps.analyze_refs();
            cps = cps.fold_constants();
        }

        let cps = cps.purge_dead_functions();
        let cps = cps.beta_contract();
        let cps = cps.fold_constants();

        let cps = cps.rename_uniquely("__");

        println!("More reductions:");
        cps.clone().rename_uniquely("__").expr().pretty_print();
        println!("\n");

        let n_registers = 5;
        let max_args = n_registers - 1; // reserve one more register for the closure

        let cps = cps.limit_args(max_args);
        let cps = cps.convert_closures2();
        let cps = cps.lift_lambdas();

        println!("Closure Conversion & Lambda Lifting:");
        cps.clone().rename_uniquely("__").expr().pretty_print();
        println!("\n");

        let cps = cps.spill(n_registers);

        let cps = cps.rename_uniquely("__");

        println!("Final:");
        cps.expr().pretty_print();
        println!("\n");

        /*let (cps_expr, _) = cps.deconstruct();
        //return crate::languages::cps_lang::interpreter::exec(&cps_expr, out);
        crate::languages::cps_lang::safe_interpreter::exec(&cps_expr, out);
        return Answer::from_usize(0);*/

        let cps = cps.allocate_registers();

        println!("Registers:");
        cps.expr().pretty_print();
        println!("\n");

        /*let (cps_expr, _) = cps.deconstruct();
        //return crate::languages::cps_lang::interpreter::exec(&cps_expr, out);
        crate::languages::cps_lang::safe_interpreter::exec(&cps_expr, out);
        return Answer::from_usize(0);*/

        let byte_code = cps.clone().generate_linear_code([R(0), R(1), R(2)]);

        println!("Linear:");
        for op in byte_code {
            match op {
                Op::Label(l) => println!("{l}:"),
                _ => println!("  {op:?}"),
            }
        }
        println!("\n");

        let c_code = cps.clone().generate_c_code();

        println!("C:");
        println!("{}", c_code);
        println!("\n");

        let bin = compile_c(c_code);
        let result = String::from_utf8(Command::new(bin).output().unwrap().stdout).unwrap();
        let result = result.trim();
        write!(out, "{}", result).unwrap();
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

    mod unpotimized {
        use super::*;
        make_testsuite_for_mini_lambda!(run_in_unoptimized_cps continuation_tests);
    }

    mod optimized {
        use super::*;
        make_testsuite_for_mini_lambda!(run_in_optimized_cps continuation_tests);
    }
}
