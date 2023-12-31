use crate::core::clicker::Clicker;
use crate::languages::cps_lang::ast::{Compute, Expr, Transform};
use crate::transformations::register_allocation::R;
use crate::transformations::{GenSym, GensymContext};
use std::borrow::Borrow;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::ops::Deref;
use std::sync::Arc;

const DEFAULT_GENSYM_DELIMITER: &str = "__";

#[derive(Clone)]
pub struct RestrictedAst<V: 'static, F: 'static> {
    ast: Expr<V, F>,
    all_names_unique: bool,
    no_dead_fns: bool,
    ref_usage: RefUsage,
    max_args: Option<usize>,
    explicit_closures: bool,
    toplevel_structure: bool,
    max_free_vars: Option<usize>,
    gensym_context: Arc<GensymContext>,
    pub clicker: Clicker,
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum RefUsage {
    Unknown,
    /// Value::Var refers to both, values and functions
    VarsOnly,
    /// Value::Var refers to values and Value::Label refers to functions
    LabelsAndVars,
}

impl<V, F> RestrictedAst<V, F> {
    pub fn new(ast: Expr<V, F>) -> Self {
        RestrictedAst {
            ast,
            all_names_unique: false,
            no_dead_fns: false,
            ref_usage: RefUsage::Unknown,
            max_args: None,
            explicit_closures: false,
            toplevel_structure: false,
            max_free_vars: None,
            gensym_context: Arc::new(GensymContext::new(DEFAULT_GENSYM_DELIMITER)),
            clicker: Default::default(),
        }
    }

    pub fn deconstruct(self) -> (Expr<V, F>, Arc<GensymContext>) {
        (self.ast, self.gensym_context)
    }

    pub fn expr(&self) -> &Expr<V, F> {
        &self.ast
    }
}

impl<V> RestrictedAst<V, V> {
    pub fn assert_all_names_unique(self) -> Self
    where
        V: Clone + Eq + Hash + Debug + Display,
    {
        let bindings = self.ast.check_all_bindings_unique();
        if !bindings.duplicates.is_empty() {
            panic!("Duplicate bindings {:?}", bindings.duplicates);
        }
        RestrictedAst {
            all_names_unique: true,
            ..self
        }
    }

    /// Make every name (variables, functions) unique.
    pub fn rename_uniquely(self, new_delimiter: impl ToString) -> Self
    where
        V: Debug + Display + Clone + Eq + Hash + GenSym,
    {
        let gensym_context = Arc::new(GensymContext::new(new_delimiter));
        let ast = super::make_all_names_unique::Context::new(gensym_context.clone())
            .rename_all(&self.ast);
        RestrictedAst {
            ast,
            gensym_context,
            all_names_unique: true,
            ..self
        }
    }

    /// Ensure that functions are referenced by Value::Label and values by Value::Var.
    pub fn analyze_refs(self) -> Self
    where
        V: Clone + Eq + Hash + GenSym,
    {
        let ast = super::label_fixrefs::Context::new().analyze_refs(&self.ast);
        RestrictedAst {
            ast,
            ref_usage: RefUsage::LabelsAndVars,
            ..self
        }
    }

    /// Use only Value::Var for both, values and functions
    pub fn reset_refs(self) -> Self
    where
        V: Clone + PartialEq,
    {
        let ast = super::labels_to_vars::LabelsToVars.transform_expr(&self.ast);
        RestrictedAst {
            ast,
            ref_usage: RefUsage::VarsOnly,
            ..self
        }
    }

    /// Remove unused functions
    pub fn purge_dead_functions(self) -> Self
    where
        V: Clone + Eq + Hash + Debug,
    {
        assert!(self.all_names_unique);
        assert_eq!(self.ref_usage, RefUsage::LabelsAndVars);
        let ast =
            super::dead_function_removal::purge_dead_functions(&self.ast, self.clicker.clone())
                .unwrap_or_else(|| self.ast.clone());
        RestrictedAst {
            ast,
            no_dead_fns: true,
            ..self
        }
    }

    /// Remove expressions whose results are not used
    pub fn eliminate_dead_code(self) -> Self
    where
        V: Clone + Eq + Hash + Debug,
    {
        let ast =
            super::dead_code_elimination::eliminate_dead_code(&self.ast, self.clicker.clone());
        RestrictedAst { ast, ..self }
    }

    /// Remove function definitions that trivially wrap another function.
    /// E.g. with `(define (foo x y) (bar x y))` every call to foo is replaced with a call to bar.
    pub fn eta_reduce(self) -> Self
    where
        V: Clone + Eq + Hash,
    {
        let ast = super::cps_eta_reduction::Context.transform_expr(&self.ast);
        RestrictedAst { ast, ..self }
    }

    /// Inverse eta reduction: wrap every function in another function.
    /// This is useful because we can optimize known calls to the function while it may escape.
    pub fn eta_split(self) -> Self
    where
        V: Clone + GenSym + Display,
    {
        let ast = super::cps_eta_splitting::Context::new(self.gensym_context.clone())
            .transform_expr(&self.ast);
        RestrictedAst { ast, ..self }
    }

    /// Perform an uncurrying step.
    pub fn uncurry(self) -> Self
    where
        V: Clone + PartialEq + Deref<Target = str> + GenSym + Display,
    {
        let ast =
            super::cps_uncurrying::Context::new(self.gensym_context.clone()).uncurry(&self.ast);
        RestrictedAst {
            ast,
            ref_usage: RefUsage::Unknown,
            ..self
        }
    }

    /// inline functions used only once.
    pub fn beta_contract(self) -> Self
    where
        V: Clone + Eq + Hash + PartialEq + Debug,
    {
        assert!(self.all_names_unique);
        assert_eq!(self.ref_usage, RefUsage::LabelsAndVars);
        assert!(self.no_dead_fns);
        let mut ast = self.ast;
        loop {
            ast = super::function_inlining::beta_contraction(&ast, self.clicker.clone());
            match super::dead_function_removal::purge_dead_functions(&ast, self.clicker.clone()) {
                Some(a) => ast = a,
                None => {
                    return RestrictedAst {
                        ast,
                        no_dead_fns: true,
                        ..self
                    }
                }
            }
        }
    }

    /// function inlining pass
    pub fn inline_functions(self) -> Self
    where
        V: Clone + Debug + Eq + Hash + PartialEq,
    {
        assert!(self.all_names_unique);
        assert_eq!(self.ref_usage, RefUsage::LabelsAndVars);
        let ast = super::function_inlining::heuristic_inline(&self.ast, self.clicker.clone());
        RestrictedAst {
            ast,
            all_names_unique: false, // inlining may introduce duplicate bindings inside function bodies
            no_dead_fns: false,      // inlining does not remove the definitions
            ..self
        }
    }

    /// Reduce various constant expressions
    pub fn fold_constants(self) -> Self
    where
        V: Clone + Debug + Eq + Hash + PartialOrd,
    {
        let ast =
            super::constant_folding::ConstantFolder::new(self.clicker.clone()).fold(&self.ast);
        RestrictedAst { ast, ..self }
    }

    /// Ensure that no function takes more than `max_args` arguments.
    pub fn limit_args(self, max_args: usize) -> Self
    where
        V: Clone + PartialEq + GenSym,
    {
        let ast = super::limit_args::LimitArgs::new(max_args, self.gensym_context.clone())
            .transform_expr(&self.ast);
        RestrictedAst {
            ast,
            max_args: Some(max_args),
            ..self
        }
    }

    /// Change all functions no accept their closure as an argument
    pub fn convert_closures(self) -> Self
    where
        V: Clone + Ord + Eq + Hash + GenSym + Debug + Display,
    {
        assert_eq!(self.ref_usage, RefUsage::VarsOnly);

        let ast = super::closure_conversion::Context::new(self.gensym_context.clone())
            .convert_closures(&self.ast);

        RestrictedAst {
            ast,
            max_args: self.max_args.map(|n| n + 1), // the closure becomes an extra argument
            ref_usage: RefUsage::LabelsAndVars, // the conversion uses Value::Label to put functions into closure records
            explicit_closures: true,
            ..self
        }
    }

    /// Change functions to take a closure argument if required
    pub fn convert_closures2(self) -> Self
    where
        V: Clone + Ord + Eq + Hash + GenSym + Debug + Display,
    {
        assert_eq!(self.ref_usage, RefUsage::LabelsAndVars);
        assert!(self.all_names_unique);
        assert!(self.max_args.is_some());
        let n = self.max_args.unwrap();

        let mut ctx =
            super::closure_conversion_advanced::Context::new(n, self.gensym_context.clone());
        ctx.compute_for_expr(&self.ast);
        let mut ctx = ctx.solve_closure_requirements();
        let ast = ctx.transform_expr(&self.ast);

        RestrictedAst {
            ast,
            max_args: self.max_args.map(|n| n + 1), // the closure becomes an extra argument
            explicit_closures: true,
            ..self
        }
    }

    /// Move all function definitions to the top level
    pub fn lift_lambdas(self) -> Self
    where
        V: Clone + Eq + Hash + Debug,
    {
        assert!(self.explicit_closures);

        let ast = super::lambda_lifting::lift_lambdas(&self.ast);

        RestrictedAst {
            ast,
            toplevel_structure: true,
            ..self
        }
    }

    /// Make sure the number of free variables never exceeds available registers
    pub fn spill(self, n_registers: usize) -> Self
    where
        V: Clone + Eq + Hash + Ord + GenSym + Debug + Display,
    {
        assert_eq!(self.ref_usage, RefUsage::LabelsAndVars);
        assert!(self.toplevel_structure);
        assert!(self.max_args.is_some());
        assert!(self.max_args.unwrap() <= n_registers);

        let ast =
            super::spill_phase::spill_toplevel(&self.ast, n_registers, self.gensym_context.clone());

        RestrictedAst {
            ast,
            max_free_vars: Some(n_registers),
            ..self
        }
    }

    /// Assign variables to registers
    pub fn allocate_registers(self) -> RestrictedAst<R, V>
    where
        V: Clone + Eq + Hash + Debug,
    {
        assert!(self.max_free_vars.is_some());
        let n_registers = self.max_free_vars.unwrap();

        let ast = super::register_allocation::allocate(n_registers, &self.ast);

        RestrictedAst {
            ast,
            all_names_unique: self.all_names_unique,
            no_dead_fns: self.no_dead_fns,
            explicit_closures: self.explicit_closures,
            max_args: self.max_args,
            max_free_vars: self.max_free_vars,
            ref_usage: self.ref_usage,
            toplevel_structure: self.toplevel_structure,
            gensym_context: self.gensym_context,
            clicker: Default::default(),
        }
    }
}

impl<V, F> RestrictedAst<V, F> {
    /// Generate Code for the abstract machine
    pub fn generate_linear_code(
        self,
        standard_arg_registers: [V; 3],
    ) -> Vec<super::cps_lang_to_abstract_machine::Op<V, F>>
    where
        V: Clone + PartialEq + Debug + Display,
        F: Clone + Eq + Hash + GenSym + Debug + Display,
    {
        let mut ctx = super::cps_lang_to_abstract_machine::Context::new(
            standard_arg_registers,
            self.gensym_context.clone(),
        );
        ctx.linearize_toplevel(&self.ast)
    }

    /// Generate C code
    pub fn generate_c_code(self) -> String
    where
        V: Clone + Debug + Display,
        F: Clone + Eq + Hash + Borrow<str> + Deref<Target = str> + Debug + Display,
    {
        assert!(self.max_free_vars.is_some());
        let n_registers = self.max_free_vars.unwrap();
        super::cps_lang_to_c::program_to_c(n_registers, &self.ast).join("\n")
    }
}
