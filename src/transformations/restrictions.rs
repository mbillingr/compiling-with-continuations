use crate::languages::cps_lang::ast::{Expr, Transform};
use crate::transformations::{GenSym, GensymContext};
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::Deref;
use std::sync::Arc;

const DEFAULT_GENSYM_DELIMITER: &str = "__";

#[derive(Clone)]
pub struct RestrictedAst<V: 'static> {
    ast: Expr<V>,
    all_names_unique: bool,
    ref_usage: RefUsage,
    max_args: Option<usize>,
    explicit_closures: bool,
    toplevel_structure: bool,
    max_free_vars: Option<usize>,
    gensym_context: Arc<GensymContext>,
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum RefUsage {
    Unknown,
    /// Value::Var refers to both, values and functions
    VarsOnly,
    /// Value::Var refers to values and Value::Label refers to functions
    LabelsAndVars,
}

impl<V> RestrictedAst<V> {
    pub fn new(ast: Expr<V>) -> Self {
        RestrictedAst {
            ast,
            all_names_unique: false,
            ref_usage: RefUsage::Unknown,
            max_args: None,
            explicit_closures: false,
            toplevel_structure: false,
            max_free_vars: None,
            gensym_context: Arc::new(GensymContext::new(DEFAULT_GENSYM_DELIMITER)),
        }
    }

    pub fn deconstruct(self) -> (Expr<V>, Arc<GensymContext>) {
        (self.ast, self.gensym_context)
    }

    pub fn expr(&self) -> &Expr<V> {
        &self.ast
    }

    pub fn assert_all_names_unique(self) -> Self
    where
        V: Clone + Eq + Hash + std::fmt::Debug,
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
        V: std::fmt::Debug + Clone + Eq + Hash + GenSym,
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

    /// Remove function definitions that trivially wrap another function.
    /// E.g. with `(define (foo x y) (bar x y))` every call to foo is replaced with a call to bar.
    pub fn eta_reduce(self) -> Self
    where
        V: Clone + Eq + Hash,
    {
        let ast = super::cps_eta_reduction::Context.eta_reduce(&self.ast);
        RestrictedAst { ast, ..self }
    }

    /// Perform an uncurrying step.
    pub fn uncurry(self) -> Self
    where
        V: Clone + PartialEq + Deref<Target = str> + GenSym,
    {
        let ast =
            super::cps_uncurrying::Context::new(self.gensym_context.clone()).uncurry(&self.ast);
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
        V: Clone + Ord + Eq + Hash + GenSym + Debug,
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
        V: Clone + Eq + Hash + Ord + GenSym + Debug,
    {
        assert!(self.toplevel_structure);

        let ast =
            super::spill_phase::spill_toplevel(&self.ast, n_registers, self.gensym_context.clone());

        RestrictedAst {
            ast,
            max_free_vars: Some(n_registers),
            ..self
        }
    }
}
