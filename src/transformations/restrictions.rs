use crate::languages::cps_lang::ast::{Expr, Transform};
use crate::transformations::{GenSym, GensymContext};
use std::hash::Hash;
use std::ops::Deref;
use std::sync::Arc;

const DEFAULT_GENSYM_DELIMITER: &str = "__";

#[derive(Clone)]
pub struct RestrictedAst<V: 'static> {
    ast: Expr<V>,
    all_names_unique: bool,
    vars_refer_to_values_only: bool,
    labels_refer_to_funcs_only: bool,
    max_args: Option<usize>,
    gensym_context: Arc<GensymContext>,
}

impl<V> RestrictedAst<V> {
    pub fn new(ast: Expr<V>) -> Self {
        RestrictedAst {
            ast,
            all_names_unique: false,
            vars_refer_to_values_only: false,
            labels_refer_to_funcs_only: false,
            max_args: None,
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
            vars_refer_to_values_only: true,
            labels_refer_to_funcs_only: true,
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

    /// Ensure that no function takes mon than `max_args` arguments.
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
}
