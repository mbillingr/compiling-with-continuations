use crate::languages::cps_lang::ast::Expr;
use crate::transformations::{GenSym, GensymContext};
use std::hash::Hash;
use std::sync::Arc;

const DEFAULT_GENSYM_DELIMITER: &str = "__";

pub struct RestrictedAst<V: 'static> {
    ast: Expr<V>,
    all_names_unique: bool,
    funcs_referred_by_labels: bool,
    gensym_context: Arc<GensymContext>,
}

impl<V> RestrictedAst<V> {
    pub fn new(ast: Expr<V>) -> Self {
        RestrictedAst {
            ast,
            all_names_unique: false,
            funcs_referred_by_labels: false,
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

    pub fn ensure_funcref_labels(self) -> Self
    where
        V: Clone + Eq + Hash + GenSym,
    {
        let ast = super::label_fixrefs::Context::new().convert_labels(&self.ast);
        RestrictedAst {
            ast,
            funcs_referred_by_labels: true,
            ..self
        }
    }

    pub fn eta_reduce(self) -> Self
    where
        V: Clone + Eq + Hash,
    {
        let ast = super::cps_eta_reduction::Context.eta_reduce(&self.ast);
        RestrictedAst { ast, ..self }
    }
}
