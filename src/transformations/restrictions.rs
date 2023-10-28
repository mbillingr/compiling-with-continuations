use crate::languages::cps_lang::ast::Expr;
use crate::transformations::{GenSym, GensymContext};
use std::hash::Hash;
use std::sync::Arc;

const DEFAULT_GENSYM_DELIMITER: &str = "__";

pub struct RestrictedAst<V: 'static> {
    ast: Expr<V>,
    all_names_unique: bool,
    gensym_context: Arc<GensymContext>,
}

impl<V> RestrictedAst<V> {
    pub fn new(ast: Expr<V>) -> Self {
        RestrictedAst {
            ast,
            all_names_unique: false,
            gensym_context: Arc::new(GensymContext::new(DEFAULT_GENSYM_DELIMITER)),
        }
    }

    pub fn rename_uniquely(&self, new_delimiter: impl ToString) -> Self
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
            ..*self
        }
    }
}
