use crate::core::reference::Ref;
use std::sync::atomic::{AtomicUsize, Ordering};

pub mod cps_eta_reduction;
pub mod mini_lambda_to_cps_lang;

pub struct Context {
    sym_ctr: AtomicUsize,
    sym_delim: &'static str,
}

impl Context {
    pub fn new(sym_delim: &'static str) -> Self {
        Context {
            sym_ctr: AtomicUsize::new(0),
            sym_delim,
        }
    }

    fn gensym(&self, name: &str) -> Ref<str> {
        let n = self.sym_ctr.fetch_add(1, Ordering::Relaxed);
        Ref::from(format!("{name}{}{}", self.sym_delim, n))
    }
}
