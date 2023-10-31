use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Value};
use crate::transformations::{GenSym, GensymContext};
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::ops::Deref;
use std::sync::Arc;

/// Convert references to known functions from Var to Label

pub struct Context {
    gs: Arc<GensymContext>,
}

impl Context {
    pub fn new(gs: Arc<GensymContext>) -> Self {
        Context { gs }
    }
    pub fn new_context(sym_delim: impl ToString) -> Self {
        Context {
            gs: Arc::new(GensymContext::new(sym_delim)),
        }
    }

    pub fn rename_all<V: Debug + Display + Clone + Eq + Hash + GenSym + Deref<Target = str>>(
        &mut self,
        expr: &Expr<V>,
    ) -> Expr<V> {
        self.convert_exp(expr, &HashMap::new())
    }

    fn convert_exp<V: Debug + Display + Clone + Eq + Hash + GenSym + Deref<Target = str>>(
        &self,
        expr: &Expr<V>,
        bindings: &HashMap<V, V>,
    ) -> Expr<V> {
        match expr {
            Expr::Record(fields, r, cnt) => {
                let fields_out = fields
                    .iter()
                    .map(|(v, p)| (self.convert_val(v, bindings), p.clone()))
                    .collect();

                let (cnt_out, r_) = self.convert_with(cnt, &bindings, r);
                Expr::Record(Ref::array(fields_out), r_, cnt_out.into())
            }

            Expr::Select(idx, r, x, cnt) => {
                let r_out = self.convert_val(r, bindings);
                let (cnt_out, x_) = self.convert_with(cnt, &bindings, x);
                Expr::Select(*idx, r_out, x_, cnt_out.into())
            }

            Expr::Offset(idx, r, x, cnt) => {
                let r_out = self.convert_val(r, bindings);
                let (cnt_out, x_) = self.convert_with(cnt, &bindings, x);
                Expr::Offset(*idx, r_out, x_, cnt_out.into())
            }

            Expr::App(func, args) => Expr::App(
                self.convert_val(func, bindings),
                self.convert_vals(args, bindings),
            ),

            Expr::Fix(funcs, body) => {
                let mut bnd = bindings.clone();
                for (f, _, _) in funcs.iter() {
                    bnd.insert(f.clone(), self.gs.resetsym(f));
                }
                let mut funcs_out = vec![];
                for (f, p, fb) in funcs.iter() {
                    let mut locals = bnd.clone();
                    let mut params = vec![];
                    for p in p.iter() {
                        let newname: V = self.gs.resetsym(p);
                        locals.insert(p.clone(), newname.clone());
                        params.push(newname);
                    }
                    funcs_out.push((
                        bnd[f].clone(),
                        Ref::array(params),
                        self.convert_exp(fb, &locals).into(),
                    ));
                }
                Expr::Fix(Ref::array(funcs_out), self.convert_exp(body, &bnd).into())
            }

            Expr::Switch(val, arms) => {
                let val_out = self.convert_val(val, bindings);
                let arms_out = arms
                    .iter()
                    .map(|x| self.convert_exp(x, bindings).into())
                    .collect();
                Expr::Switch(val_out, Ref::array(arms_out))
            }

            Expr::PrimOp(op, args, ress, cnts) => {
                let args_out = self.convert_vals(args, bindings);
                let mut bindings = bindings.clone();
                let mut new_names = vec![];
                for r in ress.iter().cloned() {
                    let nn: V = self.gs.resetsym(&r);
                    bindings.insert(r, nn.clone());
                    new_names.push(nn);
                }
                let cnts_out = cnts
                    .iter()
                    .map(|c| self.convert_exp(c, &bindings).into())
                    .collect();
                Expr::PrimOp(*op, args_out, Ref::array(new_names), Ref::array(cnts_out))
            }

            Expr::Halt(v) => Expr::Halt(self.convert_val(v, bindings)),

            Expr::Panic(msg) => Expr::Panic(*msg),
        }
    }

    fn convert_with<V: Debug + Display + Clone + Eq + Hash + GenSym + Deref<Target = str>>(
        &self,
        expr: &Expr<V>,
        bindings: &HashMap<V, V>,
        name: &V,
    ) -> (Expr<V>, V) {
        let mut bindings = bindings.clone();
        let newname: V = self.gs.resetsym(name);
        bindings.insert(name.clone(), newname.clone());
        (self.convert_exp(expr, &bindings), newname)
    }

    fn convert_val<V: Debug + Display + Clone + Eq + Hash>(
        &self,
        val: &Value<V>,
        bindings: &HashMap<V, V>,
    ) -> Value<V> {
        match val {
            Value::Var(x) => Value::Var(
                bindings
                    .get(x)
                    .unwrap_or_else(|| panic!("unbound {x:?}"))
                    .clone(),
            ),
            Value::Label(x) => Value::Label(
                bindings
                    .get(x)
                    .unwrap_or_else(|| panic!("unbound {x:?}"))
                    .clone(),
            ),
            _ => val.clone(),
        }
    }

    fn convert_vals<V: Debug + Display + Clone + Eq + Hash>(
        &self,
        vals: &[Value<V>],
        bindings: &HashMap<V, V>,
    ) -> Ref<[Value<V>]> {
        Ref::array(
            vals.into_iter()
                .map(|v| self.convert_val(v, bindings))
                .collect(),
        )
    }
}
