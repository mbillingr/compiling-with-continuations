use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{AccessPath, Expr, Value};
use crate::transformations::{GenSym, GensymContext};
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::Deref;
use std::sync::Arc;

const CLS_FUNC_INDEX: isize = 0;

pub struct Context {
    pub gs: Arc<GensymContext>,
}

impl Context {
    pub fn new(gs: Arc<GensymContext>) -> Self {
        Context { gs }
    }
    pub fn new_context(sym_delim: String) -> Self {
        Context {
            gs: Arc::new(GensymContext::new(sym_delim)),
        }
    }
}

impl Context {
    pub fn convert_closures<V: Clone + Ord + Eq + Hash + GenSym + Debug>(
        &self,
        exp: &Expr<V>,
    ) -> Expr<V> {
        self.convert_closures_(exp, &KnownFunctions::new())
    }
    fn convert_closures_<V: Clone + Ord + Eq + Hash + GenSym + Debug>(
        &self,
        exp: &Expr<V>,
        known_functions: &KnownFunctions<V>,
    ) -> Expr<V> {
        match exp {
            Expr::Record(fields, r, cnt) => Expr::Record(
                *fields,
                r.clone(),
                self.convert_closures_(cnt, &known_functions.drop(r)).into(),
            ),

            Expr::Select(idx, r, x, cnt) => Expr::Select(
                *idx,
                r.clone(),
                x.clone(),
                self.convert_closures_(cnt, &known_functions.drop(x)).into(),
            ),

            Expr::Offset(idx, r, x, cnt) => Expr::Offset(
                *idx,
                r.clone(),
                x.clone(),
                self.convert_closures_(cnt, &known_functions.drop(x)).into(),
            ),

            Expr::App(Value::Var(r) | Value::Label(r), rands) => {
                let mut rands_out = vec![Value::Var(r.clone())];
                rands_out.extend(rands.iter().cloned());

                if let Some(renamed) = known_functions.known_as(r) {
                    Expr::App(Value::Label(renamed), Ref::array(rands_out)).into()
                } else {
                    let f: V = self.gs.gensym("f");
                    Expr::Select(
                        CLS_FUNC_INDEX,
                        Value::Var(r.clone()),
                        f.clone(),
                        Expr::App(Value::Var(f), Ref::array(rands_out)).into(),
                    )
                }
            }

            Expr::App(rator, _) => panic!("invalid operator: {:?}", rator),

            Expr::Fix(defs, body) => {
                let cls_arg: V = self.gs.gensym("cls");

                let mut closure = Closure::new(&self.gs);
                for (f, _, _) in defs.iter() {
                    closure.add_function(f);
                }
                for v in exp.fix_function_free_vars().iter() {
                    closure.add_var(v);
                }

                let known_functions = known_functions.extend(closure.aliases());

                let defs_out: Vec<_> = defs
                    .iter()
                    .map(|(f, p, b)| {
                        let mut fbody = self.convert_closures_(b, &known_functions);
                        let mut f_free: Vec<_> =
                            Expr::function_free_vars(p, b).into_iter().collect();
                        f_free.sort_unstable();
                        for v in f_free {
                            fbody = closure.build_lookup(v, f, Value::Var(f.clone()), fbody);
                        }
                        (
                            closure.get_new_func_name(f),
                            p.prepend(f.clone()),
                            fbody.into(),
                        )
                    })
                    .collect();

                let mut body = Ref::new(self.convert_closures_(body, &known_functions));
                for (f, _, _) in defs.iter() {
                    let idx = closure.get_func_idx(f).unwrap();
                    body = Ref::new(Expr::Offset(
                        idx,
                        Value::Var(cls_arg.clone()),
                        f.clone(),
                        body,
                    ));
                }

                let mut cls_fields = vec![];
                for f in closure.renamed_funcs {
                    cls_fields.push((Value::Label(f), AccessPath::Ref(0)));
                }
                for v in closure.vars {
                    cls_fields.push((Value::Var(v), AccessPath::Ref(0)));
                }
                let body_out = Ref::new(Expr::Record(Ref::array(cls_fields), cls_arg, body.into()));

                Expr::Fix(Ref::array(defs_out), body_out)
            }

            Expr::Switch(v, arms) => Expr::Switch(
                v.clone(),
                Ref::array(
                    arms.iter()
                        .map(|x| self.convert_closures_(x, known_functions).into())
                        .collect(),
                ),
            ),

            Expr::PrimOp(op, args, res, cnts) => Expr::PrimOp(*op, *args, *res, {
                let known_functions = known_functions.drop_some(res.iter());
                Ref::array(
                    cnts.iter()
                        .map(|c| self.convert_closures_(c, &known_functions).into())
                        .collect(),
                )
            }),

            Expr::Halt(v) => Expr::Halt(v.clone()),

            Expr::Panic(msg) => Expr::Panic(*msg),
        }
    }
}

#[derive(Debug)]
struct Closure<'a, V> {
    gs: &'a GensymContext,
    funcs: Vec<V>,
    renamed_funcs: Vec<V>,
    vars: Vec<V>,
}

impl<'a, V: Clone + Deref<Target = str> + GenSym + Debug> Closure<'a, V> {
    fn new(gs: &'a GensymContext) -> Self {
        Closure {
            gs,
            funcs: vec![],
            renamed_funcs: vec![],
            vars: vec![],
        }
    }

    fn add_function(&mut self, name: &V) {
        self.renamed_funcs.push(self.gs.gensym(name));
        self.funcs.push(name.clone());
    }

    fn add_var(&mut self, name: &V) {
        self.vars.push(name.clone())
    }

    fn get_new_func_name(&self, name: &str) -> V {
        let idx = self.get_func_idx(name).unwrap();
        self.renamed_funcs[idx as usize].clone()
    }

    fn get_var_idx(&self, name: &str, current_fn: &str) -> Option<isize> {
        let offset = self.funcs.len() as isize;
        self.vars
            .iter()
            .enumerate()
            .find(|(_, v)| &***v == name)
            .map(|(i, _)| i as isize)
            .and_then(|i| self.get_func_idx(current_fn).map(|j| offset - j + i))
    }

    fn get_func_idx(&self, name: &str) -> Option<isize> {
        self.funcs
            .iter()
            .enumerate()
            .find(|(_, f)| &***f == name)
            .map(|(i, _)| i as isize)
    }

    fn build_lookup(&self, name: V, current_fn: &str, cls_val: Value<V>, cnt: Expr<V>) -> Expr<V> {
        if &*name == current_fn {
            return cnt;
        }

        if let Some(idx) = self.get_func_idx(&name) {
            let rel = idx - self.get_func_idx(current_fn).unwrap();
            return Expr::Offset(rel, cls_val, name, cnt.into());
        }

        if let Some(idx) = self.get_var_idx(&name, current_fn) {
            return Expr::Select(idx, cls_val, name, cnt.into());
        }

        panic!("{:?}", name);
    }

    fn aliases(&self) -> impl Iterator<Item = (V, V)> + '_ {
        self.funcs
            .iter()
            .cloned()
            .zip(self.renamed_funcs.iter().cloned())
    }
}

#[derive(Debug)]
struct KnownFunctions<V>(HashMap<V, V>);

impl<V: Clone + Eq + Hash> KnownFunctions<V> {
    pub fn new() -> Self {
        KnownFunctions(Default::default())
    }

    pub fn extend(&self, fns: impl Iterator<Item = (V, V)>) -> Self {
        let mut funcs = self.0.clone();
        funcs.extend(fns);
        KnownFunctions(funcs)
    }

    pub fn drop(&self, name: &V) -> Self {
        let mut funcs = self.0.clone();
        funcs.remove(name);
        KnownFunctions(funcs)
    }

    pub fn drop_some<'a>(&'a self, names: impl Iterator<Item = &'a V>) -> Self {
        let mut funcs = self.0.clone();
        for name in names {
            funcs.remove(name);
        }
        KnownFunctions(funcs)
    }

    pub fn known_as(&self, name: &V) -> Option<V> {
        self.0.get(name).cloned()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{cps_expr, cps_field, cps_field_list, cps_ident_list, cps_value};

    #[test]
    fn unknown_application() {
        let ctx = Box::leak(Box::new(Context::new_context("__".to_string())));

        let x: Expr<&str> = cps_expr!((f c));
        let y: Expr<&str> = cps_expr!(select 0 f f__0 (f__0 f c));
        assert_eq!(ctx.convert_closures(&x), y);
    }

    #[test]
    fn simple_conversion() {
        let ctx = Box::leak(Box::new(Context::new_context("__".to_string())));

        let x: Expr<&str> = cps_expr!(record [] r (fix f(c)=(halt r) in (f f)));
        let y: Expr<&str> = cps_expr!(record [] r (fix f__1(f c)=(select 1 f r (halt r)) in (record [(@f__1) r] cls__0 (offset 0 cls__0 f ((@f__1) f f)))));
        assert_eq!(ctx.convert_closures(&x), y);
    }

    #[test]
    fn mutual_recursion() {
        let ctx = Box::leak(Box::new(Context::new_context("__".to_string())));

        let x: Expr<&str> = cps_expr!(record [] r (fix f(c)=(halt r); g(c)=(f c) in (g f)));
        let y: Expr<&str> = cps_expr!(record [] r
            (fix
                f__1(f c)=(select 2 f r (halt r));
                g__2(g c)=(offset (-1) g f ((@f__1) f c))
            in
                (record [(@f__1) (@g__2) r] cls__0
                    (offset 1 cls__0 g
                        (offset 0 cls__0 f
                            ((@g__2) g f))))));
        assert_eq!(ctx.convert_closures(&x), y);
    }

    #[test]
    fn bug() {
        let ctx = Box::leak(Box::new(Context::new_context("__".to_string())));

        let x: Expr<&str> = cps_expr!(fix lambda(k f)=(k f) in (halt lambda));
        let y: Expr<&str> = cps_expr!(fix lambda__1(lambda k f)=(select 0 k f__2 (f__2 k f)) in (record [(@lambda__1)] cls__0 (offset 0 cls__0 lambda (halt lambda))));
        assert_eq!(ctx.convert_closures(&x), y);
    }
}
