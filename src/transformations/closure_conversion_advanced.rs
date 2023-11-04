use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Computation, Compute, Expr, Transform, Transformed, Value};
use crate::transformations::closure_conversion::{Closure, CLS_FUNC_INDEX};
use crate::transformations::{GenSym, GensymContext};
use map_macro::hash_set;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::sync::Arc;

/// Requirements:
///   - unique names
///   - labels
pub struct Context<V, F> {
    n_registers: usize,
    vars_free_in_fn: HashMap<F, HashSet<V>>,
    fns_applied_in_fn: HashMap<F, HashSet<F>>,
    sibling_fns: HashMap<F, HashSet<F>>,
    fns_that_need_closures: HashSet<F>,
    gs: Arc<GensymContext>,
}

impl<V: Clone + Eq + Hash, F: Clone + Eq + Hash> Context<V, F> {
    pub fn new(n_registers: usize, gs: Arc<GensymContext>) -> Self {
        Context {
            n_registers,
            vars_free_in_fn: Default::default(),
            fns_applied_in_fn: Default::default(),
            sibling_fns: Default::default(),
            fns_that_need_closures: Default::default(),
            gs,
        }
    }

    pub fn solve_closure_requirements(mut self) -> Self {
        loop {
            let vars_free_in_fn = self.iteration_step_free_vars();
            let fns_that_need_closures = self.iteration_step_needed_closure();

            if vars_free_in_fn == self.vars_free_in_fn
                && fns_that_need_closures == self.fns_that_need_closures
            {
                return self;
            }

            self.vars_free_in_fn = vars_free_in_fn;
            self.fns_that_need_closures = fns_that_need_closures;
        }
    }

    fn iteration_step_free_vars(&self) -> HashMap<F, HashSet<V>> {
        let mut vars_free_in_fn_out = HashMap::with_capacity(self.vars_free_in_fn.len());
        for (f, vf) in &self.vars_free_in_fn {
            let mut fvs = vf.clone();
            for g in self.fns_applied_in_fn[f].difference(&self.fns_that_need_closures) {
                fvs.extend(self.vars_free_in_fn[g].iter().cloned());
            }
            vars_free_in_fn_out.insert(f.clone(), fvs);
        }
        vars_free_in_fn_out
    }

    fn iteration_step_needed_closure(&self) -> HashSet<F> {
        let mut needed = self.fns_that_need_closures.clone();

        // todo: shouldn't we test if |fv| + |params| > N ?
        needed.extend(
            self.vars_free_in_fn
                .iter()
                .filter(|(_, vf)| vf.len() > self.n_registers)
                .map(|(f, _)| f.clone()),
        );

        for f in self.vars_free_in_fn.keys() {
            let tmp = self.fns_applied_in_fn[f]
                .intersection(&self.sibling_fns[f])
                .cloned()
                .collect();
            let mut tmp = self.fns_that_need_closures.intersection(&tmp);
            if tmp.next().is_some() {
                // f is a function that calls another closure-needing function in the same fixture
                needed.insert(f.clone());
            }
        }

        needed
    }
}

impl<'e, V: Clone + Eq + Hash, F: Clone + Eq + Hash> Compute<'e, V, F> for Context<V, F> {
    fn visit_expr(&mut self, expr: &'e Expr<V, F>) -> Computation {
        match expr {
            Expr::Fix(defs, _) => {
                let siblings: HashSet<_> = defs.iter().map(|(f, _, _)| f.clone()).collect();

                for f in &siblings {
                    let mut fsibs = siblings.clone();
                    fsibs.remove(f);
                    self.sibling_fns.insert(f.clone(), fsibs);
                }

                self.vars_free_in_fn.extend(
                    defs.iter()
                        .map(|(f, p, b)| (f, Expr::function_free_vars_nofns(p, b)))
                        .map(|(f, fvs)| (f.clone(), fvs.into())),
                );

                self.fns_applied_in_fn.extend(defs.iter().map(|(f, _, b)| {
                    let mut applied_in = FnsApplied::new();
                    applied_in.compute_for_expr(b);
                    (f.clone(), applied_in.0)
                }));

                Computation::Continue
            }

            Expr::App(_, args) => {
                self.compute_for_values(args);
                Computation::Done
            }

            _ => Computation::Continue,
        }
    }

    fn visit_value(&mut self, value: &Value<V, F>) {
        match value {
            Value::Label(f) => {
                // This function escapes (unless it's the first value of an App node, which should
                // not call this visitor).
                self.fns_that_need_closures.insert(f.clone());
            }
            _ => {}
        }
    }

    fn post_visit_expr(&mut self, _: &'e Expr<V, F>) {}
}

impl<V: Clone + Debug + Display + Eq + GenSym + Hash> Context<V, V> {
    fn make_closure_application(&mut self, f: &V, args: &Ref<[Value<V, V>]>) -> Expr<V, V> {
        let mut args_ = vec![Value::Var(f.clone())];
        args_.extend(self.transform_values(args).iter().cloned());
        let f_: V = self.gs.gensym(f);
        Expr::Select(
            CLS_FUNC_INDEX,
            Value::Var(f.clone()),
            f_.clone(),
            Expr::App(Value::Var(f_), Ref::array(args_)).into(),
        )
    }
}

impl<V: Clone + Debug + Display + Eq + GenSym + Hash> Transform<V, V> for Context<V, V> {
    fn visit_expr(&mut self, expr: &Expr<V, V>) -> Transformed<Expr<V, V>> {
        match expr {
            Expr::App(Value::Var(f), args) => {
                Transformed::Done(self.make_closure_application(f, args))
            }

            Expr::App(Value::Label(f), args) if self.fns_that_need_closures.contains(f) => {
                Transformed::Done(self.make_closure_application(f, args))
            }

            Expr::Fix(defs, cnt) => {
                let cls_arg: V = self.gs.gensym("cls");

                let mut closure = Closure::new(self.gs.clone());
                let mut clvars = hash_set![];
                for (f, _, _) in defs.iter() {
                    if self.fns_that_need_closures.contains(f) {
                        closure.add_function(f);
                        clvars.extend(&self.vars_free_in_fn[f])
                    }
                }
                for v in clvars {
                    closure.add_var(v)
                }

                let mut defs_out = vec![];
                for (f, p, b) in defs.iter() {
                    let mut fbody = self.transform_expr(b);
                    if self.fns_that_need_closures.contains(f) {
                        for v in &self.vars_free_in_fn[f] {
                            fbody =
                                closure.build_lookup(v.clone(), f, Value::Var(f.clone()), fbody);
                        }
                        defs_out.push((
                            closure.get_new_func_name(f),
                            p.prepend(f.clone()),
                            fbody.into(),
                        ));
                    } else {
                        defs_out.push((f.clone(), *p, fbody.into()));
                    }
                }

                let mut cnt = Ref::new(self.transform_expr(cnt));
                for (f, _, _) in defs.iter() {
                    if self.fns_that_need_closures.contains(f) {
                        let idx = closure.get_func_idx(f).unwrap();
                        cnt = Ref::new(Expr::Offset(
                            idx,
                            Value::Var(cls_arg.clone()),
                            f.clone(),
                            cnt,
                        ));
                    }
                }

                let cls_fields = closure.into_fields();
                let cnt_out = Expr::Record(Ref::array(cls_fields), cls_arg, cnt);

                Transformed::Done(Expr::Fix(Ref::array(defs_out), Ref::new(cnt_out)))
            }

            _ => Transformed::Continue,
        }
    }

    fn visit_value(&mut self, value: &Value<V, V>) -> Transformed<Value<V, V>> {
        match value {
            Value::Label(f) if self.fns_that_need_closures.contains(f) => {
                Transformed::Done(Value::Var(f.clone()))
            }
            _ => Transformed::Continue,
        }
    }
}

struct FnsApplied<F>(HashSet<F>);

impl<F> FnsApplied<F> {
    pub fn new() -> Self {
        FnsApplied(HashSet::new())
    }
}

impl<'e, V: Clone + Eq + Hash, F: Clone + Eq + Hash> Compute<'e, V, F> for FnsApplied<F> {
    fn visit_expr(&mut self, expr: &'e Expr<V, F>) -> Computation {
        match expr {
            Expr::App(Value::Label(f), _) => {
                self.0.insert(f.clone());
                Computation::Done
            }

            Expr::Fix(_, cnt) => {
                self.compute_for_expr(cnt);
                Computation::Done
            }

            _ => Computation::Continue,
        }
    }

    fn visit_value(&mut self, _: &Value<V, F>) {}

    fn post_visit_expr(&mut self, _: &'e Expr<V, F>) {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use map_macro::{hash_map, hash_set};

    #[test]
    fn find_free_vars() {
        let x = Expr::from_str(
            "(fix ((f () (fix ((g () (y))) (x (@ g))))) (fix ((h () (z))) ((@ h))))",
        )
        .unwrap();
        let mut ctx = Context::new(0, Arc::new(GensymContext::new("_")));
        ctx.compute_for_expr(&x);
        assert_eq!(
            ctx.vars_free_in_fn,
            hash_map! {
            "h".into() => hash_set!["z".into()],
            "g".into() => hash_set!["y".into()],
            "f".into() => hash_set!["x".into(), "y".into()]}
        )
    }

    #[test]
    fn find_escaping_functions() {
        let x = Expr::from_str(
            "(fix ((f () (fix ((g () (y (@ f)))) ((@ g))))) (fix ((h () (z))) ((@ g))))",
        )
        .unwrap();
        let mut ctx = Context::new(0, Arc::new(GensymContext::new("_")));
        ctx.compute_for_expr(&x);
        assert_eq!(ctx.fns_that_need_closures, hash_set!["f".into()]) // f escapes
    }

    #[test]
    fn find_applied_in_bodies() {
        let x = Expr::from_str(
            "(fix ((f () (fix ((g () ((@ h)))) ((@ g))))) (fix ((h () ((@ f)))) (halt 0)))",
        )
        .unwrap();
        let mut ctx = Context::new(0, Arc::new(GensymContext::new("_")));
        ctx.compute_for_expr(&x);
        assert_eq!(
            ctx.fns_applied_in_fn,
            hash_map! {
            "h".into() => hash_set!["f".into()],
            "g".into() => hash_set!["h".into()],
            "f".into() => hash_set!["g".into()]}
        )
    }

    #[test]
    fn find_siblings() {
        let x = Expr::from_str(
            "(fix ((f () (fix ((g () (y)) (i () (z))) (x)))) (fix ((h () (z)) (j () (z))) (halt 0)))",
        )
        .unwrap();
        let mut ctx = Context::new(0, Arc::new(GensymContext::new("_")));
        ctx.compute_for_expr(&x);
        assert_eq!(
            ctx.sibling_fns,
            hash_map! {
            "f".into() => hash_set![],
            "g".into() => hash_set!["i".into()],
            "i".into() => hash_set!["g".into()],
            "h".into() => hash_set!["j".into()],
            "j".into() => hash_set!["h".into()]}
        )
    }

    #[test]
    fn free_var_update() {
        let ctx: Context<&str, &str> = Context {
            n_registers: 0,
            vars_free_in_fn: hash_map![
                "f".into() => hash_set!["x".into()],
                "g".into() => hash_set!["y".into()]],
            fns_applied_in_fn: hash_map![
                "f".into() => hash_set!["g".into()],
                "g".into() => hash_set!["f".into()]],
            sibling_fns: hash_map![],
            fns_that_need_closures: hash_set![],
            gs: Arc::new(GensymContext::new("_")),
        };

        assert_eq!(
            ctx.iteration_step_free_vars(),
            hash_map![
                "f".into() => hash_set!["x".into(), "y".into()],
                "g".into() => hash_set!["y".into(), "x".into()]]
        );
    }

    #[test]
    fn free_var_convergenge() {
        let ctx: Context<&str, &str> = Context {
            n_registers: 0,
            vars_free_in_fn: hash_map![
                "f".into() => hash_set!["x".into(), "y".into()],
                "g".into() => hash_set!["y".into(), "x".into()]],
            fns_applied_in_fn: hash_map![
                "f".into() => hash_set!["g".into()],
                "g".into() => hash_set!["f".into()]],
            sibling_fns: hash_map![],
            fns_that_need_closures: hash_set![],
            gs: Arc::new(GensymContext::new("_")),
        };

        assert_eq!(
            ctx.iteration_step_free_vars(),
            hash_map![
                "f".into() => hash_set!["x".into(), "y".into()],
                "g".into() => hash_set!["y".into(), "x".into()]]
        );
    }

    #[test]
    fn closure_need_update_due_to_register_pressure() {
        let ctx: Context<&str, &str> = Context {
            n_registers: 1,
            vars_free_in_fn: hash_map![
                "f".into() => hash_set!["x".into(), "y".into()]],
            fns_applied_in_fn: hash_map![
                "f".into() => hash_set![]],
            sibling_fns: hash_map![
                "f".into() => hash_set![]],
            fns_that_need_closures: hash_set![],
            gs: Arc::new(GensymContext::new("_")),
        };

        assert_eq!(ctx.iteration_step_needed_closure(), hash_set!["f".into()]);
    }

    #[test]
    fn closure_need_update_due_to_sibling() {
        let ctx: Context<&str, &str> = Context {
            n_registers: 1,
            vars_free_in_fn: hash_map![
                "f".into() => hash_set![],
                "g".into() => hash_set![]],
            fns_applied_in_fn: hash_map![
                "f".into() => hash_set!["g".into()],
                "g".into() => hash_set![]],
            sibling_fns: hash_map![
                "f".into() => hash_set!["g".into()],
                "g".into() => hash_set!["f".into()]],
            fns_that_need_closures: hash_set!["g".into()],
            gs: Arc::new(GensymContext::new("_")),
        };

        assert_eq!(
            ctx.iteration_step_needed_closure(),
            hash_set!["f".into(), "g".into()]
        );
    }

    #[test]
    fn closure_need_convergence() {
        let ctx: Context<&str, &str> = Context {
            n_registers: 1,
            vars_free_in_fn: hash_map![
                "f".into() => hash_set!["x".into(), "y".into()],
                "g".into() => hash_set![]],
            fns_applied_in_fn: hash_map![
                "f".into() => hash_set![],
                "g".into() => hash_set!["f".into()]],
            sibling_fns: hash_map![
                "f".into() => hash_set!["g".into()],
                "g".into() => hash_set!["f".into()]],
            fns_that_need_closures: hash_set!["f".into(), "g".into()],
            gs: Arc::new(GensymContext::new("_")),
        };

        assert_eq!(
            ctx.iteration_step_needed_closure(),
            hash_set!["f".into(), "g".into()]
        );
    }

    #[test]
    fn solve_closure_needs() {
        let ctx: Context<&str, &str> = Context {
            n_registers: 1,
            vars_free_in_fn: hash_map![
                "f".into() => hash_set!["x".into(), "y".into()],
                "g".into() => hash_set!["z".into()]],
            fns_applied_in_fn: hash_map![
                "f".into() => hash_set![],
                "g".into() => hash_set!["f".into()]],
            sibling_fns: hash_map![
                "f".into() => hash_set!["g".into()],
                "g".into() => hash_set!["f".into()]],
            fns_that_need_closures: hash_set![],
            gs: Arc::new(GensymContext::new("_")),
        };

        let ctx = ctx.solve_closure_requirements();

        assert_eq!(
            ctx.fns_that_need_closures,
            hash_set!["f".into(), "g".into()]
        );

        assert_eq!(
            ctx.vars_free_in_fn,
            hash_map![
                "f".into() => hash_set!["x".into(), "y".into()],
                "g".into() => hash_set!["x".into(), "y".into(), "z".into()]]
        );
    }

    #[test]
    fn free_vars_passed_as_arguments_to_known_function() {
        // A function with just a few free vars should not require a closure if it does not escape.
        // This function's parameters will need to be extended by the free variables.
        // Any calls should pass in those variables. (This is possible, because the function is
        // known, and so all free vars are in scope at the call site.)

        let mut ctx = Context {
            n_registers: 10,
            vars_free_in_fn: hash_map![
                "f".into() => hash_set!["x".into(), "y".into()]],
            fns_applied_in_fn: hash_map![
                "f".into() => hash_set![]],
            sibling_fns: hash_map![
                "f".into() => hash_set![]],
            fns_that_need_closures: hash_set![],
            gs: Arc::new(GensymContext::new("__")),
        };

        let x = Expr::from_str("((@ f) 0)").unwrap();
        let y = Expr::from_str("((@ f) 0 x y)").unwrap();
        assert_eq!(ctx.transform_expr(&x), y);

        let x = Expr::from_str("(fix ((f (a) (halt 0))) (halt 0))").unwrap();
        let y = Expr::from_str("(fix ((f (a x y) (halt 0))) (halt 0))").unwrap();
        assert_eq!(ctx.transform_expr(&x), y);
    }
}