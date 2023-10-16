use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{AccessPath, Expr, Value};
use crate::transformations::GensymContext;
use std::collections::HashMap;

const CLS_FUNC_INDEX: isize = 0;

pub struct Context {
    gs: GensymContext,
}

impl Context {
    pub fn new(sym_delim: String) -> Self {
        Context {
            gs: GensymContext::new(sym_delim),
        }
    }
}

impl Context {
    pub fn convert_closures(&self, exp: &Expr<Ref<str>>) -> Expr<Ref<str>> {
        self.convert_closures_(exp, &KnownFunctions::new())
    }
    fn convert_closures_(
        &self,
        exp: &Expr<Ref<str>>,
        known_functions: &KnownFunctions,
    ) -> Expr<Ref<str>> {
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
                let mut rands_out = vec![Value::Var(*r)];
                rands_out.extend(rands.iter().cloned());

                if let Some(renamed) = known_functions.known_as(r) {
                    Expr::App(Value::Label(renamed), Ref::array(rands_out)).into()
                } else {
                    let f = self.gs.gensym("f");
                    Expr::Select(
                        CLS_FUNC_INDEX,
                        Value::Var(r.clone()),
                        f,
                        Expr::App(Value::Var(f), Ref::array(rands_out)).into(),
                    )
                }
            }

            Expr::App(rator, _) => panic!("invalid operator: {:?}", rator),

            Expr::Fix(defs, body) => {
                let cls_arg = self.gs.gensym("cls");

                let mut closure = Closure::new(&self.gs);
                for (f, _, _) in defs.iter() {
                    closure.add_function(*f);
                }
                for v in exp.fix_function_free_vars().iter() {
                    closure.add_var(*v);
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
                            fbody = closure.build_lookup(v, f, Value::Var(*f), fbody);
                        }
                        (closure.get_new_func_name(f), p.prepend(*f), fbody.into())
                    })
                    .collect();

                let mut body = Ref::new(self.convert_closures_(body, &known_functions));
                for (f, _, _) in defs.iter() {
                    let idx = closure.get_func_idx(f).unwrap();
                    body = Ref::new(Expr::Offset(idx, Value::Var(cls_arg), *f, body));
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
                let known_functions = known_functions.drop_some(res.iter().map(|r| &**r));
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
struct Closure<'a> {
    gs: &'a GensymContext,
    funcs: Vec<Ref<str>>,
    renamed_funcs: Vec<Ref<str>>,
    vars: Vec<Ref<str>>,
}

impl<'a> Closure<'a> {
    fn new(gs: &'a GensymContext) -> Self {
        Closure {
            gs,
            funcs: vec![],
            renamed_funcs: vec![],
            vars: vec![],
        }
    }

    fn add_function(&mut self, name: Ref<str>) {
        self.renamed_funcs.push(self.gs.gensym(&name));
        self.funcs.push(name);
    }

    fn add_var(&mut self, name: Ref<str>) {
        self.vars.push(name)
    }

    fn get_new_func_name(&self, name: &str) -> Ref<str> {
        let idx = self.get_func_idx(name).unwrap();
        self.renamed_funcs[idx as usize]
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

    fn build_lookup(
        &self,
        name: Ref<str>,
        current_fn: &str,
        cls_val: Value<Ref<str>>,
        cnt: Expr<Ref<str>>,
    ) -> Expr<Ref<str>> {
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

    fn aliases(&self) -> impl Iterator<Item = (Ref<str>, Ref<str>)> + '_ {
        self.funcs
            .iter()
            .copied()
            .zip(self.renamed_funcs.iter().copied())
    }
}

#[derive(Debug)]
struct KnownFunctions(HashMap<Ref<str>, Ref<str>>);

impl KnownFunctions {
    pub fn new() -> Self {
        KnownFunctions(Default::default())
    }

    pub fn extend(&self, fns: impl Iterator<Item = (Ref<str>, Ref<str>)>) -> Self {
        let mut funcs = self.0.clone();
        funcs.extend(fns);
        KnownFunctions(funcs)
    }

    pub fn drop(&self, name: &str) -> Self {
        let mut funcs = self.0.clone();
        funcs.remove(name);
        KnownFunctions(funcs)
    }

    pub fn drop_some<'a>(&self, names: impl Iterator<Item = &'a str>) -> Self {
        let mut funcs = self.0.clone();
        for name in names {
            funcs.remove(name);
        }
        KnownFunctions(funcs)
    }

    pub fn known_as(&self, name: &str) -> Option<Ref<str>> {
        self.0.get(name).copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{cps_expr, cps_field, cps_field_list, cps_ident_list, cps_value};

    #[test]
    fn unknown_application() {
        let ctx = Box::leak(Box::new(Context::new("__".to_string())));

        let x = cps_expr!((f x));
        let y = cps_expr!(select 0 f f__0 (f__0 f x));
        assert_eq!(ctx.convert_closures(&x), y);
    }

    #[test]
    fn simple_conversion() {
        let ctx = Box::leak(Box::new(Context::new("__".to_string())));

        let x = cps_expr!(record [] r (fix f(x)=(halt r) in (f f)));
        let y = cps_expr!(record [] r (fix f__1(f x)=(select 1 f r (halt r)) in (record [(@f__1) r] cls__0 (offset 0 cls__0 f ((@f__1) f f)))));
        assert_eq!(ctx.convert_closures(&x), y);
    }

    #[test]
    fn mutual_recursion() {
        let ctx = Box::leak(Box::new(Context::new("__".to_string())));

        let x = cps_expr!(record [] r (fix f(x)=(halt r); g(x)=(f g) in (g f)));
        let y = cps_expr!(record [] r
            (fix
                f__1(f x)=(select 2 f r (halt r));
                g__2(g x)=(offset (-1) g f ((@f__1) f g))
            in
                (record [(@f__1) (@g__2) r] cls__0
                    (offset 1 cls__0 g
                        (offset 0 cls__0 f
                            ((@g__2) g f))))));
        assert_eq!(ctx.convert_closures(&x), y);
    }
}
