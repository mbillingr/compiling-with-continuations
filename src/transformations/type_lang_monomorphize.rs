use crate::languages::type_lang::ast::{Def, EnumMatchArm, Expr, Type};
use crate::transformations::GensymContext;
use std::sync::Arc;

#[derive(Default)]
pub struct Context {
    function_realizations: Vec<(String, Option<Vec<(String, Type)>>)>,
    gs: Arc<GensymContext>,
}

impl Context {
    pub fn new(gs: Arc<GensymContext>) -> Self {
        Context {
            function_realizations: Default::default(),
            gs,
        }
    }

    pub fn monomporphize(&mut self, expr: &Expr) -> Expr {
        match expr {
            Expr::Int(x) => Expr::Int(*x),
            Expr::Real(x) => Expr::Real(*x),
            Expr::String(x) => Expr::String(x.clone()),
            Expr::Ref(x) => Expr::Ref(x.clone()),
            Expr::Apply(app) => Expr::apply(self.monomporphize(&app.0), self.monomporphize(&app.1)),
            Expr::Record(fields) => Expr::record(
                fields
                    .iter()
                    .map(|f| self.monomporphize(f))
                    .collect::<Vec<_>>(),
            ),
            Expr::Cons(cons) => {
                let (ty, va, args) = &**cons;
                Expr::cons(
                    ty,
                    va,
                    args.iter()
                        .map(|a| self.monomporphize(a))
                        .collect::<Vec<_>>(),
                )
            }
            Expr::Cons2(_) => expr.clone(),
            Expr::MatchEnum(mat) => Expr::match_enum(
                self.monomporphize(&mat.0),
                mat.1
                    .iter()
                    .map(|arm| EnumMatchArm {
                        pattern: arm.pattern.clone(),
                        branch: self.monomporphize(&arm.branch),
                    })
                    .collect::<Vec<_>>(),
            ),
            Expr::Lambda(lam) => {
                self.push_nonfn_binding(lam.param.to_string());
                let body_ = self.monomporphize(&lam.body);
                self.pop_binding();
                Expr::lambda(&lam.param, body_)
            }

            Expr::Defs(dfs) => {
                let (defs, body) = &**dfs;

                for def in defs {
                    match def {
                        Def::Enum(_) => {} //ignore
                        Def::Func(_) => panic!("uninferred function"),
                        Def::InferredFunc(fun) => {
                            self.push_fndef(fun.fname.to_string());
                        }
                    }
                }

                let body_ = self.monomporphize(body);

                let mut defs_out = vec![];
                for def in defs {
                    match def {
                        Def::Enum(_) => {} //ignore
                        Def::Func(_) => panic!("uninferred function"),
                        Def::InferredFunc(fun) => {
                            self.push_nonfn_binding(fun.param.clone());
                            let fn_body = self.monomporphize(&fun.body);
                            self.pop_binding();

                            for (new_name, realized_signature) in
                                self.lookup(&fun.fname).map(Vec::as_slice).unwrap_or(&[])
                            {
                                defs_out.push(Def::inferred_func(
                                    realized_signature.clone(),
                                    new_name,
                                    &fun.param,
                                    fn_body.clone(),
                                ))
                            }
                        }
                    }
                }

                for def in defs {
                    match def {
                        Def::Enum(_) => {} //ignore
                        Def::Func(_) => panic!("uninferred function"),
                        Def::InferredFunc(_) => {
                            self.pop_binding();
                        }
                    }
                }

                Expr::defs(defs_out, body_)
            }

            Expr::Add(add) => Expr::add(self.monomporphize(&add.0), self.monomporphize(&add.1)),
            Expr::Read() => Expr::Read(),
            Expr::Show(x) => Expr::show(self.monomporphize(x)),

            Expr::Annotation(ann) => match &**ann {
                (ty @ Type::Fn(_), ex @ Expr::Ref(fname)) => {
                    let gs = self.gs.clone(); // to avoid borrow of self
                    match self.lookup_mut(fname) {
                        Some(frs) => {
                            let new_name =
                                if let Some((name, _)) = frs.iter().find(|(_, t)| t == ty) {
                                    name.clone()
                                } else {
                                    let name: String = gs.gensym(fname);
                                    frs.push((name.clone(), ty.clone()));
                                    name
                                };
                            Expr::annotate(ty.clone(), Expr::Ref(new_name))
                        }
                        None => Expr::annotate(ty.clone(), self.monomporphize(ex)),
                    }
                }
                (ty, ex) => Expr::annotate(ty.clone(), self.monomporphize(ex)),
            },
        }
    }

    fn push_fndef(&mut self, name: String) {
        self.function_realizations.push((name, Some(vec![])));
    }

    fn pop_binding(&mut self) {
        self.function_realizations.pop();
    }

    fn push_nonfn_binding(&mut self, name: String) {
        self.function_realizations.push((name, None));
    }

    fn lookup(&self, name: &str) -> Option<&Vec<(String, Type)>> {
        self.function_realizations
            .iter()
            .rev()
            .find(|(fname, _)| fname == name)
            .and_then(|(_, frs)| frs.as_ref())
    }

    fn lookup_mut(&mut self, name: &str) -> Option<&mut Vec<(String, Type)>> {
        self.function_realizations
            .iter_mut()
            .rev()
            .find(|(fname, _)| fname == name)
            .and_then(|(_, frs)| frs.as_mut())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::type_lang::ast::{Def, Type};

    #[test]
    fn non_generic_function() {
        let x = Expr::defs(
            [Def::inferred_func(
                Type::func(Type::Int, Type::Int),
                "fn",
                "x",
                "x",
            )],
            Expr::apply(Expr::annotate(Type::func(Type::Int, Type::Int), "fn"), 123),
        );

        let y = Expr::defs(
            [Def::inferred_func(
                Type::func(Type::Int, Type::Int),
                "fn__0",
                "x",
                "x",
            )],
            Expr::apply(
                Expr::annotate(Type::func(Type::Int, Type::Int), "fn__0"),
                123,
            ),
        );

        assert_eq!(Context::default().monomporphize(&x), y);
    }

    #[test]
    fn unused_function() {
        let x = Expr::defs(
            [Def::inferred_func(
                Type::func(Type::Int, Type::Int),
                "fn",
                "x",
                "x",
            )],
            0,
        );

        let y = Expr::defs([], 0);

        assert_eq!(Context::default().monomporphize(&x), y);
    }

    #[test]
    fn one_generic_use() {
        let x = Expr::defs(
            [Def::inferred_func(
                Type::Int, // this is bullshit, but should not matter
                "fn",
                "x",
                "x",
            )],
            Expr::annotate(Type::func(Type::Int, Type::Int), "fn"),
        );

        let y = Expr::defs(
            [Def::inferred_func(
                Type::func(Type::Int, Type::Int),
                "fn__0",
                "x",
                "x",
            )],
            Expr::annotate(Type::func(Type::Int, Type::Int), "fn__0"),
        );

        assert_eq!(Context::default().monomporphize(&x), y);
    }

    #[test]
    fn different_generic_uses() {
        let x = Expr::defs(
            [Def::inferred_func(
                Type::Unit, // this is bullshit, but should not matter
                "fn",
                "x",
                "x",
            )],
            Expr::record([
                Expr::annotate(Type::func(Type::Int, Type::Int), "fn"),
                Expr::annotate(Type::func(Type::Real, Type::Real), "fn"),
                Expr::annotate(Type::func(Type::Int, Type::Int), "fn"),
            ]),
        );

        let y = Expr::defs(
            [
                Def::inferred_func(Type::func(Type::Int, Type::Int), "fn__0", "x", "x"),
                Def::inferred_func(Type::func(Type::Real, Type::Real), "fn__1", "x", "x"),
            ],
            Expr::record([
                Expr::annotate(Type::func(Type::Int, Type::Int), "fn__0"),
                Expr::annotate(Type::func(Type::Real, Type::Real), "fn__1"),
                Expr::annotate(Type::func(Type::Int, Type::Int), "fn__0"),
            ]),
        );

        assert_eq!(Context::default().monomporphize(&x), y);
    }

    #[test]
    fn unused_because_shadowed_by_lambda_binding() {
        let x = Expr::defs(
            [Def::inferred_func(
                Type::Unit, // this is bullshit, but should not matter
                "f",
                "x",
                "x",
            )],
            Expr::lambda("f", Expr::annotate(Type::func(Type::Int, Type::Int), "f")),
        );

        let y = Expr::defs(
            [],
            Expr::lambda("f", Expr::annotate(Type::func(Type::Int, Type::Int), "f")),
        );

        assert_eq!(Context::default().monomporphize(&x), y);
    }

    #[test]
    fn unused_because_shadowed_by_def_binding() {
        let x = Expr::defs(
            [Def::inferred_func(
                Type::Unit, // this is bullshit, but should not matter
                "f",
                "x",
                "x",
            )],
            Expr::defs(
                [Def::inferred_func(
                    Type::Unit, // this is bullshit, but should not matter
                    "g",
                    "f",
                    Expr::annotate(Type::func(Type::Int, Type::Int), "f"),
                )],
                0,
            ),
        );

        let y = Expr::defs([], Expr::defs([], 0));

        assert_eq!(Context::default().monomporphize(&x), y);
    }

    #[test]
    fn usage_refers_only_to_binding_in_scope() {
        let x = Expr::defs(
            [Def::inferred_func(
                Type::Unit, // this is bullshit, but should not matter
                "f",
                "x",
                "x",
            )],
            Expr::defs(
                [Def::inferred_func(
                    Type::Unit, // this is bullshit, but should not matter
                    "f",
                    "x",
                    "x",
                )],
                Expr::annotate(Type::func(Type::Int, Type::Int), "f"),
            ),
        );

        let y = Expr::defs(
            [],
            Expr::defs(
                [Def::inferred_func(
                    Type::func(Type::Int, Type::Int),
                    "f__0",
                    "x",
                    "x",
                )],
                Expr::annotate(Type::func(Type::Int, Type::Int), "f__0"),
            ),
        );

        assert_eq!(Context::default().monomporphize(&x), y);
    }

    #[test]
    fn indirect_usage() {
        let x = Expr::defs(
            [Def::inferred_func(
                Type::Unit, // this is bullshit, but should not matter
                "f",
                "x",
                "x",
            )],
            Expr::defs(
                [Def::inferred_func(
                    Type::Unit, // this is bullshit, but should not matter
                    "g",
                    "y",
                    Expr::annotate(Type::func(Type::Int, Type::Int), "f"),
                )],
                Expr::annotate(Type::func(Type::Int, Type::Int), "g"),
            ),
        );

        let y = Expr::defs(
            [Def::inferred_func(
                Type::func(Type::Int, Type::Int), // this is bullshit, but should not matter
                "f__1",
                "x",
                "x",
            )],
            Expr::defs(
                [Def::inferred_func(
                    Type::func(Type::Int, Type::Int), // this is bullshit, but should not matter
                    "g__0",
                    "y",
                    Expr::annotate(Type::func(Type::Int, Type::Int), "f__1"),
                )],
                Expr::annotate(Type::func(Type::Int, Type::Int), "g__0"),
            ),
        );

        assert_eq!(Context::default().monomporphize(&x), y);
    }
}
