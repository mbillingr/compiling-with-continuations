use crate::core::reference::Ref;
use crate::languages::common_primops::PrimOp;
use crate::languages::mini_lambda::ast::{Con, ConRep};
use crate::languages::type_lang::ast::{Def, EnumType, EnumVariantPattern, Type};
use crate::transformations::GensymContext;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

pub type LExp = crate::languages::mini_lambda::ast::Expr<Ref<str>>;
pub type TExp = crate::languages::type_lang::ast::Expr;

#[derive(Default)]
pub struct Context {
    enum_reprs: HashMap<*const EnumType, HashMap<String, ConRep>>,
    gs: Arc<GensymContext>,
}

impl Context {
    pub fn new(gs: Arc<GensymContext>) -> Self {
        Context {
            enum_reprs: Default::default(),
            gs,
        }
    }
}

impl Context {
    pub fn convert(&mut self, expr: &TExp) -> LExp {
        match expr {
            TExp::Int(x) => LExp::int(*x),
            TExp::Real(x) => LExp::real(*x),
            TExp::String(x) => LExp::string(x),
            TExp::Ref(x) => LExp::var(x),
            TExp::Apply(app) => LExp::apply(self.convert(&app.0), self.convert(&app.1)),

            TExp::Lambda(lam) => LExp::func(&lam.param, self.convert(&lam.body)),

            TExp::Defs(dfs) => {
                let (defs, body) = &**dfs;

                let mut names = vec![];
                let mut fns = vec![];
                for def in defs {
                    match def {
                        Def::Func(_) => panic!("Uninferred func: {def:?}"),
                        Def::Enum(_) => {}
                        Def::InferredFunc(d) => {
                            names.push(d.fname.clone());
                            fns.push(LExp::func(&d.param, self.convert(&d.body)));
                        }
                    }
                }

                LExp::fix(names, fns, self.convert(body))
            }

            TExp::Cons(_) | TExp::Add(_) => panic!("Annotation required: {expr:?}"),

            TExp::Decons(deco) => {
                let (val, variant, vars, matches, mismatch) = &**deco;
                let en = match val.get_type() {
                    Type::Enum(en) => en,
                    _ => panic!("Expected enum: {val:?}"),
                };
                let otherwise = self.convert(mismatch);
                let conreps: Vec<_> = self.enum_all_reps(en).collect();
                let target_rep = self.enum_variant_repr(en, variant);
                match target_rep {
                    ConRep::Constant(_) => {
                        let arm = vec![(Con::Data(target_rep), self.convert(matches))];
                        LExp::switch(self.convert(val), conreps, arm, Some(otherwise))
                    }
                    _ => {
                        let switch_val: Ref<str> = self.gs.gensym("switch_val");
                        let mut arm = self.convert(matches);
                        let inner = LExp::decon(target_rep, switch_val);
                        if vars.len() == 1 {
                            arm = LExp::bind(&vars[0], inner.clone(), arm)
                        } else {
                            for (i, v) in vars.iter().enumerate() {
                                arm = LExp::bind(v, LExp::select(i as isize, inner.clone()), arm)
                            }
                        }
                        let the_switch = LExp::switch(
                            switch_val,
                            conreps,
                            vec![(Con::Data(target_rep), arm)],
                            Some(otherwise),
                        );
                        LExp::bind(switch_val, self.convert(val), the_switch)
                    }
                }
            }

            TExp::MatchEnum(mat) => {
                let (val, arms) = &**mat;
                let en = match val.get_type() {
                    Type::Enum(en) => en,
                    _ => panic!("Expected enum: {val:?}"),
                };
                let switch_val: Ref<str> = self.gs.gensym("switch_val");

                let mut arms_ = vec![];
                for (pat, branch) in arms {
                    match pat {
                        EnumVariantPattern::Constant(name) => {
                            let variant_rep = self.enum_variant_repr(en, name);
                            arms_.push((Con::Data(variant_rep), self.convert(branch)))
                        }
                        EnumVariantPattern::Constructor(name, var) => {
                            let variant_rep = self.enum_variant_repr(en, name);
                            arms_.push((
                                Con::Data(variant_rep),
                                LExp::bind(
                                    var,
                                    LExp::decon(variant_rep, switch_val),
                                    self.convert(branch),
                                ),
                            ))
                        }
                    }
                }

                let conreps: Vec<_> = self.enum_all_reps(en).collect();
                let the_switch = LExp::switch(switch_val, conreps, arms_, None::<LExp>);
                LExp::bind(switch_val, self.convert(val), the_switch)
            }

            TExp::Show(x) => match x.get_type() {
                Type::Int => LExp::apply(PrimOp::ShowInt, self.convert(x)),
                Type::Real => LExp::apply(PrimOp::ShowReal, self.convert(x)),
                Type::String => LExp::apply(PrimOp::ShowStr, self.convert(x)),
                Type::Enum(e) => {
                    let mut conreps = vec![];
                    let mut arms = vec![];
                    for (vname, rep) in self.enum_repr(e) {
                        conreps.push(*rep);
                        arms.push((
                            Con::Data(*rep),
                            match rep {
                                ConRep::Constant(_) => {
                                    LExp::apply(PrimOp::ShowStr, LExp::string(vname))
                                }
                                ConRep::Tagged(_) | ConRep::Transparent => LExp::sequence(vec![
                                    LExp::apply(PrimOp::ShowStr, LExp::string("(")),
                                    LExp::apply(PrimOp::ShowStr, LExp::string(vname)),
                                    LExp::apply(PrimOp::ShowStr, LExp::string(" ")),
                                    LExp::apply(PrimOp::ShowStr, LExp::string("...")),
                                    LExp::apply(PrimOp::ShowStr, LExp::string(")")),
                                ]),
                            },
                        ));
                    }
                    LExp::switch(self.convert(x), conreps, arms, None::<LExp>)
                }
                _ => todo!("{expr:?}"),
            },

            TExp::Annotation(ann) => match &**ann {
                (Type::Enum(en), TExp::Cons(con)) => {
                    let (_, variant, args) = &**con;
                    let conrep = self.enum_variant_repr(en, variant);
                    let val = match args.as_slice() {
                        [] => LExp::int(0),
                        [x] => self.convert(x),
                        xs => LExp::record(xs.iter().map(|x| self.convert(x)).collect::<Vec<_>>()),
                    };
                    LExp::con(conrep, val)
                }

                (Type::Enum(en), TExp::Cons2(con)) => {
                    let variant = &con.1;
                    let conrep = self.enum_variant_repr(en, variant);
                    LExp::con(conrep, LExp::int(0))
                }

                (Type::Fn(tf), TExp::Cons2(con)) => {
                    let en = match &tf.1 {
                        Type::Enum(en) => en,
                        _ => panic!("wrong type"),
                    };
                    let variant = &con.1;
                    let conrep = self.enum_variant_repr(en, variant);
                    LExp::func("x", LExp::con(conrep, LExp::var("x")))
                }

                (Type::Int, TExp::Add(add)) => LExp::apply(
                    PrimOp::IAdd,
                    LExp::record(vec![
                        self.convert(&add.0).into(),
                        self.convert(&add.1).into(),
                    ]),
                ),

                (Type::Real, TExp::Add(add)) => LExp::apply(
                    todo!() as PrimOp,
                    LExp::record(vec![
                        self.convert(&add.0).into(),
                        self.convert(&add.1).into(),
                    ]),
                ),

                (Type::Int, TExp::Read()) => LExp::apply(PrimOp::ReadInt, LExp::record(vec![])),

                (_, ex @ TExp::Ref(_)) => self.convert(ex),
                (_, ex @ TExp::Apply(_)) => self.convert(ex),
                (_, ex @ TExp::Lambda(_)) => self.convert(ex),
                (_, ex @ TExp::MatchEnum(_)) => self.convert(ex),
                _ => todo!("{expr:?}"),
            },

            _ => todo!("{expr:?}"),
        }
    }

    pub fn enum_repr(&mut self, en: &Rc<EnumType>) -> &HashMap<String, ConRep> {
        self.enum_ensure_known(en);
        &self.enum_reprs[&Rc::as_ptr(en)]
    }

    pub fn enum_variant_repr(&mut self, en: &Rc<EnumType>, variant: &str) -> ConRep {
        self.enum_repr(en)[variant]
    }

    pub fn enum_all_reps<'a>(&'a mut self, en: &Rc<EnumType>) -> impl Iterator<Item = ConRep> + 'a {
        self.enum_ensure_known(en);
        let mut named_reps: Vec<_> = self.enum_reprs[&Rc::as_ptr(en)].iter().collect();
        named_reps.sort_unstable_by_key(|(name, _)| *name);
        named_reps.into_iter().map(|(_, &cr)| cr)
    }

    pub fn enum_ensure_known(&mut self, en: &Rc<EnumType>) {
        if self.enum_reprs.get(&Rc::as_ptr(en)).is_some() {
            return;
        }

        let mut const_variants: Vec<_> = en
            .variants
            .iter()
            .filter(|(_, args)| args.is_empty())
            .map(|(name, _)| name)
            .collect();

        let mut tag_variants: Vec<_> = en
            .variants
            .iter()
            .filter(|(_, args)| !args.is_empty())
            .map(|(name, _)| name)
            .collect();

        let mut reps = HashMap::new();

        if const_variants.len() == 0 && tag_variants.len() == 1 {
            reps.insert(tag_variants.pop().cloned().unwrap(), ConRep::Transparent);
        } else {
            // make the representation consistent
            const_variants.sort_unstable();
            tag_variants.sort_unstable();

            reps.extend(
                const_variants
                    .into_iter()
                    .enumerate()
                    .map(|(i, name)| (name.clone(), ConRep::Constant(i))),
            );
            reps.extend(
                tag_variants
                    .into_iter()
                    .enumerate()
                    .map(|(i, name)| (name.clone(), ConRep::Tagged(i))),
            );
        }

        self.enum_reprs.insert(Rc::as_ptr(en), reps);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::mini_lambda::ast::{Con, ConRep};
    use crate::languages::type_lang::ast::{Def, EnumDef};
    use crate::languages::type_lang::type_checker::GenericType;

    #[test]
    fn convert_constants() {
        assert_eq!(Context::default().convert(&TExp::int(42)), LExp::Int(42));
        assert_eq!(
            Context::default().convert(&TExp::real(3.14)),
            LExp::Real(3.14)
        );
        assert_eq!(
            Context::default().convert(&TExp::string("foo")),
            LExp::from_str("\"foo\"").unwrap()
        );
    }

    #[test]
    fn convert_variable_reference() {
        assert_eq!(
            Context::default().convert(&TExp::var("x")),
            LExp::from_str("x").unwrap()
        );
    }

    #[test]
    fn convert_application() {
        assert_eq!(
            Context::default().convert(&TExp::apply("f", "x")),
            LExp::from_str("(f x)").unwrap()
        );
    }

    #[test]
    fn convert_lambda() {
        assert_eq!(
            Context::default().convert(&TExp::lambda("x", "x")),
            LExp::from_str("(fn x x)").unwrap()
        );
    }

    #[test]
    fn convert_add() {
        assert_eq!(
            Context::default().convert(&TExp::annotate(Type::Int, TExp::add(1, 2))),
            LExp::from_str("((primitive +) (record 1 2))").unwrap()
        );

        /*assert_eq!(
            Context::new().convert(&TExp::annotate(Type::Real, TExp::add(1.2, 2.2))),
            LExp::from_str("((primitive +) (record 1 2))").unwrap()
        );*/

        // no need to worry about this case, the type checker should prevent it!
        assert_eq!(
            Context::default().convert(&TExp::annotate(Type::Int, TExp::add(1, 2.0))),
            LExp::from_str("((primitive +) (record 1 2.0))").unwrap()
        );
    }

    #[test]
    fn convert_read() {
        assert_eq!(
            Context::default().convert(&TExp::annotate(Type::Int, TExp::Read())),
            LExp::from_str("((primitive read-int) (record))").unwrap()
        );
    }

    #[test]
    fn convert_show() {
        assert_eq!(
            Context::default().convert(&TExp::show(TExp::int(42))),
            LExp::from_str("((primitive show-int) 42)").unwrap()
        );

        assert_eq!(
            Context::default().convert(&TExp::show(TExp::annotate(Type::Int, TExp::add(1, 2)))),
            LExp::from_str("((primitive show-int) ((primitive +) (record 1 2)))").unwrap()
        );
    }

    #[test]
    fn convert_simple_enum() {
        let x = TExp::annotate(
            Type::enum_(
                Rc::new(GenericType::GenericEnum(EnumDef {
                    tname: "ABC".to_string(),
                    tvars: vec![],
                    variants: vec![].into(),
                })),
                [
                    ("A".to_string(), vec![]),
                    ("B".to_string(), vec![]),
                    ("C".to_string(), vec![]),
                ],
            ),
            TExp::cons("ABC", "B", [] as [i64; 0]),
        );

        let y = LExp::con(ConRep::Constant(1), 0);

        assert_eq!(Context::default().convert(&x), y);
    }

    #[test]
    fn convert_enum_with_variants() {
        let mut ctx = Context::default();
        let ety = Type::enum_(
            Rc::new(GenericType::GenericEnum(EnumDef {
                tname: "ABC".to_string(),
                tvars: vec![],
                variants: vec![].into(),
            })),
            [
                ("A".to_string(), vec![]),
                ("B".to_string(), vec![Type::Int]),
                ("C".to_string(), vec![Type::Int, Type::Int]),
            ],
        );

        let x = TExp::annotate(ety.clone(), TExp::cons("ABC", "A", [] as [i64; 0]));
        let y = LExp::con(ConRep::Constant(0), 0);
        assert_eq!(ctx.convert(&x), y);

        let x = TExp::annotate(ety.clone(), TExp::cons("ABC", "B", [1]));
        let y = LExp::con(ConRep::Tagged(0), 1);
        assert_eq!(ctx.convert(&x), y);

        let x = TExp::annotate(ety.clone(), TExp::cons("ABC", "B", [2, 3]));
        let y = LExp::con(
            ConRep::Tagged(0),
            LExp::record(vec![LExp::int(2), LExp::int(3)]),
        );
        assert_eq!(ctx.convert(&x), y);
    }

    #[test]
    fn convert_transparent_enum() {
        let x = TExp::annotate(
            Type::enum_(
                Rc::new(GenericType::GenericEnum(EnumDef {
                    tname: "Foo".to_string(),
                    tvars: vec![],
                    variants: vec![].into(),
                })),
                [("X".to_string(), vec![Type::Int])],
            ),
            TExp::cons("Foo", "X", [42]),
        );

        let y = LExp::con(ConRep::Transparent, 42);

        assert_eq!(Context::default().convert(&x), y);
    }

    #[test]
    fn convert_decons_only_constants() {
        let mut ctx = Context::default();
        let ety = Type::enum_(
            Rc::new(GenericType::GenericEnum(EnumDef {
                tname: "ABC".to_string(),
                tvars: vec![],
                variants: vec![].into(),
            })),
            [
                ("A".to_string(), vec![]),
                ("B".to_string(), vec![]),
                ("C".to_string(), vec![]),
            ],
        );

        let x = TExp::decons(TExp::annotate(ety.clone(), "x"), "A", [] as [&str; 0], 1, 0);

        let y = LExp::switch(
            "x",
            vec![
                ConRep::Constant(0),
                ConRep::Constant(1),
                ConRep::Constant(2),
            ],
            vec![(Con::Data(ConRep::Constant(0)), LExp::Int(1))],
            Some(0),
        );

        assert_eq!(ctx.convert(&x), y);
    }

    #[test]
    fn convert_decons_tagged() {
        let mut ctx = Context::default();
        let ety = Type::enum_(
            Rc::new(GenericType::GenericEnum(EnumDef {
                tname: "ABC".to_string(),
                tvars: vec![],
                variants: vec![].into(),
            })),
            [
                ("A".to_string(), vec![]),
                ("B".to_string(), vec![Type::Int]),
                ("C".to_string(), vec![Type::Int, Type::Int]),
            ],
        );

        let x = TExp::decons(TExp::annotate(ety.clone(), "x"), "B", ["y"], "y", 0);
        let y = LExp::bind(
            "switch_val__0",
            "x",
            LExp::switch(
                "switch_val__0",
                vec![ConRep::Constant(0), ConRep::Tagged(0), ConRep::Tagged(1)],
                vec![(
                    Con::Data(ConRep::Tagged(0)),
                    LExp::bind("y", LExp::decon(ConRep::Tagged(0), "switch_val__0"), "y"),
                )],
                Some(0),
            ),
        );
        assert_eq!(ctx.convert(&x), y);

        let x = TExp::decons(TExp::annotate(ety.clone(), "x"), "C", ["y", "z"], 1, 0);
        let y = LExp::bind(
            "switch_val__1",
            "x",
            LExp::switch(
                "switch_val__1",
                vec![ConRep::Constant(0), ConRep::Tagged(0), ConRep::Tagged(1)],
                vec![(
                    Con::Data(ConRep::Tagged(1)),
                    LExp::bind(
                        "z",
                        LExp::select(1, LExp::decon(ConRep::Tagged(1), "switch_val__1")),
                        LExp::bind(
                            "y",
                            LExp::select(0, LExp::decon(ConRep::Tagged(1), "switch_val__1")),
                            1,
                        ),
                    ),
                )],
                Some(0),
            ),
        );
        assert_eq!(ctx.convert(&x), y);
    }

    #[test]
    fn convert_decons_transparent() {
        let mut ctx = Context::default();
        let ety = Type::enum_(
            Rc::new(GenericType::GenericEnum(EnumDef {
                tname: "Foo".to_string(),
                tvars: vec![],
                variants: vec![].into(),
            })),
            [("X".to_string(), vec![Type::Int])],
        );

        let x = TExp::decons(TExp::annotate(ety.clone(), "x"), "X", ["y"], "y", 0);
        let y = LExp::bind(
            "switch_val__0",
            "x",
            LExp::switch(
                "switch_val__0",
                vec![ConRep::Transparent],
                vec![(
                    Con::Data(ConRep::Transparent),
                    LExp::bind("y", LExp::decon(ConRep::Transparent, "switch_val__0"), "y"),
                )],
                Some(0),
            ),
        );
        assert_eq!(ctx.convert(&x), y);
    }

    #[test]
    fn convert_fndefs() {
        assert_eq!(
            Context::default().convert(&TExp::defs(
                [Def::inferred_func(
                    Type::func(Type::Int, Type::Int),
                    "fn",
                    "x",
                    "x"
                )],
                TExp::apply("fn", 123)
            )),
            LExp::from_str("(fix ((fn x x)) (fn 123))").unwrap()
        );
    }
}
