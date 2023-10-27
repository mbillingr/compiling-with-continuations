use crate::core::ptr_tagging::make_tag;
use crate::core::reference::Ref;
use crate::languages::common_primops::PrimOp;
use crate::languages::cps_lang::ast as cps;
use crate::languages::cps_lang::ast::AccessPath;
use crate::languages::mini_lambda::ast;
use crate::languages::mini_lambda::ast::{Con, ConRep};
use crate::list;
use crate::transformations::GensymContext;

type LExpr = ast::Expr<Ref<str>>;
type CExpr = cps::Expr<Ref<str>>;
type CVal = cps::Value<Ref<str>>;

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
    pub fn convert(&'static self, expr: &LExpr, c: Box<dyn FnOnce(CVal) -> CExpr>) -> CExpr {
        match expr {
            LExpr::Var(v) => c(CVal::Var(*v)),
            LExpr::Int(i) => c(CVal::Int(*i)),
            LExpr::Real(r) => c(CVal::Real(*r)),
            LExpr::String(s) => c(CVal::String(*s)),

            LExpr::Fn(var, body) => {
                let f = self.gs.gensym("lambda");
                let k = self.gs.gensym("k");
                CExpr::Fix(
                    list![(
                        f,
                        list![k, *var],
                        Ref::new(
                            self.convert(
                                body,
                                Box::new(move |z| CExpr::App(CVal::Var(k), list![z]))
                            )
                        )
                    )],
                    Ref::new(c(CVal::Var(f))),
                )
            }

            LExpr::Fix(fnames, funcs, body) => {
                CExpr::Fix(self.g(*fnames, *funcs), Ref::new(self.convert(body, c)))
            }

            LExpr::Record(fields) if fields.len() == 0 => c(CVal::Int(0)),

            LExpr::Record(fields) => {
                let x = self.gs.gensym("r");
                self.convert_sequence(*fields, move |a| {
                    CExpr::Record(
                        Ref::array(
                            a.into_iter()
                                .map(|v| (v.clone(), AccessPath::Ref(0)))
                                .collect(),
                        ),
                        x,
                        Ref::new(c(CVal::Var(x))),
                    )
                })
            }

            LExpr::Select(idx, rec) => {
                let idx = *idx;
                let w = self.gs.gensym("w");
                self.convert(
                    rec,
                    Box::new(move |v| CExpr::Select(idx, v, w, Ref::new(c(CVal::Var(w))))),
                )
            }

            LExpr::App(Ref(LExpr::Prim(PrimOp::CallCC)), arg) => {
                let k = self.gs.gensym("k");
                let x = self.gs.gensym("x");
                CExpr::Fix(
                    list![(k, list![x], Ref::new(c(CVal::Var(x))))],
                    Ref::new(self.convert(
                        arg,
                        Box::new(move |f| CExpr::App(f, list![CVal::Var(k), CVal::Var(k)])),
                    )),
                )
            }

            LExpr::App(Ref(LExpr::Prim(PrimOp::Throw)), Ref(LExpr::Record(args))) => self.convert(
                &args[0],
                Box::new(|k| self.convert(&args[1], Box::new(|v| CExpr::App(k, list![v])))),
            ),

            LExpr::App(Ref(LExpr::Prim(op)), arg) if op.n_args() == 1 && op.is_branching() => {
                let k = self.gs.gensym("k");
                let x = self.gs.gensym("x");
                self.convert(
                    arg,
                    Box::new(move |v| {
                        CExpr::Fix(
                            list![(k, list![x], Ref::new(c(CVal::Var(x))))],
                            Ref::new(CExpr::PrimOp(
                                *op,
                                list![v],
                                list![],
                                list![
                                    Ref::new(CExpr::App(CVal::Var(k), list![CVal::Int(0)],)),
                                    Ref::new(CExpr::App(CVal::Var(k), list![CVal::Int(1)],)),
                                ],
                            )),
                        )
                    }),
                )
            }

            LExpr::App(Ref(LExpr::Prim(op)), arg) if op.n_args() == 1 && op.n_results() == 0 => {
                self.convert(
                    arg,
                    Box::new(move |v| {
                        CExpr::PrimOp(*op, list![v], list![], list![Ref::new(c(CVal::Int(0)))])
                    }),
                )
            }

            LExpr::App(Ref(LExpr::Prim(op)), arg) if op.n_args() == 1 => {
                let w = self.gs.gensym("w");
                self.convert(
                    arg,
                    Box::new(move |v| {
                        CExpr::PrimOp(*op, list![v], list![w], list![Ref::new(c(CVal::Var(w)))])
                    }),
                )
            }

            LExpr::App(Ref(LExpr::Prim(op)), Ref(LExpr::Record(arg)))
                if op.n_args() > 1 && op.is_branching() =>
            {
                let k = self.gs.gensym("k");
                let x = self.gs.gensym("x");
                self.convert_sequence(*arg, move |a| {
                    CExpr::Fix(
                        list![(k, list![x], Ref::new(c(CVal::Var(x))))],
                        Ref::new(CExpr::PrimOp(
                            *op,
                            a,
                            list![],
                            list![
                                Ref::new(CExpr::App(CVal::Var(k), list![CVal::Int(0)])),
                                Ref::new(CExpr::App(CVal::Var(k), list![CVal::Int(1)])),
                            ],
                        )),
                    )
                })
            }

            LExpr::App(Ref(LExpr::Prim(op)), Ref(LExpr::Record(arg)))
                if op.n_args() > 1 && op.n_results() == 0 =>
            {
                self.convert_sequence(*arg, move |a| {
                    CExpr::PrimOp(*op, a, list![], list![Ref::new(c(CVal::Int(0)))])
                })
            }

            LExpr::App(Ref(LExpr::Prim(op)), Ref(LExpr::Record(arg))) if op.n_args() > 1 => {
                let w = self.gs.gensym("w");
                self.convert_sequence(*arg, move |a| {
                    CExpr::PrimOp(*op, a, list![w], list![Ref::new(c(CVal::Var(w)))])
                })
            }

            LExpr::App(f, e) => {
                let e = *e;
                let r = self.gs.gensym("ret");
                let x = self.gs.gensym("val");
                CExpr::Fix(
                    list![(r, list![x], Ref::new(c(CVal::Var(x))))],
                    Ref::new(self.convert(
                        f,
                        Box::new(move |fv| {
                            self.convert(
                                &e,
                                Box::new(move |ev| CExpr::App(fv, list![CVal::Var(r), ev])),
                            )
                        }),
                    )),
                )
            }

            LExpr::Prim(op) if op.n_args() == 1 => {
                let x = self.gs.gensym("x");
                self.convert(
                    &LExpr::Fn(
                        x,
                        Ref::new(LExpr::App(LExpr::Prim(*op).into(), LExpr::Var(x).into())),
                    ),
                    c,
                )
            }

            LExpr::Prim(op) => {
                let r = self.gs.gensym("r");
                let args = (0..op.n_args())
                    .map(|i| LExpr::Select(i as isize, LExpr::Var(r).into()))
                    .collect();
                self.convert(
                    &LExpr::Fn(
                        r,
                        Ref::new(LExpr::App(
                            LExpr::Prim(*op).into(),
                            LExpr::Record(Ref::array(args)).into(),
                        )),
                    ),
                    c,
                )
            }

            LExpr::Con(ConRep::Constant(ctag), _) => {
                self.convert(&LExpr::Int(make_tag(*ctag) as i64), c)
            }
            LExpr::Con(ConRep::Tagged(tag), x) => self.convert(
                &LExpr::Record(list![(**x).clone(), LExpr::Int(*tag as i64)]),
                c,
            ),
            LExpr::Con(ConRep::Transparent, x) => self.convert(&*x, c),

            LExpr::DeCon(ConRep::Constant(_), _) => panic!("attempt to decon a constant"),
            LExpr::DeCon(ConRep::Tagged(_), r) => self.convert(&LExpr::Select(0, *r), c),
            LExpr::DeCon(ConRep::Transparent, x) => self.convert(x, c),

            LExpr::Switch(cond, conreps, arms, default) => {
                let mut matches_transparent = false;
                let mut matches_constant = false;
                let mut matches_tagged = false;
                for arm in arms.iter() {
                    match arm.0 {
                        Con::Data(ConRep::Transparent) => matches_transparent = true,
                        Con::Data(ConRep::Constant(_)) => matches_constant = true,
                        Con::Data(ConRep::Tagged(_)) => matches_tagged = true,
                        _ => {}
                    }
                }

                if matches_transparent && (matches_constant || matches_tagged) {
                    panic!("Invalid match: Transparent cannot be combined with other cases.")
                }

                let arms = *arms;
                let default = default
                    .unwrap_or_else(|| Ref::new(LExpr::Panic("unspecified default case".into())));
                let k = self.gs.gensym("k");
                let x = self.gs.gensym("x");
                let f = self.gs.gensym("f");
                let z = self.gs.gensym("z");
                let default_cont = self.convert(
                    &default,
                    Box::new(move |z| CExpr::App(CVal::Var(k), list![z])),
                );

                let actual_switch = if matches_constant && matches_tagged {
                    let default_cont = Ref::new(default_cont);
                    CExpr::PrimOp(
                        PrimOp::CorP,
                        list![CVal::Var(z)],
                        list![],
                        list![
                            self.convert_switch_const_table(conreps, arms, k, z, default_cont)
                                .into(),
                            self.convert_switch_tag_table(conreps, arms, k, z, default_cont)
                                .into()
                        ],
                    )
                } else if matches_constant {
                    self.convert_switch_const_table(conreps, arms, k, z, Ref::new(default_cont))
                } else if matches_tagged {
                    self.convert_switch_tag_table(conreps, arms, k, z, Ref::new(default_cont))
                } else {
                    self.convert_switch_linear(CVal::Var(z), arms, default_cont, CVal::Var(k))
                };
                CExpr::Fix(
                    list![
                        (k, list![x], Ref::new(c(CVal::Var(x)))),
                        (f, list![z], Ref::new(actual_switch))
                    ],
                    Ref::new(
                        self.convert(cond, Box::new(move |z| CExpr::App(CVal::Var(f), list![z]))),
                    ),
                )
            }

            LExpr::Panic(msg) => CExpr::Panic(*msg),

            LExpr::ShowInt(value) | LExpr::ShowReal(value) | LExpr::ShowStr(value) => todo!(),
        }
    }

    fn convert_switch_const_table(
        &'static self,
        conreps: &Ref<[ConRep]>,
        arms: Ref<[(Con, LExpr)]>,
        k: Ref<str>,
        z: Ref<str>,
        default_cont: Ref<CExpr>,
    ) -> CExpr {
        let t = self.gs.gensym("t");
        CExpr::PrimOp(
            PrimOp::Untag,
            list![CVal::Var(z)],
            list![t],
            list![Ref::new(self.convert_switch_table(
                CVal::Var(t),
                Self::max_const_idx(conreps),
                arms,
                default_cont,
                CVal::Var(k),
                true,
                false,
            ))],
        )
    }

    fn convert_switch_tag_table(
        &'static self,
        conreps: &Ref<[ConRep]>,
        arms: Ref<[(Con, LExpr)]>,
        k: Ref<str>,
        z: Ref<str>,
        default_cont: Ref<CExpr>,
    ) -> CExpr {
        let t = self.gs.gensym("t");
        CExpr::Select(
            1,
            CVal::Var(z),
            t,
            Ref::new(self.convert_switch_table(
                CVal::Var(t),
                Self::max_tag_idx(conreps),
                arms,
                default_cont,
                CVal::Var(k),
                false,
                true,
            )),
        )
    }

    fn max_const_idx(conreps: &Ref<[ConRep]>) -> usize {
        let max_idx = conreps
            .iter()
            .filter_map(|cr| match cr {
                ConRep::Constant(i) => Some(*i),
                _ => None,
            })
            .max()
            .unwrap();
        max_idx
    }

    fn max_tag_idx(conreps: &Ref<[ConRep]>) -> usize {
        let max_idx = conreps
            .iter()
            .filter_map(|cr| match cr {
                ConRep::Tagged(i) => Some(*i),
                _ => None,
            })
            .max()
            .unwrap();
        max_idx
    }

    fn convert_switch_table(
        &'static self,
        condval: CVal,
        max_idx: usize,
        arms: Ref<[(Con, LExpr)]>,
        default: Ref<CExpr>,
        return_cont: CVal,
        use_const: bool,
        use_tags: bool,
    ) -> CExpr {
        let mut branches = vec![default; max_idx + 1];
        // Iterating over arms in reverse order so that in case of duplicates the first takes
        // precedence. This makes the behavior consistent with the interpreter.
        for (check, br) in arms.iter().rev() {
            let idx = match check {
                Con::Int(i) => *i as usize,
                Con::Data(ConRep::Constant(i)) if use_const => *i,
                Con::Data(ConRep::Tagged(i)) if use_tags => *i,
                _ => continue,
            };
            let rc = return_cont.clone();
            branches[idx] = Ref::new(self.convert(br, Box::new(move |z| CExpr::App(rc, list![z]))));
        }
        CExpr::Switch(condval, Ref::array(branches))
    }

    fn convert_switch_linear(
        &'static self,
        condval: CVal,
        arms: Ref<[(Con, LExpr)]>,
        default: CExpr,
        return_cont: CVal,
    ) -> CExpr {
        if arms.is_empty() {
            return default;
        }
        let (test, branch) = &arms[0];

        let else_cont = self.convert_switch_linear(
            condval.clone(),
            Ref::slice(&arms.as_ref()[1..]),
            default,
            return_cont.clone(),
        );

        let then_cont = self.convert(branch, Box::new(move |z| CExpr::App(return_cont, list![z])));
        match test {
            Con::Data(ConRep::Transparent) => then_cont,
            Con::Data(ConRep::Constant(ctag)) => CExpr::PrimOp(
                PrimOp::ISame,
                list![condval, CVal::Int(make_tag(*ctag) as i64)],
                list![],
                list![Ref::new(else_cont), Ref::new(then_cont)],
            ),
            Con::Data(ConRep::Tagged(tag)) => {
                let t = self.gs.gensym("t");
                CExpr::Select(
                    1,
                    condval,
                    t,
                    Ref::new(CExpr::PrimOp(
                        PrimOp::ISame,
                        list![CVal::Var(t), CVal::Int(*tag as i64)],
                        list![],
                        list![Ref::new(else_cont), Ref::new(then_cont)],
                    )),
                )
            }
            Con::Int(i) => CExpr::PrimOp(
                PrimOp::ISame,
                list![condval, CVal::Int(*i)],
                list![],
                list![Ref::new(else_cont), Ref::new(then_cont)],
            ),
            Con::Real(f) => CExpr::PrimOp(
                PrimOp::FSame,
                list![condval, CVal::Real(*f)],
                list![],
                list![Ref::new(else_cont), Ref::new(then_cont)],
            ),
            Con::String(s) => CExpr::PrimOp(
                PrimOp::SSame,
                list![condval, CVal::String(s.to_string().into())],
                list![],
                list![Ref::new(else_cont), Ref::new(then_cont)],
            ),
        }
    }

    fn convert_sequence(
        &'static self,
        items: Ref<[LExpr]>,
        c: impl 'static + FnOnce(Ref<[CVal]>) -> CExpr,
    ) -> CExpr {
        self.convert_sequence_recursion(items, Vec::with_capacity(items.len()), Box::new(c))
    }

    fn convert_sequence_recursion(
        &'static self,
        items: Ref<[LExpr]>,
        mut w: Vec<CVal>,
        c: Box<dyn FnOnce(Ref<[CVal]>) -> CExpr>,
    ) -> CExpr {
        if items.is_empty() {
            c(Ref::array(w))
        } else {
            self.convert(
                &items[0],
                Box::new(move |v| {
                    w.push(v);
                    self.convert_sequence_recursion(Ref::slice(&items.as_ref()[1..]), w, c)
                }),
            )
        }
    }

    fn g(
        &'static self,
        fnames: Ref<[Ref<str>]>,
        funcs: Ref<[LExpr]>,
    ) -> Ref<[(Ref<str>, Ref<[Ref<str>]>, Ref<CExpr>)]> {
        Ref::array(
            fnames
                .into_iter()
                .zip(funcs.into_iter())
                .map(|(h1, f)| match f {
                    LExpr::Fn(v, b) => {
                        let w = self.gs.gensym("w");
                        (
                            *h1,
                            list![w, *v],
                            Ref::new(
                                self.convert(
                                    b,
                                    Box::new(move |z| CExpr::App(CVal::Var(w), list![z])),
                                ),
                            ),
                        )
                    }
                    _ => panic!("Invalid function {:?}", f),
                })
                .collect(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    use crate::core::answer::Answer;
    use crate::languages::cps_lang;
    use crate::{
        cps_expr, cps_expr_list, cps_field, cps_field_list, cps_ident_list, cps_value,
        cps_value_list, make_testsuite_for_mini_lambda, mini_expr,
    };

    pub fn convert_program(expr: LExpr) -> CExpr {
        // for testing we need to generate symbols that are valid rust identifiers
        let ctx = Box::leak(Box::new(Context::new("__".to_string())));
        ctx.convert(&expr, Box::new(|x| CExpr::Halt(x)))
    }

    #[test]
    fn convert_variable() {
        assert_eq!(convert_program(mini_expr!(foo)), cps_expr!(halt foo));
    }

    #[test]
    fn convert_constants() {
        assert_eq!(
            convert_program(mini_expr!((int 0))),
            cps_expr!(halt (int 0))
        );
        assert_eq!(
            convert_program(mini_expr!((real 0.0))),
            cps_expr!(halt (real 0.0))
        );
        assert_eq!(
            convert_program(mini_expr!((str "foo"))),
            cps_expr!(halt (str "foo"))
        );
    }

    #[test]
    fn convert_records() {
        assert_eq!(convert_program(mini_expr!([])), cps_expr!(halt (int 0)));
        assert_eq!(
            convert_program(mini_expr!([(int 1)])),
            cps_expr!(record [(int 1)] r__0 (halt r__0))
        );
        assert_eq!(
            convert_program(mini_expr!([(int 1) x (int 3)])),
            cps_expr!(record [(int 1) x (int 3)] r__0 (halt r__0))
        );
        assert_eq!(
            convert_program(mini_expr!([[(int 1)]])),
            cps_expr!(record [(int 1)] r__1 (record [r__1] r__0 (halt r__0)))
        );
        assert_eq!(
            convert_program(mini_expr!([[(int 1)] [(int 2)]])),
            cps_expr!(record [(int 1)] r__1 (record [(int 2)] r__2 (record [r__1 r__2] r__0 (halt r__0))))
        );
    }

    #[test]
    fn convert_select() {
        assert_eq!(
            convert_program(mini_expr!(select [(int 1)] 0)),
            cps_expr!(record [(int 1)] r__1 (select 0 r__1 w__0 (halt w__0)))
        );
    }

    #[test]
    fn convert_unary_primops() {
        assert_eq!(
            convert_program(mini_expr!(ineg int 1)),
            cps_expr!(- (int 1) [w__0] [(halt w__0)])
        );

        // mini_expr!(ineg) --> mini_expr!(fun x__0 = (ineg x__0))
        assert_eq!(
            convert_program(mini_expr!(ineg)),
            cps_expr!(fix lambda__1(k__2 x__0)=(- x__0 [w__3] [(k__2 w__3)]) in (halt lambda__1))
        );

        assert_eq!(
            convert_program(mini_expr!(is_zero)),
            cps_expr!(
                fix lambda__1(k__2 x__0)=(fix k__3(x__4)=(k__2 x__4)
                                     in (is_zero x__0 [] [(k__3 (int 0)) (k__3 (int 1))]))
                in (halt lambda__1))
        );
    }

    #[test]
    fn convert_nary_primops() {
        assert_eq!(
            convert_program(mini_expr!(- [(int 2) (int 3)])),
            cps_expr!(- [(int 2) (int 3)] [w__0] [(halt w__0)])
        );

        assert_eq!(
            convert_program(mini_expr!(-)),
            cps_expr!(fix lambda__1(k__2 r__0)=
                (select 0 r__0 w__4
                    (select 1 r__0 w__5
                        (- [w__4 w__5] [w__3] [(k__2 w__3)])))
                in (halt lambda__1))
        );

        assert_eq!(
            convert_program(mini_expr!(=)),
            cps_expr!(fix lambda__1(k__2 r__0)=
                (select 0 r__0 w__5
                    (select 1 r__0 w__6
                        (fix k__3(x__4)=(k__2 x__4)
                        in
                            (= [w__5 w__6] [] [(k__3 (int 0)) (k__3 (int 1))]))))
                in (halt lambda__1))
        );
    }

    #[test]
    fn convert_side_effect_primops() {
        assert_eq!(
            convert_program(mini_expr!(set [(box (int 2)) (int 3)])),
            cps_expr!(box (int 2) [w__0] [(set [w__0 (int 3)] [] [(halt (int 0))])])
        );
    }

    #[test]
    fn convert_branching_primops() {
        assert_eq!(
            convert_program(mini_expr!(is_zero int 2)),
            cps_expr!(fix k__0(x__1)=(halt x__1) in (is_zero (int 2) [] [(k__0 (int 0)) (k__0 (int 1))]))
        );
        assert_eq!(
            convert_program(mini_expr!(= [(int 2) (int 3)])),
            cps_expr!(fix k__0(x__1)=(halt x__1) in (= [(int 2) (int 3)] [] [(k__0 (int 0)) (k__0 (int 1))]))
        );
    }

    #[test]
    fn function_definition() {
        assert_eq!(
            convert_program(mini_expr!(fun x = x)),
            cps_expr!(fix lambda__0(k__1 x)=(k__1 x) in (halt lambda__0))
        )
    }

    #[test]
    fn application() {
        assert_eq!(
            convert_program(mini_expr!(f e)),
            cps_expr!(fix ret__0(val__1)=(halt val__1) in (f ret__0 e))
        )
    }

    #[test]
    fn mutual_recursion() {
        assert_eq!(
            convert_program(mini_expr!(fix fun foo x = (bar x) fun bar y = y in z)),
            cps_expr!(
                fix foo(w__0 x)=(fix ret__1(val__2)=(w__0 val__2)
                                 in (bar ret__1 x));
                    bar(w__3 y)=(w__3 y)
                in (halt z))
        )
    }

    #[test]
    fn data_constructors() {
        assert_eq!(
            convert_program(mini_expr!(con (const 7))),
            cps_expr!(halt (int 15)) // 7 represented to be distinguishable from ptrs
        );
        assert_eq!(
            convert_program(mini_expr!(con (tag 5) real 99.9)),
            cps_expr!(record [(real 99.9) (int 5)] r__0 (halt r__0))
        );
        assert_eq!(
            convert_program(mini_expr!(con transparent real 99.9)),
            cps_expr!(halt (real 99.9))
        );
    }

    #[test]
    fn data_deconstrutors() {
        assert_eq!(
            convert_program(mini_expr!(decon (tag 3) r)),
            cps_expr!(select 0 r w__0 (halt w__0))
        );
        assert_eq!(
            convert_program(mini_expr!(decon transparent x)),
            cps_expr!(halt x)
        );
    }

    #[test]
    fn switch_over_int() {
        assert_eq!(
            convert_program(mini_expr!(switch foo [] [] (int 1))),
            cps_expr!(fix 
                k__0(x__1)=(halt x__1);
                f__2(z__3)=(k__0 (int 1))
            in (f__2 foo))
        );

        assert_eq!(
            convert_program(mini_expr!(switch foo [] [(int 0) => (int 2)] (int 1))),
            // k__0 is the continuation "after" the switch; all arms pass their results to it.
            // f__2 is the continuation where the value of foo is bound to z__3, so we only evaluate it once.
            cps_expr!(fix 
                k__0(x__1)=(halt x__1);
                f__2(z__3)=(= [z__3 (int 0)] [] [(k__0 (int 1)) (k__0 (int 2))])
            in (f__2 foo))
        );

        assert_eq!(
            convert_program(
                mini_expr!(switch foo [] [(int 0) => (int 2); (int 7) => (int 3)] (int 1))
            ),
            cps_expr!(fix
                k__0(x__1)=(halt x__1);
                f__2(z__3)=(= [z__3 (int 0)] [] [(= [z__3 (int 7)] [] [(k__0 (int 1)) (k__0 (int 3))]) (k__0 (int 2))])
            in (f__2 foo))
        );
    }

    #[test]
    fn switch_over_real() {
        assert_eq!(
            convert_program(mini_expr!(switch foo [] [(real 0.0) => (int 2)] (int 1))),
            cps_expr!(fix
                k__0(x__1)=(halt x__1);
                f__2(z__3)=(fsame [z__3 (real 0.0)] [] [(k__0 (int 1)) (k__0 (int 2))])
            in (f__2 foo))
        );
    }

    #[test]
    fn switch_over_strings() {
        assert_eq!(
            convert_program(mini_expr!(switch foo [] [(str "bla") => (int 2)] (int 1))),
            cps_expr!(fix
                k__0(x__1)=(halt x__1);
                f__2(z__3)=(ssame [z__3 (str "bla")] [] [(k__0 (int 1)) (k__0 (int 2))])
            in (f__2 foo))
        );
    }

    #[test]
    fn switch_over_datatypes() {
        assert_eq!(
            convert_program(mini_expr!(switch foo [transparent] [transparent => (int 2)] (int 1))),
            cps_expr!(fix
                k__0(x__1)=(halt x__1);
                f__2(z__3)=(k__0 (int 2))
            in (f__2 foo))
        );

        assert_eq!(
            convert_program(
                mini_expr!(switch foo [(const 0) (const 1) (const 2)] [(const 1) => (int 2)] (int 1))
            ),
            cps_expr!(fix
                k__0(x__1)=(halt x__1);
                f__2(z__3)=(untag z__3 t__4 (switch t__4 [(k__0 (int 1)) (k__0 (int 2)) (k__0 (int 1))]))
            in (f__2 foo))
        );

        assert_eq!(
            convert_program(mini_expr!(switch foo [(tag 0) (tag 1)] [(tag 0) => (int 2)] (int 1))),
            cps_expr!(fix
                k__0(x__1)=(halt x__1);
                f__2(z__3)=(select 1 z__3 t__4 (switch t__4 [(k__0 (int 2)) (k__0 (int 1))]))
            in (f__2 foo))
        );

        assert_eq!(
            convert_program(mini_expr!(switch foo [(const 0) (tag 0) (tag 1) (const 1)]
                [(tag 0) => (int 2);
                (const 0) => (int 3)]
                (int 1))),
            cps_expr!(fix
                k__0(x__1)=(halt x__1);
                f__2(z__3)=(const_or_ptr z__3 [] [
                    (untag z__3 t__4 (switch t__4 [(k__0 (int 3)) (k__0 (int 1))]))
                    (select 1 z__3 t__5 (switch t__5 [(k__0 (int 2)) (k__0 (int 1))]))])
            in (f__2 foo))
        );
    }

    #[test]
    fn continuation_manipulation() {
        assert_eq!(
            convert_program(mini_expr!(callcc (fun k = (int 42)))),
            cps_expr!(
                fix k__0(x__1)=(halt x__1)
                in (fix lambda__2(k__3 k)=(k__3 (int 42))
                    in (lambda__2 k__0 k__0)))
        );

        assert_eq!(
            convert_program(mini_expr!(throw [k (int 123)])),
            cps_expr!(
                (k (int 123))
            )
        );
    }

    unsafe fn run_in_cps(mini_lambda_expr: &LExpr, out: impl Write) -> Answer {
        let cps_expr = convert_program(mini_lambda_expr.clone());
        cps_lang::interpreter::exec(&cps_expr)
    }

    make_testsuite_for_mini_lambda!(run_in_cps continuation_tests);
}
