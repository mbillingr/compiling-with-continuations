use crate::core::reference::Ref;
use crate::languages::common_primops::PrimOp;
use crate::languages::cps_lang::ast::{Expr, Transform, Transformed, Value};

pub struct ConstantFolder;

impl<V: Clone + PartialEq, F: Clone + PartialEq> Transform<V, F> for ConstantFolder {
    fn visit_expr(&mut self, expr: &Expr<V, F>) -> Transformed<Expr<V, F>> {
        match expr {
            Expr::Switch(Value::Int(idx), cnts) => {
                Transformed::Again((*cnts[*idx as usize]).clone())
            }

            Expr::PrimOp(
                PrimOp::ISame | PrimOp::FSame | PrimOp::SSame,
                Ref([a, b]),
                _,
                Ref([_, yes]),
            ) if a == b => Transformed::Again((**yes).clone()),

            // Variables may have any value, so we can never know in advance if they are the same
            Expr::PrimOp(
                PrimOp::ISame | PrimOp::FSame | PrimOp::SSame,
                Ref([Value::Var(_), _] | [_, Value::Var(_)]),
                _,
                Ref([_, _]),
            ) => Transformed::Continue,

            Expr::PrimOp(
                PrimOp::ISame | PrimOp::FSame | PrimOp::SSame,
                Ref([_, _]),
                _,
                Ref([no, _]),
            ) => Transformed::Again((**no).clone()),

            Expr::PrimOp(PrimOp::ILess, Ref([Value::Int(a), Value::Int(b)]), _, Ref([no, yes])) => {
                if a < b {
                    Transformed::Again((**yes).clone())
                } else {
                    Transformed::Again((**no).clone())
                }
            }

            Expr::PrimOp(PrimOp::ILess, Ref([Value::Var(a), Value::Var(b)]), _, Ref([no, _]))
                if a == b =>
            {
                Transformed::Again((**no).clone())
            }

            Expr::PrimOp(
                PrimOp::IAdd,
                Ref([Value::Int(a), Value::Int(b)]),
                Ref([var]),
                Ref([cnt]),
            ) => Transformed::Again((**cnt).substitute_var(var, &Value::Int(*a + *b))),

            Expr::PrimOp(PrimOp::IAdd, Ref([Value::Int(0), x]), Ref([var]), Ref([cnt])) => {
                Transformed::Again((**cnt).substitute_var(var, x))
            }

            Expr::PrimOp(PrimOp::IAdd, Ref([x, Value::Int(0)]), Ref([var]), Ref([cnt])) => {
                Transformed::Again((**cnt).substitute_var(var, x))
            }

            Expr::PrimOp(
                PrimOp::ISub,
                Ref([Value::Int(a), Value::Int(b)]),
                Ref([var]),
                Ref([cnt]),
            ) => Transformed::Again((**cnt).substitute_var(var, &Value::Int(*a - *b))),

            Expr::PrimOp(PrimOp::ISub, Ref([x, Value::Int(0)]), Ref([var]), Ref([cnt])) => {
                Transformed::Again((**cnt).substitute_var(var, x))
            }

            Expr::PrimOp(
                PrimOp::IMul,
                Ref([Value::Int(a), Value::Int(b)]),
                Ref([var]),
                Ref([cnt]),
            ) => Transformed::Again((**cnt).substitute_var(var, &Value::Int(*a * *b))),

            Expr::PrimOp(PrimOp::IMul, Ref([x, Value::Int(1)]), Ref([var]), Ref([cnt])) => {
                Transformed::Again((**cnt).substitute_var(var, x))
            }

            Expr::PrimOp(PrimOp::IMul, Ref([Value::Int(1), x]), Ref([var]), Ref([cnt])) => {
                Transformed::Again((**cnt).substitute_var(var, x))
            }

            Expr::PrimOp(PrimOp::IMul, Ref([_, Value::Int(0)]), Ref([var]), Ref([cnt])) => {
                Transformed::Again((**cnt).substitute_var(var, &Value::Int(0)))
            }

            Expr::PrimOp(PrimOp::IMul, Ref([Value::Int(0), _]), Ref([var]), Ref([cnt])) => {
                Transformed::Again((**cnt).substitute_var(var, &Value::Int(0)))
            }

            Expr::PrimOp(
                PrimOp::IDiv,
                Ref([Value::Int(a), Value::Int(b)]),
                Ref([var]),
                Ref([cnt]),
            ) => Transformed::Again((**cnt).substitute_var(var, &Value::Int(*a / *b))),

            Expr::PrimOp(PrimOp::IDiv, Ref([x, Value::Int(1)]), Ref([var]), Ref([cnt])) => {
                Transformed::Again((**cnt).substitute_var(var, x))
            }

            _ => Transformed::Continue,
        }
    }

    fn visit_value(&mut self, _: &Value<V, F>) -> Transformed<Value<V, F>> {
        Transformed::Continue
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fold_switch_over_constant() {
        let x = Expr::from_str("(switch 1 (halt 10) (halt 20) (halt 30))").unwrap();
        let y = Expr::from_str("(halt 20)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);
    }

    #[test]
    fn fold_constant_equality() {
        let x = Expr::from_str("(primop = (0 0) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(yes)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop = (0 1) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(no)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop =f (0.0 0.0) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(yes)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop =f (1.0 0.1) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(no)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop =s (\"foo\" \"foo\") () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(yes)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop =s (\"foo\" \"bar\") () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(no)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);
    }

    #[test]
    fn fold_integer_comparison() {
        let x = Expr::from_str("(primop < (0 0) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(no)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop < (0 1) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(yes)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop < (x x) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(no)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop < (x y) () ((no) (yes)))").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), x);

        let x = Expr::from_str("(primop < (0 x) () ((no) (yes)))").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), x);

        let x = Expr::from_str("(primop < (x 0) () ((no) (yes)))").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), x);
    }

    #[test]
    fn fold_comparison_over_variables() {
        let x = Expr::from_str("(primop = (x x) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(yes)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop = (x y) () ((no) (yes)))").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), x);

        let x = Expr::from_str("(primop = (x 0) () ((no) (yes)))").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), x);

        let x = Expr::from_str("(primop = (0 x) () ((no) (yes)))").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), x);
    }

    #[test]
    fn fold_integer_arithmetic() {
        let x = Expr::from_str("(primop + (1 2) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt 3)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop - (2 1) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt 1)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop * (2 2) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt 4)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop / (6 2) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt 3)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop + (0 x) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt x)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop + (x 0) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt x)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop - (x 0) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt x)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop * (x 1) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt x)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop * (1 x) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt x)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop / (x 1) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt x)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop * (x 0) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt 0)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop * (0 x) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt 0)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        // fold-cascade
        let x = Expr::from_str("(primop + (1 2) (y) ((primop + (y y) (z) ((halt z)))))").unwrap();
        let y = Expr::from_str("(halt 6)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);
    }
}
