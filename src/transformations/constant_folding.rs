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

            // Two different variables may or may not have the same value
            Expr::PrimOp(
                PrimOp::ISame | PrimOp::FSame | PrimOp::SSame,
                Ref([Value::Var(_), Value::Var(_)]),
                _,
                Ref([_, _]),
            ) => Transformed::Continue,

            Expr::PrimOp(
                PrimOp::ISame | PrimOp::FSame | PrimOp::SSame,
                Ref([_, _]),
                _,
                Ref([no, _]),
            ) => Transformed::Again((**no).clone()),

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
    fn fold_constant_comparison() {
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
    fn fold_comparison_over_same_variables() {
        let x = Expr::from_str("(primop = (x x) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(yes)").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), y);

        let x = Expr::from_str("(primop = (x y) () ((no) (yes)))").unwrap();
        assert_eq!(ConstantFolder.transform_expr(&x), x);
    }
}
