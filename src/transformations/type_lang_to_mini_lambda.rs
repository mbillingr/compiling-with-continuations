use crate::core::reference::Ref;
use crate::languages::common_primops::PrimOp;
use crate::languages::type_lang::ast::Type;

pub type LExp = crate::languages::mini_lambda::ast::Expr<Ref<str>>;
pub type TExp = crate::languages::type_lang::ast::Expr;

pub struct Context {}

impl Context {
    pub fn new() -> Self {
        Context {}
    }
}

impl Context {
    pub fn convert(&self, expr: &TExp) -> LExp {
        match expr {
            TExp::Int(x) => LExp::int(*x),
            TExp::Real(x) => LExp::real(*x),
            TExp::String(x) => LExp::string(x),
            TExp::Ref(x) => LExp::var(x),
            TExp::Apply(app) => LExp::apply(self.convert(&app.0), self.convert(&app.1)),
            TExp::Lambda(lam) => LExp::func(&lam.param, self.convert(&lam.body)),

            TExp::Add(_) => panic!("Unannotated add: {expr:?}"),

            TExp::Show(x) => match x.get_type() {
                Type::Int => LExp::apply(PrimOp::ShowInt, self.convert(x)),
                _ => todo!("{expr:?}"),
            },

            TExp::Annotation(ann) => match &**ann {
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

                _ => todo!("{expr:?}"),
            },

            _ => todo!("{expr:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn convert_constants() {
        assert_eq!(Context::new().convert(&TExp::int(42)), LExp::Int(42));
        assert_eq!(Context::new().convert(&TExp::real(3.14)), LExp::Real(3.14));
        assert_eq!(
            Context::new().convert(&TExp::string("foo")),
            LExp::from_str("\"foo\"").unwrap()
        );
    }

    #[test]
    fn convert_variable_reference() {
        assert_eq!(
            Context::new().convert(&TExp::var("x")),
            LExp::from_str("x").unwrap()
        );
    }

    #[test]
    fn convert_application() {
        assert_eq!(
            Context::new().convert(&TExp::apply("f", "x")),
            LExp::from_str("(f x)").unwrap()
        );
    }

    #[test]
    fn convert_lambda() {
        assert_eq!(
            Context::new().convert(&TExp::lambda("x", "x")),
            LExp::from_str("(fn x x)").unwrap()
        );
    }

    #[test]
    fn convert_add() {
        assert_eq!(
            Context::new().convert(&TExp::annotate(Type::Int, TExp::add(1, 2))),
            LExp::from_str("((primitive +) (record 1 2))").unwrap()
        );

        /*assert_eq!(
            Context::new().convert(&TExp::annotate(Type::Real, TExp::add(1.2, 2.2))),
            LExp::from_str("((primitive +) (record 1 2))").unwrap()
        );*/

        // no need to worry about this case, the type checker should prevent it!
        assert_eq!(
            Context::new().convert(&TExp::annotate(Type::Int, TExp::add(1, 2.0))),
            LExp::from_str("((primitive +) (record 1 2.0))").unwrap()
        );
    }

    #[test]
    fn convert_read() {
        assert_eq!(
            Context::new().convert(&TExp::annotate(Type::Int, TExp::Read())),
            LExp::from_str("((primitive read-int) (record))").unwrap()
        );
    }

    #[test]
    fn convert_show() {
        assert_eq!(
            Context::new().convert(&TExp::show(TExp::int(42))),
            LExp::from_str("((primitive show-int) 42)").unwrap()
        );

        assert_eq!(
            Context::new().convert(&TExp::show(TExp::annotate(Type::Int, TExp::add(1, 2)))),
            LExp::from_str("((primitive show-int) ((primitive +) (record 1 2)))").unwrap()
        );
    }

    #[test]
    fn convert_cons() {
        todo!()
    }

    #[test]
    fn convert_decons() {
        todo!()
    }

    #[test]
    fn convert_fndefs() {
        todo!()
    }
}
