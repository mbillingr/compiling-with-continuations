use crate::core::reference::Ref;
use sexpr_parser::SexprFactory;

#[derive(Debug, Clone, PartialEq)]
pub enum S {
    Int(i64),
    Float(f64),
    Symbol(Ref<str>),
    String(Ref<String>),
    List(Ref<[S]>),
}

pub struct SF;

impl SexprFactory for SF {
    type Sexpr = S;
    type Integer = i64;
    type Float = f64;

    fn int(&mut self, x: i64) -> S {
        S::Int(x)
    }

    fn float(&mut self, x: f64) -> Self::Sexpr {
        S::Float(x)
    }

    fn symbol(&mut self, x: &str) -> Self::Sexpr {
        S::Symbol(x.to_string().into())
    }

    fn string(&mut self, x: &str) -> Self::Sexpr {
        S::String(x.to_string().into())
    }

    fn list(&mut self, x: Vec<Self::Sexpr>) -> Self::Sexpr {
        S::List(Ref::array(x))
    }

    fn pair(&mut self, _: Self::Sexpr, _: Self::Sexpr) -> Self::Sexpr {
        unimplemented!()
    }
}
