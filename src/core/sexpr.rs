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

impl S {
    pub fn symbol(s: &'static str) -> Self {
        S::Symbol(Ref(s))
    }
    pub fn list(elems: Vec<S>) -> Self {
        S::List(Ref::array(elems))
    }

    pub fn replace_head(&self, new_head: S) -> Self {
        match self {
            S::List(elems) => {
                let mut es: Vec<_> = elems.iter().cloned().collect();
                if es.is_empty() {
                    new_head
                } else {
                    es[0] = new_head;
                    S::List(Ref::array(es))
                }
            }
            _ => panic!("not a list"),
        }
    }

    pub fn try_symbol(&self) -> Option<Ref<str>> {
        match self {
            S::Symbol(s) => Some(*s),
            _ => None,
        }
    }
}

impl From<Ref<str>> for S {
    fn from(value: Ref<str>) -> Self {
        S::Symbol(value)
    }
}

impl From<usize> for S {
    fn from(value: usize) -> Self {
        S::Int(value as i64)
    }
}

impl std::fmt::Display for S {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            S::Int(v) => write!(f, "{}", v),
            S::Float(v) => write!(f, "{}", v),
            S::Symbol(s) => write!(f, "{}", s),
            S::String(s) => write!(f, "{:?}", s),
            S::List(elems) => {
                write!(f, "(")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", e)?;
                }
                write!(f, ")")
            }
        }
    }
}
