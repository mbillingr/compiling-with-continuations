/*!
Defines the possible kinds of types.
Kinds play the same role for types, as types do for values.
!*/

use std::fmt::Formatter;
use std::rc::Rc;

/// The kind of a type
#[derive(Clone, PartialEq)]
pub enum Kind {
    /// The kind of simple (nullary) types such as `Int` or `Int -> Bool`.
    Star,

    /// The kind of type constructors such as `List t`.
    Kfun(Rc<(Kind, Kind)>),
}

impl std::fmt::Debug for Kind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::Star => write!(f, "*"),
            Kind::Kfun(rc) => {
                let (a, b) = &**rc;
                match a {
                    Kind::Star => write!(f, "{a:?}->{b:?}"),
                    _ => write!(f, "({a:?})->{b:?}"),
                }
            }
        }
    }
}

impl Kind {
    pub fn kfun(a: Kind, b: Kind) -> Kind {
        Kind::Kfun(Rc::new((a, b)))
    }
}

pub trait HasKind {
    fn kind(&self) -> super::Result<&Kind>;
}
