/*!
Types
!*/
use super::kinds::{HasKind, Kind};
use super::{Id, Int, Result};
use std::fmt::{Debug, Formatter};
use std::rc::Rc;

/// The type of a value
#[derive(Clone, PartialEq)]
pub enum Type {
    /// A type variable
    TVar(Tyvar),

    /// A type constant
    TCon(Tycon),

    /// A type application (applying a type of kind `k1` to a type of
    /// kind `k1 -> k2` results in a type of kind `k2`.)
    TApp(Rc<(Self, Self)>),

    /// A generic (quantified) type variable
    TGen(Int),
}

impl Debug for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::TVar(tv) => write!(f, "{}", tv.0),
            Type::TCon(tc) => write!(f, "{}", tc.0),
            Type::TApp(rc) => write!(f, "({:?} {:?})", rc.0, rc.1),
            Type::TGen(k) => write!(f, "'{k}"),
        }
    }
}

/// A type variable
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Tyvar(pub Id, pub Kind);

/// A type constant
#[derive(Clone, Debug, PartialEq)]
pub struct Tycon(pub Id, pub Kind);

impl Type {
    /// construct a type application (convenience method)
    pub fn tapp(a: Type, b: Type) -> Type {
        Type::TApp(Rc::new((a, b)))
    }

    pub fn tcon(tcon: impl Into<Id>) -> Self {
        Type::TCon(Tycon(tcon.into(), Kind::Star))
    }

    pub fn tvar(name: impl Into<Id>, kind: impl Into<Kind>) -> Self {
        Type::TVar(Tyvar::new(name, kind))
    }
}

impl Tyvar {
    pub fn new(name: impl Into<Id>, kind: impl Into<Kind>) -> Self {
        Tyvar(name.into(), kind.into())
    }
}

impl HasKind for Tyvar {
    fn kind(&self) -> Result<&Kind> {
        Ok(&self.1)
    }
}

impl HasKind for Tycon {
    fn kind(&self) -> Result<&Kind> {
        Ok(&self.1)
    }
}

impl HasKind for Type {
    fn kind(&self) -> Result<&Kind> {
        match self {
            Type::TCon(tc) => tc.kind(),
            Type::TVar(u) => u.kind(),
            Type::TApp(app) => match app.0.kind()? {
                Kind::Kfun(kf) => Ok(&kf.1),
                _ => Err("Invalid Kind in TApp")?,
            },
            Type::TGen(_) => panic!("Don't know what to do :(   (maybe ignore somehow?)"),
        }
    }
}
