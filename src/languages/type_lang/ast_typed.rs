use crate::languages::type_lang::ast::{EnumDef, Lambda};
use crate::languages::type_lang::type_checker::GenericType;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::rc::Rc;

#[derive(Debug, PartialEq)]
pub enum TExpr {
    Int(i64),
    Real(f64),
    Ref(Type, String),
    Apply(Type, Rc<(Self, Self)>),
    Cons(Type, Rc<(String, Vec<Self>)>),
    Decons(Type, Rc<(Self, String, Vec<String>, Self, Self)>),
    Lambda(Type, Rc<Lambda<Self>>),
    Defs(Rc<(Vec<TDef>, Self)>),
    Add(Type, Rc<(Self, Self)>),
    Read(Type),
    Show(Rc<Self>),
}

#[derive(Debug, PartialEq)]
pub enum TDef {
    Func(TFnDef),
    Enum(EnumDef),
}

#[derive(Debug, PartialEq)]
pub struct TFnDef {
    pub fname: String,
    pub tvars: Vec<String>,
    pub param: String,
    pub ptype: Type,
    pub rtype: Type,
    pub body: TExpr,
}

#[derive(Clone)]
pub enum Type {
    Unit,
    Int,
    Real,
    Opaque(String),
    Var(usize),
    Fn(Rc<(Type, Type)>),
    Generic(Rc<dyn GenericType>),
    Enum(Rc<(String, HashMap<String, Vec<Type>>)>),
}

impl TExpr {
    pub fn get_type(&self) -> &Type {
        match self {
            TExpr::Int(_) => &Type::Int,
            TExpr::Real(_) => &Type::Real,
            TExpr::Ref(t, _) => t,
            TExpr::Apply(t, _) => t,
            TExpr::Cons(t, _) => t,
            TExpr::Decons(t, _) => t,
            TExpr::Lambda(t, _) => t,
            TExpr::Defs(d) => &d.1.get_type(),
            TExpr::Add(t, _) => t,
            TExpr::Read(t) => t,
            TExpr::Show(_) => &Type::Unit,
        }
    }
}

impl Debug for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Unit => write!(f, "<unit>"),
            Type::Int => write!(f, "Int"),
            Type::Real => write!(f, "Real"),
            Type::Opaque(name) => write!(f, "{name}"),
            Type::Var(nr) => write!(f, "'{nr}"),
            Type::Fn(sig) => write!(f, "({:?} -> {:?})", sig.0, sig.1),
            Type::Generic(g) => write!(f, "{g:?}"),
            Type::Enum(e) => write!(f, "<Enum {}>", e.0),
        }
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Unit, Type::Unit) => true,
            (Type::Int, Type::Int) => true,
            (Type::Real, Type::Real) => true,
            (Type::Opaque(a), Type::Opaque(b)) => a == b,
            (Type::Var(a), Type::Var(b)) => a == b,
            (Type::Fn(a), Type::Fn(b)) => a == b,
            _ => false,
        }
    }
}
