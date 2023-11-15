use crate::languages::type_lang::type_checker::GenericType;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::rc::Rc;

/// Nodes of the abstract syntax tree
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    /// Integer constant
    Int(i64),

    /// Real constant
    Real(f64),

    /// String constant
    String(String),

    /// Variable reference
    Ref(String),

    /// Function application
    Apply(Rc<(Self, Self)>),

    /// Tuple construction
    Record(Rc<Vec<Self>>),

    /// Enum variant construction
    Cons(Rc<(String, String, Vec<Self>)>),

    /// Enum deconstruction (will be replaced by pattern matching)
    Decons(Rc<(Self, String, Vec<String>, Self, Self)>),

    /// Anonymous function
    Lambda(Rc<Lambda<Self>>),

    /// Definition scope
    Defs(Rc<(Vec<Def>, Self)>),

    /// Placeholders for more general primitives
    Add(Rc<(Self, Self)>),
    Read(),
    Show(Rc<Self>),

    /// Internal type annotations are not part of the syntax. They are produced by the type checker
    /// to augment the AST with typing information.
    Annotation(Rc<(Type, Self)>),
}

/// Syntax for representing types
#[derive(Clone, Debug, PartialEq)]
pub enum TyExpr {
    Int,
    Real,
    String,
    Var(String),
    Fn(Rc<(TyExpr, TyExpr)>),
}

/// The AST of an anonymous function
#[derive(Debug, PartialEq)]
pub struct Lambda<E> {
    pub param: String,
    pub body: E,
}

/// Different variants of definitions
#[derive(Debug, PartialEq)]
pub enum Def {
    /// Function definition
    Func(FnDef),
    /// Enum definition
    Enum(EnumDef),
    /// Function definition
    InferredFunc(TFnDef),
}

/// Function Definition with explicit types
#[derive(Debug, PartialEq)]
pub struct FnDef {
    pub fname: String,
    pub tvars: Vec<String>,
    pub param: String,
    pub ptype: TyExpr,
    pub rtype: TyExpr,
    pub body: Expr,
}

/// Function Definition with inferred signature
#[derive(Debug, PartialEq)]
pub struct TFnDef {
    pub signature: Type,
    pub fname: String,
    pub param: String,
    pub body: Expr,
}

/// Enum definition
#[derive(Debug, PartialEq)]
pub struct EnumDef {
    pub tname: String,
    pub variants: Vec<EnumVariant>,
}

/// Possible enum variants
#[derive(Debug, PartialEq)]
pub enum EnumVariant {
    Constant(String),
    Constructor(String, TyExpr),
}

impl Expr {
    pub fn int(x: impl Into<i64>) -> Self {
        Expr::Int(x.into())
    }

    pub fn real(x: impl Into<f64>) -> Self {
        Expr::Real(x.into())
    }

    pub fn string(x: impl Into<String>) -> Self {
        Expr::String(x.into())
    }

    pub fn var(name: impl ToString) -> Self {
        Expr::Ref(name.to_string())
    }

    pub fn record(fields: impl ListBuilder<Expr>) -> Self {
        Expr::Record(Rc::new(fields.build()))
    }

    pub fn cons(ety: impl ToString, variant: impl ToString, args: impl ListBuilder<Expr>) -> Self {
        Expr::Cons(Rc::new((
            ety.to_string(),
            variant.to_string(),
            args.build(),
        )))
    }

    pub fn decons(
        value: impl Into<Expr>,
        variant: impl ToString,
        vars: impl ListBuilder<String>,
        matches: impl Into<Expr>,
        mismatch: impl Into<Expr>,
    ) -> Self {
        Expr::Decons(Rc::new((
            value.into(),
            variant.to_string(),
            vars.build(),
            matches.into(),
            mismatch.into(),
        )))
    }

    pub fn apply(f: impl Into<Expr>, a: impl Into<Expr>) -> Self {
        Expr::Apply(Rc::new((f.into(), a.into())))
    }

    pub fn lambda<T>(p: impl ToString, body: T) -> Self
    where
        Expr: From<T>,
    {
        Expr::Lambda(Rc::new(Lambda {
            param: p.to_string(),
            body: body.into(),
        }))
    }

    pub fn defs<T>(defs: impl Into<Vec<Def>>, body: T) -> Self
    where
        Expr: From<T>,
    {
        Expr::Defs(Rc::new((defs.into(), body.into())))
    }

    pub fn add(a: impl Into<Expr>, b: impl Into<Expr>) -> Self {
        Expr::Add(Rc::new((a.into(), b.into())))
    }

    pub fn show(val: impl Into<Expr>) -> Self {
        Expr::Show(Rc::new(val.into()))
    }

    pub fn annotate(t: impl Into<Type>, x: impl Into<Self>) -> Self {
        Expr::Annotation(Rc::new((t.into(), x.into())))
    }

    pub fn get_type(&self) -> &Type {
        match self {
            Expr::Int(_) => &Type::Int,
            Expr::Real(_) => &Type::Real,
            Expr::Show(_) => &Type::Unit,
            Expr::Defs(defs) => defs.1.get_type(),
            Expr::Annotation(ann) => &ann.0,
            _ => panic!("unannotated expression: {self:?}"),
        }
    }
}

impl Def {
    pub fn func<V, P, R, B>(
        fname: impl ToString,
        tvars: impl IntoIterator<Item = V>,
        ptype: P,
        rtype: R,
        param: impl ToString,
        body: B,
    ) -> Self
    where
        V: ToString,
        TyExpr: From<P>,
        TyExpr: From<R>,
        Expr: From<B>,
    {
        Def::Func(FnDef {
            fname: fname.to_string(),
            tvars: tvars.into_iter().map(|v| v.to_string()).collect(),
            param: param.to_string(),
            ptype: ptype.into(),
            rtype: rtype.into(),
            body: body.into(),
        })
    }

    pub fn enum_(tname: impl ToString, variants: impl ListBuilder<EnumVariant>) -> Self {
        Def::Enum(EnumDef {
            tname: tname.to_string(),
            variants: variants.build(),
        })
    }
    pub fn inferred_func(
        sig: impl Into<Type>,
        fname: impl ToString,
        param: impl ToString,
        body: impl Into<Expr>,
    ) -> Self {
        Def::InferredFunc(TFnDef {
            signature: sig.into(),
            fname: fname.to_string(),
            param: param.to_string(),
            body: body.into(),
        })
    }
}

impl TyExpr {
    pub fn func<P, R>(p: P, r: R) -> Self
    where
        TyExpr: From<P>,
        TyExpr: From<R>,
    {
        TyExpr::Fn(Rc::new((p.into(), r.into())))
    }
}

impl From<&str> for Expr {
    fn from(value: &str) -> Self {
        Expr::Ref(value.to_string())
    }
}

impl From<i64> for Expr {
    fn from(value: i64) -> Self {
        Expr::Int(value)
    }
}

impl From<f64> for Expr {
    fn from(value: f64) -> Self {
        Expr::Real(value)
    }
}

impl From<&str> for TyExpr {
    fn from(value: &str) -> Self {
        TyExpr::Var(value.to_string())
    }
}

impl From<&str> for EnumVariant {
    fn from(name: &str) -> Self {
        EnumVariant::Constant(name.into())
    }
}

impl From<(&str, TyExpr)> for EnumVariant {
    fn from((name, ty): (&str, TyExpr)) -> Self {
        EnumVariant::Constructor(name.into(), ty)
    }
}

/// Internal representation of types, as produces by the type checker
#[derive(Clone, PartialEq)]
pub enum Type {
    Unit,
    Int,
    Real,
    String,
    Opaque(String),
    Var(usize),
    Fn(Rc<(Type, Type)>),
    Generic(Rc<GenericType>),
    Record(Rc<Vec<Type>>),
    Enum(Rc<EnumType>),
}

#[derive(PartialEq)]
pub struct EnumType {
    pub name: String,
    pub variants: HashMap<String, Vec<Type>>,
}

impl Debug for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Unit => write!(f, "<unit>"),
            Type::Int => write!(f, "Int"),
            Type::Real => write!(f, "Real"),
            Type::String => write!(f, "String"),
            Type::Opaque(name) => write!(f, "{name}"),
            Type::Var(nr) => write!(f, "'{nr}"),
            Type::Fn(sig) => write!(f, "({:?} -> {:?})", sig.0, sig.1),
            Type::Generic(g) => write!(f, "{g:?}"),
            Type::Record(xs) => write!(
                f,
                "[{}]",
                xs.iter()
                    .map(|x| format!("{:?}", x))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            Type::Enum(e) => write!(f, "<Enum {}>", e.name),
        }
    }
}

impl Type {
    pub fn func(f: impl Into<Type>, p: impl Into<Type>) -> Self {
        Self::Fn(Rc::new((f.into(), p.into())))
    }

    pub fn enum_(name: impl Into<String>, variants: impl ListBuilder<(String, Vec<Self>)>) -> Self {
        Self::Enum(Rc::new(EnumType {
            name: name.into(),
            variants: variants.build().into_iter().collect(),
        }))
    }
}

pub trait ListBuilder<T> {
    fn build(self) -> Vec<T>
    where
        Self: Sized,
    {
        let mut list = vec![];
        self.build_into(&mut list);
        list
    }
    fn build_into(self, buf: &mut Vec<T>);
}

impl<T> ListBuilder<T> for Vec<T> {
    fn build(self) -> Vec<T>
    where
        Self: Sized,
    {
        self
    }

    fn build_into(self, buf: &mut Vec<T>) {
        buf.extend(self)
    }
}

impl<T: Clone> ListBuilder<T> for &[T] {
    fn build(self) -> Vec<T>
    where
        Self: Sized,
    {
        self.to_vec()
    }

    fn build_into(self, buf: &mut Vec<T>) {
        buf.extend(self.iter().cloned())
    }
}

impl<T> ListBuilder<T> for () {
    fn build_into(self, _: &mut Vec<T>) {}
}

impl<A, OUT> ListBuilder<OUT> for (A,)
where
    A: Into<OUT>,
{
    fn build_into(self, buf: &mut Vec<OUT>) {
        buf.push(self.0.into());
    }
}

impl<A, Z, OUT> ListBuilder<OUT> for (A, Z)
where
    Z: ListBuilder<OUT>,
    A: Into<OUT>,
{
    fn build_into(self, buf: &mut Vec<OUT>) {
        buf.push(self.0.into());
        self.1.build_into(buf);
    }
}

impl<A, B, Z, OUT> ListBuilder<OUT> for (A, B, Z)
where
    Z: ListBuilder<OUT>,
    A: Into<OUT>,
    B: Into<OUT>,
{
    fn build_into(self, buf: &mut Vec<OUT>) {
        buf.push(self.0.into());
        buf.push(self.1.into());
        self.2.build_into(buf);
    }
}

impl<A, OUT, const N: usize> ListBuilder<OUT> for [A; N]
where
    A: Into<OUT>,
{
    fn build_into(self, buf: &mut Vec<OUT>) {
        buf.extend(self.into_iter().map(|x| x.into()))
    }
}
