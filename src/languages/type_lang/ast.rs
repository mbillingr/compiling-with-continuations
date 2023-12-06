use crate::languages::type_lang::type_checker::GenericType;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

/// Nodes of the abstract syntax tree
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    /// The value of the unit type
    Unit,

    /// Integer constant
    Int(i64),

    /// Real constant
    Real(f64),

    /// String constant
    String(String),

    /// Variable reference
    Ref(String),

    /// Function application
    Apply(Rc<(Self, Vec<Self>)>),

    /// Tuple construction
    Record(Rc<Vec<Self>>),

    /// Tuple access
    Select(Rc<(usize, Self)>),

    /// Enum variant construction
    Cons(Rc<(TyExpr, String)>),

    /// Enum pattern matching (will be replaced by more general pattern matching)
    MatchEnum(Rc<(Self, Vec<EnumMatchArm>)>),

    /// Anonymous function
    Lambda(Rc<Lambda<Self>>),

    /// Definition scope
    Defs(Rc<(Vec<Def>, Self)>),

    /// Sequence of statements
    Sequence(Rc<(Self, Self)>),

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
    Unit,
    Int,
    Real,
    String,
    Named(String),
    Fn(Rc<(Vec<TyExpr>, TyExpr)>),
    Record(Rc<Vec<TyExpr>>),
    Construct(Rc<(String, Vec<TyExpr>)>),
}

/// The AST of an anonymous function
#[derive(Debug, PartialEq)]
pub struct Lambda<E> {
    pub params: Vec<String>,
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
    pub params: Vec<String>,
    pub ptypes: Vec<TyExpr>,
    pub rtype: TyExpr,
    pub body: Expr,
}

/// Function Definition with inferred signature
#[derive(Debug, PartialEq)]
pub struct TFnDef {
    pub signature: Type,
    pub fname: String,
    pub params: Vec<String>,
    pub body: Expr,
}

/// Enum definition
#[derive(Clone, Debug, PartialEq)]
pub struct EnumDef {
    pub tname: String,
    pub tvars: Vec<String>,
    pub variants: Rc<Vec<EnumVariant>>,
}

/// Possible enum variants
#[derive(Debug, PartialEq)]
pub struct EnumVariant {
    pub name: String,
    pub tyxs: Vec<TyExpr>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct EnumMatchArm {
    pub pattern: EnumVariantPattern,
    pub branch: Expr,
}

#[derive(Clone, Debug, PartialEq)]
pub struct EnumVariantPattern {
    pub name: String,
    pub vars: Vec<String>,
}

/// Implementation block
#[derive(Debug, PartialEq)]
pub struct Impl {
    pub tvars: Vec<String>,
    pub impl_type: TyExpr,
    pub defs: Vec<FnDef>,
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

    pub fn select(index: usize, rec: impl Into<Expr>) -> Self {
        Expr::Select(Rc::new((index, rec.into())))
    }

    pub fn cons(etx: impl Into<TyExpr>, variant: impl ToString) -> Self {
        Expr::Cons(Rc::new((etx.into(), variant.to_string())))
    }

    pub fn match_enum(value: impl Into<Expr>, arms: impl ListBuilder<EnumMatchArm>) -> Self {
        Expr::MatchEnum(Rc::new((value.into(), arms.build())))
    }

    pub fn apply(f: impl Into<Expr>, a: impl ListBuilder<Expr>) -> Self {
        Expr::Apply(Rc::new((f.into(), a.build())))
    }

    pub fn lambda<T>(p: impl ListBuilder<String>, body: T) -> Self
    where
        Expr: From<T>,
    {
        Expr::Lambda(Rc::new(Lambda {
            params: p.build(),
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

    pub fn get_type(&self) -> Type {
        match self {
            Expr::Unit => Type::Unit,
            Expr::Int(_) => Type::Int,
            Expr::Real(_) => Type::Real,
            Expr::String(_) => Type::String,
            Expr::Show(_) => Type::Unit,
            Expr::Defs(defs) => defs.1.get_type(),
            Expr::Sequence(xs) => xs.1.get_type(),
            Expr::Annotation(ann) => ann.0.clone(),
            _ => panic!("unannotated expression: {self:?}"),
        }
    }

    pub fn sequence(exprs: impl ListBuilder<Self>) -> Self {
        let mut exprs = exprs.build().into_iter().rev();
        let mut expr = exprs.next().expect("sequence can't be empty");
        for x in exprs {
            expr = Expr::Sequence(Rc::new((x, expr)));
        }
        expr
    }
}

impl Def {
    pub fn func(
        fname: impl ToString,
        tvars: impl ListBuilder<String>,
        ptypes: impl ListBuilder<TyExpr>,
        rtype: impl Into<TyExpr>,
        params: impl ListBuilder<String>,
        body: impl Into<Expr>,
    ) -> Self {
        Def::Func(FnDef::new(fname, tvars, ptypes, rtype, params, body))
    }

    pub fn enum_<V: ToString>(
        tname: impl ToString,
        tvars: impl IntoIterator<Item = V>,
        variants: impl ListBuilder<EnumVariant>,
    ) -> Self {
        Def::Enum(EnumDef {
            tname: tname.to_string(),
            tvars: tvars.into_iter().map(|v| v.to_string()).collect(),
            variants: Rc::new(variants.build()),
        })
    }
    pub fn inferred_func(
        sig: impl Into<Type>,
        fname: impl ToString,
        params: impl ListBuilder<String>,
        body: impl Into<Expr>,
    ) -> Self {
        Def::InferredFunc(TFnDef {
            signature: sig.into(),
            fname: fname.to_string(),
            params: params.build(),
            body: body.into(),
        })
    }
}

impl FnDef {
    pub fn new(
        fname: impl ToString,
        tvars: impl ListBuilder<String>,
        ptypes: impl ListBuilder<TyExpr>,
        rtype: impl Into<TyExpr>,
        params: impl ListBuilder<String>,
        body: impl Into<Expr>,
    ) -> Self {
        FnDef {
            fname: fname.to_string(),
            tvars: tvars.build(),
            params: params.build(),
            ptypes: ptypes.build(),
            rtype: rtype.into(),
            body: body.into(),
        }
    }
}

impl TyExpr {
    pub fn func(p: impl ListBuilder<TyExpr>, r: impl Into<TyExpr>) -> Self {
        TyExpr::Fn(Rc::new((p.build(), r.into())))
    }
}

impl EnumVariant {
    pub fn constant(name: impl ToString) -> Self {
        EnumVariant {
            name: name.to_string(),
            tyxs: vec![],
        }
    }

    pub fn constructor(name: impl ToString, tyxs: impl ListBuilder<TyExpr>) -> Self {
        EnumVariant {
            name: name.to_string(),
            tyxs: tyxs.build(),
        }
    }
}

impl EnumVariantPattern {
    pub fn constant(name: impl ToString) -> Self {
        EnumVariantPattern {
            name: name.to_string(),
            vars: vec![],
        }
    }

    pub fn constructor(name: impl ToString, vars: impl ListBuilder<String>) -> Self {
        EnumVariantPattern {
            name: name.to_string(),
            vars: vars.build(),
        }
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
        TyExpr::Named(value.to_string())
    }
}

impl<A: Into<String>> From<(A,)> for TyExpr {
    fn from((a,): (A,)) -> Self {
        TyExpr::Construct(Rc::new((a.into(), vec![])))
    }
}

impl<A: Into<String>, B: Into<TyExpr>> From<(A, B)> for TyExpr {
    fn from((a, b): (A, B)) -> Self {
        TyExpr::Construct(Rc::new((a.into(), vec![b.into()])))
    }
}

impl From<&str> for EnumVariant {
    fn from(name: &str) -> Self {
        EnumVariant {
            name: name.into(),
            tyxs: vec![],
        }
    }
}

impl<T: ListBuilder<TyExpr>> From<(&str, T)> for EnumVariant {
    fn from((name, tys): (&str, T)) -> Self {
        EnumVariant {
            name: name.into(),
            tyxs: tys.build(),
        }
    }
}

impl From<&str> for EnumVariantPattern {
    fn from(name: &str) -> Self {
        EnumVariantPattern {
            name: name.to_string(),
            vars: vec![],
        }
    }
}

impl<N: ToString, V: ListBuilder<String>> From<(N, V)> for EnumVariantPattern {
    fn from((name, vars): (N, V)) -> Self {
        EnumVariantPattern {
            name: name.to_string(),
            vars: vars.build(),
        }
    }
}

impl<P: Into<EnumVariantPattern>, B: Into<Expr>> From<(P, B)> for EnumMatchArm {
    fn from((pattern, branch): (P, B)) -> Self {
        EnumMatchArm {
            pattern: pattern.into(),
            branch: branch.into(),
        }
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
    Fn(Rc<(Vec<Type>, Type)>),
    Generic(Rc<GenericType>),
    Record(Rc<Vec<Type>>),
    Enum(Rc<EnumType>),

    /// a generic type applied to type arguments
    GenericInstance(Rc<GenericInstance>),
}

#[derive(PartialEq)]
pub struct EnumType {
    pub template: Rc<GenericType>,
    pub variants: HashMap<String, Vec<Type>>,
}

impl Debug for EnumType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "<enum {} {:p}>",
            self.template.get_name(),
            Rc::as_ptr(&self.template)
        )
    }
}

pub struct GenericInstance {
    pub generic: Rc<GenericType>,
    pub targs: Vec<Type>,
    pub actual_t: RefCell<Option<Type>>,
}

impl PartialEq for GenericInstance {
    fn eq(&self, other: &Self) -> bool {
        self.generic == other.generic && self.targs == other.targs
    }
}

impl Eq for Type {}

impl Hash for Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Type::Unit => 0.hash(state),
            Type::Int => 1.hash(state),
            Type::Real => 2.hash(state),
            Type::String => 3.hash(state),
            Type::Opaque(name) => name.hash(state),
            Type::Var(v) => v.hash(state),
            Type::Fn(rc) => Rc::as_ptr(rc).hash(state),
            Type::Generic(rc) => Rc::as_ptr(rc).hash(state),
            Type::Record(rc) => Rc::as_ptr(rc).hash(state),
            Type::Enum(rc) => Rc::as_ptr(rc).hash(state),
            Type::GenericInstance(gi) => {
                Rc::as_ptr(&gi.generic).hash(state);
                for t in gi.targs.iter() {
                    t.hash(state);
                }
            }
        }
    }
}

impl Debug for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Unit => write!(f, "Unit"),
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
            Type::Enum(e) => write!(f, "{:?}", e),

            Type::GenericInstance(gi) => {
                write!(f, "({}", gi.generic.get_name())?;
                for t in gi.targs.iter() {
                    write!(f, ", {t:?}")?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Type {
    pub fn func(f: impl ListBuilder<Type>, p: impl Into<Type>) -> Self {
        Self::Fn(Rc::new((f.build(), p.into())))
    }

    pub fn enum_(
        template: Rc<GenericType>,
        variants: impl ListBuilder<(String, Vec<Self>)>,
    ) -> Self {
        Self::Enum(Rc::new(EnumType {
            template,
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

impl ListBuilder<String> for Vec<&str> {
    fn build_into(self, buf: &mut Vec<String>) {
        buf.extend(self.into_iter().map(str::to_string))
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

impl<A, B, C, Z, OUT> ListBuilder<OUT> for (A, B, C, Z)
where
    Z: ListBuilder<OUT>,
    A: Into<OUT>,
    B: Into<OUT>,
    C: Into<OUT>,
{
    fn build_into(self, buf: &mut Vec<OUT>) {
        buf.push(self.0.into());
        buf.push(self.1.into());
        buf.push(self.2.into());
        self.3.build_into(buf);
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
