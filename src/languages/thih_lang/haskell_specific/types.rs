use crate::languages::thih_lang::thih_core::kinds::Kind;
use crate::languages::thih_lang::thih_core::types::{Tycon, Type};

/// construct the unit type
pub fn t_unit() -> Type {
    Type::TCon(Tycon("()".into(), Kind::Star))
}

/// construct the character type
pub fn t_char() -> Type {
    Type::TCon(Tycon("Char".into(), Kind::Star))
}

/// construct the string type
pub fn t_string() -> Type {
    Type::TCon(Tycon("String".into(), Kind::Star))
}

/// construct the int type
pub fn t_int() -> Type {
    Type::TCon(Tycon("Int".into(), Kind::Star))
}

/// construct the integer type
pub fn t_integer() -> Type {
    Type::TCon(Tycon("Integer".into(), Kind::Star))
}

/// construct the float type
pub fn t_float() -> Type {
    Type::TCon(Tycon("Float".into(), Kind::Star))
}

/// construct the double type
pub fn t_double() -> Type {
    Type::TCon(Tycon("Double".into(), Kind::Star))
}

/// construct the list type constructor
pub fn t_list() -> Type {
    Type::TCon(Tycon("[]".into(), Kind::kfun(Kind::Star, Kind::Star)))
}

/// construct the function type constructor
pub fn t_arrow() -> Type {
    Type::TCon(Tycon(
        "->".into(),
        Kind::kfun(Kind::Star, Kind::kfun(Kind::Star, Kind::Star)),
    ))
}

/// construct the 2-tuple type constructor
pub fn t_tuple2() -> Type {
    Type::TCon(Tycon(
        ",".into(),
        Kind::kfun(Kind::Star, Kind::kfun(Kind::Star, Kind::Star)),
    ))
}

/// apply a type to another
pub fn tapp(a: Type, b: Type) -> Type {
    Type::tapp(a, b)
}

/// construct a function type
pub fn func(a: Type, b: Type) -> Type {
    tapp(tapp(t_arrow(), a), b)
}

/// construct a list type
pub fn list(t: Type) -> Type {
    tapp(t_list(), t)
}

/// construct a pair type
pub fn pair(a: Type, b: Type) -> Type {
    tapp(tapp(t_tuple2(), a), b)
}
