use std::any::type_name;
use std::fmt::Formatter;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde::de::{EnumAccess, Visitor};
use crate::core::reference::Ref;

#[derive(Debug, Eq, PartialEq, Hash)]
struct Symbol(Ref<str>);


impl Symbol {
    fn from_static(s: &'static str) -> Self {
        Symbol(Ref(s))
    }
}

impl Serialize for Symbol {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer {
        // pretend symbols are unit variants; works only because they are static strings...
        serializer.serialize_unit_variant("", 0, self.0.0)
    }
}

impl<'de> Deserialize<'de> for Symbol {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error> where D: Deserializer<'de> {
        assert_eq!(type_name::<D>(), "&mut serde_lexpr::value::de::Deserializer");
        let x:&serde_lexpr::Value = unsafe {
            // This is so unsafe, I'm sure it will break!
            let ptr = &deserializer as *const D;
            let ptr = ptr as *const *const *const serde_lexpr::Value;
            &***ptr
        };
        if let serde_lexpr::Value::Symbol(s) = x {
            Ok(Symbol(Ref::from(s.to_string())))
        } else {
            panic!("{:?}", x)
        }
    }
}

struct SymbolVisitor;

impl<'de> Visitor<'de> for SymbolVisitor {
    type Value = Symbol;

    fn expecting(&self, formatter: &mut Formatter) -> std::fmt::Result {
        write!(formatter, "a symbol")
    }

    fn visit_enum<A>(self, data: A) -> Result<Self::Value, A::Error> where A: EnumAccess<'de> {
        println!("{:?}", type_name::<A>());
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ser() {
        assert_eq!(serde_lexpr::to_string(&Symbol::from_static("foo")).unwrap(), "foo");
    }

    #[test]
    fn de() {
        assert_eq!(serde_lexpr::from_str::<Symbol>("foo").unwrap(), Symbol::from_static("foo"));
    }
}