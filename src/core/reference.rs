use std::borrow::Borrow;
use std::fmt::Formatter;
use std::ops::Deref;

#[derive(PartialEq, PartialOrd, Ord, Eq, Hash)]
// public field for pattern matching
pub struct Ref<T: ?Sized + 'static>(pub &'static T);

impl<T> Ref<T> {
    pub fn new(obj: T) -> Self {
        Ref(Box::leak(Box::new(obj)))
    }
}
impl<T: ?Sized> Ref<T> {
    pub fn as_ptr(&self) -> *const T {
        self.0
    }

    pub fn as_ref(&self) -> &'static T {
        &self.0
    }

    pub unsafe fn unsafe_mutate(&self, f: impl Fn(&mut T)) {
        let cptr = self.0 as *const T;
        let mptr = cptr as *mut T;
        let mut_ref = &mut *mptr;
        f(mut_ref)
    }
}

impl<T> Ref<[T]> {
    pub fn array(obj: Vec<T>) -> Self {
        Ref(Box::leak(obj.into_boxed_slice()))
    }
    pub fn slice(obj: &'static [T]) -> Self {
        Ref(obj)
    }
}

impl<T: Clone> Ref<[T]> {
    pub fn prepend(&self, x: T) -> Self {
        let mut xs = Vec::with_capacity(1 + self.len());
        xs.push(x);
        for y in self.iter().cloned() {
            xs.push(y);
        }
        Self::array(xs)
    }

    pub fn append(&self, ys: impl IntoIterator<Item = T>) -> Self {
        let mut xs = self.to_vec();
        xs.extend(ys);
        Self::array(xs)
    }
}

#[macro_export]
macro_rules! list {
    ($($item:expr),*$(,)?) => { $crate::core::reference::Ref::array(vec![$($item),*]) };
}

impl<T: ?Sized> Copy for Ref<T> {}

impl<T: ?Sized> Clone for Ref<T> {
    fn clone(&self) -> Self {
        Ref(self.0)
    }
}

impl From<&'static str> for Ref<str> {
    fn from(value: &'static str) -> Self {
        Ref(value.into())
    }
}

impl From<String> for Ref<str> {
    fn from(value: String) -> Self {
        Ref(Box::leak(value.into_boxed_str()))
    }
}

impl From<&String> for Ref<str> {
    fn from(value: &String) -> Self {
        Ref(Box::leak(value.to_string().into_boxed_str()))
    }
}

impl From<&str> for Ref<String> {
    fn from(value: &str) -> Self {
        Ref::new(value.to_string())
    }
}

impl From<&String> for Ref<String> {
    fn from(value: &String) -> Self {
        Ref::new(value.clone())
    }
}

impl<T> From<Vec<T>> for Ref<[T]> {
    fn from(value: Vec<T>) -> Self {
        Ref::array(value)
    }
}

impl<T> From<T> for Ref<T> {
    fn from(obj: T) -> Self {
        Ref::new(obj)
    }
}

impl<T: ?Sized> Deref for Ref<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<T: ?Sized + std::fmt::Debug> std::fmt::Debug for Ref<T> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: ?Sized> Borrow<T> for Ref<T> {
    fn borrow(&self) -> &T {
        return self.0;
    }
}

impl<T: ?Sized + std::fmt::Display> std::fmt::Display for Ref<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn struct_sizes() {
        assert_eq!(std::mem::size_of::<Ref<()>>(), 8);
        assert_eq!(std::mem::size_of::<Ref<i8>>(), 8);
        assert_eq!(std::mem::size_of::<Ref<i64>>(), 8);
        assert_eq!(std::mem::size_of::<Ref<i128>>(), 8);
        assert_eq!(std::mem::size_of::<Ref<Vec<()>>>(), 8);
        assert_eq!(std::mem::size_of::<Ref<String>>(), 8);

        assert_eq!(std::mem::size_of::<Ref<[()]>>(), 16); // note that Ref now is a fatptr
        assert_eq!(std::mem::size_of::<Ref<str>>(), 16); // note that Ref now is a fatptr
    }
}
