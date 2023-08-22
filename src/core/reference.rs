use std::ops::Deref;

#[derive(Debug)]
// may contain a &'static T in the future
pub struct Ref<T: ?Sized + 'static>(&'static T);

impl<T> Ref<T> {
    pub fn new(obj: T) -> Self {
        Ref(Box::leak(Box::new(obj)))
    }

    pub fn as_ptr(&self) -> *const T {
        self.0
    }

    pub unsafe fn unsafe_mutate(&self, f: impl Fn(&mut T)) {
        let mut_ref = &mut *(self.0 as *const _ as *mut _);
        f(mut_ref)
    }
}

impl<T> Ref<[T]> {
    pub fn array(obj: Vec<T>) -> Self {
        Ref(Box::leak(obj.into_boxed_slice()))
    }
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
