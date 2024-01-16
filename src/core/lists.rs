use std::fmt::{Debug, Formatter};
use std::rc::Rc;
#[macro_export]
macro_rules! list {
    () => { $crate::lists::List::Nil };

    ($x:expr $(, $r:expr)*) => {
        list![$($r),*].cons($x)
    };
}

pub fn rfold1<T, I: DoubleEndedIterator<Item = T>>(
    it: impl IntoIterator<Item = T, IntoIter = I>,
    f: impl Fn(T, T) -> T,
) -> T {
    let mut it = it.into_iter().rev();
    let mut res = it.next().expect("List with at least one element");
    while let Some(x) = it.next() {
        res = f(x, res);
    }
    res
}

pub fn eq_diff<T: PartialEq>(a: impl IntoIterator<Item = T>, mut b: Vec<T>) -> Vec<T> {
    let mut out = vec![];
    for x in a {
        if let Some(i) = b.iter().position(|y| &x == y) {
            b.swap_remove(i);
        } else {
            out.push(x);
        }
    }
    out
}

pub fn eq_union<T: PartialEq>(mut a: Vec<T>, b: impl IntoIterator<Item = T>) -> Vec<T> {
    for x in b {
        if !a.contains(&x) {
            a.push(x)
        }
    }
    a
}

pub fn eq_intersect<T: PartialEq>(a: impl IntoIterator<Item = T>, b: Vec<T>) -> Vec<T> {
    a.into_iter().filter(|x| b.contains(x)).collect()
}

#[derive(PartialEq)]
pub enum List<T> {
    Nil,
    Elem(Rc<(T, Self)>),
}

impl<T: Debug> Debug for List<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        let mut es = self.iter();
        if let Some(e) = es.next() {
            write!(f, "{:?}", e)?;
        }
        for e in es {
            write!(f, " {:?}", e)?;
        }
        write!(f, "]")
    }
}

impl<T> List<T> {
    pub fn cons(&self, x: T) -> Self {
        List::Elem(Rc::new((x, self.clone())))
    }

    pub fn iter(&self) -> ListIter<T> {
        ListIter(&self)
    }

    pub fn concat<I>(ls: I) -> Self
    where
        T: Clone,
        I: IntoIterator<Item = Self>,
        I::IntoIter: DoubleEndedIterator,
    {
        let mut out = Self::Nil;
        for l in ls.into_iter().rev() {
            out = l.append(out)
        }
        out
    }

    pub fn append(&self, b: Self) -> Self
    where
        T: Clone,
    {
        match self {
            Self::Nil => b,
            Self::Elem(e) => e.1.append(b).cons(e.0.clone()),
        }
    }

    pub fn contains(&self, x: &T) -> bool
    where
        T: PartialEq,
    {
        match self {
            Self::Nil => false,
            Self::Elem(e) if &e.0 == x => true,
            Self::Elem(e) => e.1.contains(x),
        }
    }
}

impl<T> Clone for List<T> {
    fn clone(&self) -> Self {
        match self {
            List::Nil => List::Nil,
            List::Elem(e) => List::Elem(e.clone()),
        }
    }
}

pub struct ListIter<'a, T>(&'a List<T>);

impl<'a, T> Iterator for ListIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let e = match &self.0 {
            List::Nil => return None,
            List::Elem(e) => e,
        };

        self.0 = &e.1;
        return Some(&e.0);
    }
}

impl<T> FromIterator<T> for List<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut items: Vec<_> = iter.into_iter().collect();
        let mut out = List::Nil;
        while let Some(x) = items.pop() {
            out = out.cons(x);
        }
        out
    }
}

impl<'a, T> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = ListIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        ListIter(self)
    }
}
