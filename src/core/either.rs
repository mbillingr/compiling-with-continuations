pub fn either<T>(value: T) -> Either<T> {
    Either { value }
}

#[derive(Debug)]
pub struct Either<T> {
    value: T,
}

#[derive(Debug)]
pub struct Or<A, B> {
    a: A,
    b: B,
}

impl<T> Either<T> {
    pub fn or(self, value: T) -> Or<Self, T> {
        Or { a: self, b: value }
    }
}

impl<T: PartialEq> PartialEq<T> for Either<T> {
    fn eq(&self, other: &T) -> bool {
        self.value == *other
    }
}

impl<T, A: PartialEq<T>, B: PartialEq<T>> PartialEq<T> for Or<A, B> {
    fn eq(&self, other: &T) -> bool {
        self.a == *other || self.b == *other
    }
}

impl<A: PartialEq<i32>, B: PartialEq<i32>> PartialEq<Or<A, B>> for i32 {
    fn eq(&self, other: &Or<A, B>) -> bool {
        other == self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn either_or() {
        assert_eq!(either(1).or(2), 1);
        assert_eq!(2, either(1).or(2));
        assert_ne!(3, either(1).or(2));
    }
}
