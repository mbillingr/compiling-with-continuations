#[macro_export]
macro_rules! map {
    ($($k:expr => $v:expr),* $(,)?) => {{
        $crate::core::persistent::PersistentMap::new()$(.insert($k, $v))*
    }};
}

#[macro_export]
macro_rules! set {
    ($($k:expr),* $(,)?) => {{
        $crate::core::persistent::PersistentSet::new()$(.insert($k))*
    }};
}

#[cfg(test)]
mod tests {
    use crate::core::persistent::PersistentMap;
    use crate::core::persistent::PersistentSet;

    #[test]
    fn make_map() {
        assert_eq!(map![], PersistentMap::<i8, i16>::new());
        assert_eq!(map!["a" => 2], PersistentMap::new().insert("a", 2));
        assert_eq!(map!["a" => 2,], PersistentMap::new().insert("a", 2));
        assert_eq!(
            map!["a" => 2, "b" => 30],
            PersistentMap::new().insert("a", 2).insert("b", 30)
        );
    }

    #[test]
    fn make_set() {
        assert_eq!(set![], PersistentSet::<i8>::new());
        assert_eq!(set!["a"], PersistentSet::new().insert("a"));
        assert_eq!(set!["a",], PersistentSet::new().insert("a"));
        assert_eq!(set!["a", "b"], PersistentSet::new().insert("a").insert("b"));
    }
}
