use crate::core::persistent::PersistentMap;
use serde::de::{MapAccess, Visitor};
use serde::{Deserialize, Deserializer};
use std::hash::Hash;
use std::marker::PhantomData;

impl<'de, K, V> Deserialize<'de> for PersistentMap<K, V>
where
    K: Deserialize<'de> + Eq + Hash,
    V: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_map(MapVisitor {
            marker: PhantomData,
        })
    }
}

struct MapVisitor<K, V> {
    marker: PhantomData<PersistentMap<K, V>>,
}

impl<'de, K, V> Visitor<'de> for MapVisitor<K, V>
where
    K: Deserialize<'de> + Eq + Hash,
    V: Deserialize<'de>,
{
    type Value = PersistentMap<K, V>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a map")
    }

    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
    where
        M: MapAccess<'de>,
    {
        let mut map = PersistentMap::new();

        while let Some((key, value)) = access.next_entry()? {
            map = map.insert(key, value);
        }

        Ok(map)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::map;

    #[test]
    fn map() {
        assert_eq!(
            serde_json::from_str::<PersistentMap<_, _>>("{\"a\": 1, \"x\": 2}").unwrap(),
            map!["a" => 1, "x" => 2]
        )
    }
}
