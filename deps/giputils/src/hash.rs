use ahash::{HashMap, HashSet, RandomState};
use serde::{Deserialize, Serialize};
use std::{
    collections::{hash_map, hash_set},
    fmt::{self, Debug},
    hash::Hash,
    ops::{Deref, DerefMut},
};

#[derive(Clone)]
pub struct GHashSet<T> {
    h: HashSet<T>,
}

impl<T> GHashSet<T> {
    pub fn new() -> Self {
        let hb = RandomState::with_seeds(0, 0, 0, 0);
        Self {
            h: HashSet::with_hasher(hb),
        }
    }
}

impl<T> Deref for GHashSet<T> {
    type Target = HashSet<T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.h
    }
}

impl<T> DerefMut for GHashSet<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.h
    }
}

impl<T> Default for GHashSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> IntoIterator for GHashSet<T> {
    type Item = T;

    type IntoIter = hash_set::IntoIter<T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.h.into_iter()
    }
}

impl<T: Eq + Hash> FromIterator<T> for GHashSet<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let hb = RandomState::with_seeds(0, 0, 0, 0);
        let mut h = HashSet::with_hasher(hb);
        h.extend(iter);
        Self { h }
    }
}

impl<T: Debug> Debug for GHashSet<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.h.fmt(f)
    }
}

impl<T: Eq + Hash> PartialEq for GHashSet<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.h == other.h
    }
}

impl<T: Eq + Hash> Eq for GHashSet<T> {}

impl<T: Serialize> Serialize for GHashSet<T> {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.h.serialize(serializer)
    }
}

impl<'de, T: Deserialize<'de> + Eq + Hash> Deserialize<'de> for GHashSet<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        HashSet::<T>::deserialize(deserializer).map(|h| {
            let mut new_h = GHashSet::new();
            new_h.extend(h);
            new_h
        })
    }
}

#[derive(Clone)]
pub struct GHashMap<K, V> {
    h: HashMap<K, V>,
}

impl<K, V> GHashMap<K, V> {
    pub fn new() -> Self {
        let hb = RandomState::with_seeds(0, 0, 0, 0);
        Self {
            h: HashMap::with_hasher(hb),
        }
    }
}

impl<K, V> Deref for GHashMap<K, V> {
    type Target = HashMap<K, V>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.h
    }
}

impl<K, V> DerefMut for GHashMap<K, V> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.h
    }
}

impl<K, V> Default for GHashMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> IntoIterator for GHashMap<K, V> {
    type Item = (K, V);

    type IntoIter = hash_map::IntoIter<K, V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.h.into_iter()
    }
}

impl<K: Eq + Hash, V> FromIterator<(K, V)> for GHashMap<K, V> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let hb = RandomState::with_seeds(0, 0, 0, 0);
        let mut h = HashMap::with_hasher(hb);
        h.extend(iter);
        Self { h }
    }
}

impl<K: Debug, V: Debug> Debug for GHashMap<K, V> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.h.fmt(f)
    }
}

impl<K: Eq + Hash, V: PartialEq> PartialEq for GHashMap<K, V> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.h == other.h
    }
}

impl<K: Eq + Hash, V: Eq> Eq for GHashMap<K, V> {}

impl<K: Serialize, V: Serialize> Serialize for GHashMap<K, V> {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.h.serialize(serializer)
    }
}

impl<'de, K: Deserialize<'de> + Eq + Hash, V: Deserialize<'de>> Deserialize<'de>
    for GHashMap<K, V>
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        HashMap::<K, V>::deserialize(deserializer).map(|h| {
            let mut new_h = GHashMap::new();
            new_h.extend(h);
            new_h
        })
    }
}
