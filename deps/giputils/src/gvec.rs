use std::{
    ops::{Deref, DerefMut, Index, IndexMut},
    ptr, vec,
};

use rand::{
    RngExt,
    distr::{Distribution, StandardUniform},
    rngs::StdRng,
};
use serde::{Deserialize, Serialize};

#[derive(Default, Debug, Clone)]
pub struct Gvec<T> {
    data: Vec<T>,
}

impl<T> Gvec<T> {
    #[inline]
    pub fn new() -> Self {
        Self {
            data: Default::default(),
        }
    }

    #[inline]
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    #[inline]
    pub fn new_rand(len: usize, rng: &mut StdRng) -> Self
    where
        StandardUniform: Distribution<T>,
    {
        let mut data = Vec::with_capacity(len);
        for _ in 0..len {
            data.push(rng.random());
        }
        Self { data }
    }

    #[inline]
    pub fn swap(&mut self, x: u32, y: u32) {
        let pa = ptr::addr_of_mut!(self[x]);
        let pb = ptr::addr_of_mut!(self[y]);
        unsafe {
            ptr::swap(pa, pb);
        }
    }
}

impl<T: Copy + Clone> Gvec<T> {
    #[inline]
    pub fn swap_remove(&mut self, index: usize) {
        let len = self.len() - 1;
        self[index] = self[len];
        unsafe { self.set_len(len) }
    }
}

impl<T: Default> Gvec<T> {
    #[inline]
    pub fn reserve(&mut self, size: usize) {
        if self.len() <= size {
            self.data.resize_with(size, Default::default);
        }
    }
}

impl<T> Index<u32> for Gvec<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: u32) -> &Self::Output {
        #[cfg(not(debug_assertions))]
        unsafe {
            self.data.get_unchecked(index as usize)
        }
        #[cfg(debug_assertions)]
        &self.data[index as usize]
    }
}

impl<T> IndexMut<u32> for Gvec<T> {
    #[inline]
    fn index_mut(&mut self, index: u32) -> &mut Self::Output {
        #[cfg(not(debug_assertions))]
        unsafe {
            self.data.get_unchecked_mut(index as usize)
        }
        #[cfg(debug_assertions)]
        &mut self.data[index as usize]
    }
}

impl<T> Index<i32> for Gvec<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: i32) -> &Self::Output {
        #[cfg(not(debug_assertions))]
        unsafe {
            self.data.get_unchecked(index as usize)
        }
        #[cfg(debug_assertions)]
        &self.data[index as usize]
    }
}

impl<T> IndexMut<i32> for Gvec<T> {
    #[inline]
    fn index_mut(&mut self, index: i32) -> &mut Self::Output {
        #[cfg(not(debug_assertions))]
        unsafe {
            self.data.get_unchecked_mut(index as usize)
        }
        #[cfg(debug_assertions)]
        &mut self.data[index as usize]
    }
}

impl<T> Index<usize> for Gvec<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        #[cfg(not(debug_assertions))]
        unsafe {
            self.data.get_unchecked(index)
        }
        #[cfg(debug_assertions)]
        &self.data[index]
    }
}

impl<T> IndexMut<usize> for Gvec<T> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        #[cfg(not(debug_assertions))]
        unsafe {
            self.data.get_unchecked_mut(index)
        }
        #[cfg(debug_assertions)]
        &mut self.data[index]
    }
}

impl<T> IntoIterator for Gvec<T> {
    type Item = T;

    type IntoIter = vec::IntoIter<T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.data.into_iter()
    }
}

impl<A> FromIterator<A> for Gvec<A> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        Self {
            data: Vec::from_iter(iter),
        }
    }
}

impl<T, const N: usize> From<[T; N]> for Gvec<T> {
    #[inline]
    fn from(data: [T; N]) -> Self {
        Self {
            data: Vec::from(data),
        }
    }
}

impl<T> From<Vec<T>> for Gvec<T> {
    #[inline]
    fn from(data: Vec<T>) -> Self {
        Self { data }
    }
}

impl<T: Serialize> Serialize for Gvec<T> {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.data.serialize(serializer)
    }
}

impl<'de, T: Deserialize<'de>> Deserialize<'de> for Gvec<T> {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Vec::<T>::deserialize(deserializer).map(Self::from)
    }
}

impl<T> Deref for Gvec<T> {
    type Target = Vec<T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<T> DerefMut for Gvec<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}
