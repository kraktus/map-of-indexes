use std::cmp::Ordering;
use std::fmt::Debug;
use thiserror::Error;

pub trait KeyValue {
    type K: Ord + Debug;
    type V;
    fn key(&self) -> &Self::K;
    fn value(&self) -> &Self::V;
}

impl<K: Ord + Debug, V> KeyValue for (K, V) {
    type K = K;
    type V = V;
    fn key(&self) -> &Self::K {
        &self.0
    }
    fn value(&self) -> &Self::V {
        &self.1
    }
}

#[derive(Error, Debug, PartialEq, Eq)]
pub enum MapOfIndexesError {
    #[error("At least two elements with same keys. Keys must be uniques.")]
    DuplicateKeys,
}

#[derive(Clone, Debug)]
pub struct MapOfIndexes<T> {
    inner: Vec<T>,
}

impl<T: KeyValue> Default for MapOfIndexes<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: KeyValue> TryFrom<Vec<T>> for MapOfIndexes<T> {
    type Error = MapOfIndexesError;

    fn try_from(mut vec: Vec<T>) -> Result<Self, Self::Error> {
        // Other solution was to check duplicate while sorting, supposedly faster to make linear search after
        // when comparing elements is cheap
        vec.sort_unstable_by(|a, b| a.key().cmp(b.key()));
        let duplicate = vec.windows(2).any(|w| w[0].key() == w[1].key());
        if duplicate {
            Err(MapOfIndexesError::DuplicateKeys)
        } else {
            Ok(Self { inner: vec })
        }
    }
}

impl<T: KeyValue> MapOfIndexes<T> {
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Vec::with_capacity(capacity),
        }
    }

    pub fn push(&mut self, element: T) {
        if let Some(last) = self.inner.last() {
            println!("{:?}", last.key());
            if last.key() >= element.key() {
                panic!(
                    "Attempted to push a lower element {:?}, last element value is: {:?}",
                    element.key(),
                    last.key()
                );
            }
        }
        self.inner.push(element)
    }

    fn get_idx(&self, key: &T::K) -> Option<usize> {
        if self.inner.len() == 0 {
            return None;
        }
        let mut idx = self.inner.len() / 2;
        for _ in 0..std::mem::size_of::<usize>() * 8 - self.inner.len().leading_zeros() as usize {
            // to handle 32bit targets
            match self.inner[idx].key().cmp(key) {
                Ordering::Less => idx = std::cmp::min(idx * 2, self.inner.len() - 1),
                Ordering::Greater => idx /= 2,
                Ordering::Equal => return Some(idx),
            }
        }
        None
    }

    pub fn get(&self, key: &T::K) -> Option<&T::V> {
        self.get_idx(key).map(|idx| self.inner[idx].value())
    }

    pub fn set(&mut self, element: T) {
        if let Some(idx) = self.get_idx(element.key()) {
            self.inner[idx] = element
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_push() {
        let mut v = Vec::<(i128, u8)>::new();
        v.push((1, 1));
        v.push((2, 1));
        assert_eq!(&v, &[(1, 1), (2, 1)]);
    }

    #[test]
    fn test_push_sorted() {
        let mut s = MapOfIndexes::<(i128, u8)>::new();
        s.push((1, 1));
        s.push((2, 1));
        assert_eq!(&s.inner, &[(1, 1), (2, 1)]);
    }

    #[test]
    fn test_get_1() {
        let mut s = MapOfIndexes::<(i128, u8)>::new();
        s.push((10, 10));
        s.push((11, 11));
        s.push((12, 12));
        s.push((13, 13));
        for i in 10..14 {
            assert_eq!(s.get(&(i as i128)), Some(&(i as u8)));
        }
    }
    #[test]
    fn test_get_2() {
        let mut s = MapOfIndexes::<(u8, u8)>::new();
        for i in 0..u8::MAX {
            s.push((i, i));
            assert_eq!(s.get(&i), Some(&i));
        }
    }

    #[test]
    #[should_panic]
    fn test_push_sorted_panic() {
        let mut s = MapOfIndexes::<(i128, u8)>::new();
        s.push((1, 1));
        s.push((-100, 1));
    }

    #[test]
    fn test_try_from() {
        let mut s = Vec::<(i32, u64)>::new();
        s.push((1, 1));
        s.push((-100, 2));
        s.push((3, 15));
        let sorted_map: MapOfIndexes<(i32, u64)> = s.try_into().unwrap();
        assert_eq!(&sorted_map.inner, &[(-100, 2), (1, 1), (3, 15)])
    }

    #[test]
    fn test_try_from_fail_duplicate() {
        let mut s = Vec::<(i32, u64)>::new();
        s.push((1, 1));
        s.push((1, 2));
        s.push((3, 15));
        let sorted_map_err = MapOfIndexes::<(i32, u64)>::try_from(s).err().unwrap();
        assert_eq!(sorted_map_err, MapOfIndexesError::DuplicateKeys)
    }

    #[test]
    fn test_set() {
        let mut s = MapOfIndexes::<(u16, u16)>::new();
        s.push((10, 10));
        s.push((11, 11));
        s.push((12, 12));
        s.push((13, 13));
        s.set((10, 100));
        assert_eq!(&s.inner, &[(10, 100), (11, 11), (12, 12), (13, 13)])
    }
}
