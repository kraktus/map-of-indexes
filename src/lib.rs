use std::cmp::Ordering;
use std::fmt::Debug;
use thiserror::Error;

pub trait KeyValue {
    type K: Ord + Debug;
    type V;
    fn key(&self) -> &Self::K;
    fn value(&self) -> &Self::V;
}

// implementation of `KeyValue` for all combinations of tuple of integers
include!(concat!(env!("OUT_DIR"), "/lib.rs")); // generated by build.rs

#[derive(Error, Debug, PartialEq, Eq)]
pub enum MapOfIndexesError {
    #[error("At least two elements with same keys. Keys must be uniques.")]
    DuplicateKeys,
}

#[derive(Clone, Debug)]
pub struct MapOfIndexes<T> {
    inner: Vec<T>,
}

#[derive(Clone, Debug)]
pub struct SortedMapOfIndexes<T> {
    inner: Vec<T>,
}

impl<T: KeyValue> MapOfIndexes<T> {
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    pub fn push(&mut self, element: T) {
        self.inner.push(element);
    }
}

impl<T: KeyValue> TryFrom<MapOfIndexes<T>> for SortedMapOfIndexes<T> {
    type Error = MapOfIndexesError;

    fn try_from(mut map_of_index: MapOfIndexes<T>) -> Result<Self, Self::Error> {
        // Other solution was to check duplicate while sorting
        map_of_index
            .inner
            .sort_unstable_by(|a, b| a.key().cmp(b.key()));
        let duplicate = map_of_index.inner.windows(2).any(|w| w[0].key() == w[1].key());
        if duplicate {
            Err(MapOfIndexesError::DuplicateKeys)
        } else {
            Ok(Self {
                inner: map_of_index.inner,
            })
        }
    }
}

impl<T: KeyValue> SortedMapOfIndexes<T> {
    pub fn new() -> Self {
        Self { inner: Vec::new() }
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

    pub fn get(&self, key: T::K) -> Option<&T::V> {
        if self.inner.len() == 0 {
            return None;
        }
        let mut idx = self.inner.len() / 2;
        for _ in 0..std::mem::size_of::<usize>() * 8 - self.inner.len().leading_zeros() as usize {
            // to handle 32bit targets
            match self.inner[idx].key().cmp(&key) {
                Ordering::Less => idx = std::cmp::min(idx * 2, self.inner.len() - 1),
                Ordering::Greater => idx /= 2,
                Ordering::Equal => return Some(self.inner[idx].value()),
            }
        }
        None
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_init() {
        MapOfIndexes::<(u8, u8)>::new();
    }

    #[test]
    fn test_push() {
        let mut s = MapOfIndexes::<(i128, u8)>::new();
        s.push((1, 1));
        s.push((2, 1));
        assert_eq!(&s.inner, &[(1, 1), (2, 1)]);
    }

    #[test]
    fn test_push_sorted() {
        let mut s = SortedMapOfIndexes::<(i128, u8)>::new();
        s.push((1, 1));
        s.push((2, 1));
        assert_eq!(&s.inner, &[(1, 1), (2, 1)]);
    }

    #[test]
    fn test_get_1() {
        let mut s = SortedMapOfIndexes::<(i128, u8)>::new();
        s.push((10, 10));
        s.push((11, 11));
        s.push((12, 12));
        s.push((13, 13));
        for i in 10..14 {
            assert_eq!(s.get(i as i128), Some(&(i as u8)));
        }
    }
    #[test]
    fn test_get_2() {
        let mut s = SortedMapOfIndexes::<(u8, u8)>::new();
        for i in 0..u8::MAX {
            s.push((i, i));
            assert_eq!(s.get(i), Some(&i));
        }
    }

    #[test]
    #[should_panic]
    fn test_push_sorted_panic() {
        let mut s = SortedMapOfIndexes::<(i128, u8)>::new();
        s.push((1, 1));
        s.push((-100, 1));
    }

    #[test]
    fn try_from() {
        let mut s = MapOfIndexes::<(i32, u64)>::new();
        s.push((1, 1));
        s.push((-100, 2));
        s.push((3, 15));
        let sorted_map: SortedMapOfIndexes::<(i32, u64)> = s.try_into().unwrap();
        assert_eq!(&sorted_map.inner, &[(-100, 2), (1, 1), (3, 15)])
    }

    #[test]
    fn try_from_fail_duplicate() {
        let mut s = MapOfIndexes::<(i32, u64)>::new();
        s.push((1, 1));
        s.push((1, 2));
        s.push((3, 15));
        let sorted_map_err = SortedMapOfIndexes::<(i32, u64)>::try_from(s).err().unwrap();
        assert_eq!(sorted_map_err, MapOfIndexesError::DuplicateKeys)
    }
}
