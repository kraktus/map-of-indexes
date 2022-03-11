use std::cmp::Ordering;
use std::fmt::Debug;

pub trait KeyValue {
    type K: Ord + Debug;
    type V;
    fn key(&self) -> &Self::K;
    fn value(&self) -> &Self::V;
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

    fn push(&mut self, element: T) {
        self.inner.push(element);
    }
}

impl<T: KeyValue> From<MapOfIndexes<T>> for SortedMapOfIndexes<T> {
    fn from(mut map_of_index: MapOfIndexes<T>) -> Self {
        map_of_index.inner.sort_by(|a, b| a.key().cmp(b.key()));
        Self {
            inner: map_of_index.inner,
        }
    }
}

impl<T: KeyValue> SortedMapOfIndexes<T> {
    fn push(&mut self, element: T) {
        if let Some(last) = self.inner.last() {
            if last.key() <= element.key() {
                panic!(
                    "Attempted to push a lower element {:?}, last element value is: {:?}",
                    element.key(),
                    last.key()
                );
            }
        }
    }

    fn get(&self, key: T::K) -> &T::V {
        let mut idx = self.inner.len() / 2;
        loop {
            match self.inner[idx].key().cmp(&key) {
                Ordering::Less => idx *= 2,
                Ordering::Greater => idx /= 2,
                Ordering::Equal => return &self.inner[idx].value(),
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn name() {
        MapOfIndexes::<u8>::new();
    }
}
