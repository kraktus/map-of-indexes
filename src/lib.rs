use std::cmp::Ordering;
use std::fmt::Debug;
use thiserror::Error;

const USIZE_NB_BITS: usize = std::mem::size_of::<usize>() * 8;

pub trait KeyValue<'a> {
    type K: Ord;
    type V;
    fn key(&'a self) -> Self::K;
    fn value(&'a self) -> Self::V;
}

impl<'a, KEY: Ord + Debug, VALUE> KeyValue<'a> for (KEY, VALUE)
where
    KEY: 'a,
    VALUE: 'a,
{
    type K = &'a KEY;
    type V = &'a VALUE;
    fn key(&'a self) -> Self::K {
        &self.0
    }
    fn value(&'a self) -> Self::V {
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

impl<T: for<'a> KeyValue<'a>> Default for MapOfIndexes<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: for<'a> KeyValue<'a>> TryFrom<Vec<T>> for MapOfIndexes<T> {
    type Error = MapOfIndexesError;

    fn try_from(mut vec: Vec<T>) -> Result<Self, Self::Error> {
        // Other solution was to check duplicate while sorting, supposedly faster to make linear search after
        // when comparing elements is cheap
        vec.sort_unstable_by(|a, b| a.key().cmp(&b.key()));
        let duplicate = vec.windows(2).any(|w| w[0].key() == w[1].key());
        if duplicate {
            Err(MapOfIndexesError::DuplicateKeys)
        } else {
            Ok(Self { inner: vec })
        }
    }
}

impl<T: for<'a> KeyValue<'a>> MapOfIndexes<T> {
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
            if last.key() >= element.key() {
                panic!("Attempted to push an element with a lower key than last element");
            }
        }
        self.inner.push(element)
    }

    fn get_idx<'a>(&'a self, key: <T as KeyValue<'a>>::K) -> Option<usize> {
        if self.inner.len() == 0 {
            return None;
        }
        let mut idx = self.inner.len() / 2;
        for _ in 0..USIZE_NB_BITS - self.inner.len().leading_zeros() as usize {
            // to handle 32bit targets
            match self.inner[idx].key().cmp(&key) {
                Ordering::Less => idx = std::cmp::min(idx * 2, self.inner.len() - 1),
                Ordering::Greater => idx /= 2,
                Ordering::Equal => return Some(idx),
            }
        }
        None
    }

    pub fn get<'a>(&'a self, key: <T as KeyValue<'a>>::K) -> Option<<T as KeyValue<'_>>::V> {
        self.get_idx(key).map(|idx| self.inner[idx].value())
    }

    pub fn set(&mut self, element: T) {
        if let Some(idx) = self.get_idx(element.key()) {
            self.inner[idx] = element
        }
    }
}

// TODO https://nora.codes/post/its-time-to-get-hyped-about-const-generics-in-rust/ statically check if mem_size<T> * 8 >= KEY_NB_BITS
pub struct CombinedKeyValue<T, const KEY_NB_BITS: usize, const VALUE_NB_BITS: usize>(T);

// If `KEY_NB_BITS` and `VALUE_NB_BITS` are compatible with backed type, `TryFrom<usize>` should never fail.
impl<T: TryFrom<usize> + Into<usize>, const KEY_NB_BITS: usize, const VALUE_NB_BITS: usize>
    CombinedKeyValue<T, { KEY_NB_BITS }, { VALUE_NB_BITS }>
where
    <T as TryFrom<usize>>::Error: Debug,
{
    // To be run once after defining a type alias.
    // TODO use Macro instead(?)
    pub fn safety_check() {
        if std::mem::size_of::<T>() * 8 < KEY_NB_BITS + VALUE_NB_BITS {
            panic!("KEY_NB_BITS value is higher than the number of bits of the backup type.");
        }
    }

    /// panics if `value` has more bits than `KEY_NB_BITS`
    pub fn new<K: Into<usize>, V: Into<usize>>(key: K, value: V) -> Self {
        // TODO assert key and value have less bits than defined in the type
        Self(
            T::try_from(key.into() | (value.into() << KEY_NB_BITS))
                .expect("Run `Self::safety_check` and should never panic"),
        )
    }
}

impl<'a, T: TryFrom<usize> + Ord + Copy, const KEY_NB_BITS: usize, const VALUE_NB_BITS: usize>
    KeyValue<'a> for CombinedKeyValue<T, { KEY_NB_BITS }, { VALUE_NB_BITS }>
where
    usize: From<T>,
    <T as TryFrom<usize>>::Error: Debug,
{
    type K = T;
    type V = T;
    fn key(&self) -> Self::K {
        T::try_from(usize::from(self.0) & (usize::MAX >> (USIZE_NB_BITS - KEY_NB_BITS)))
            .expect("Run `Self::safety_check` and should never panic")
    }
    fn value(&self) -> Self::V {
        T::try_from(usize::from(self.0) >> KEY_NB_BITS)
            .expect("Run `Self::safety_check` and should never panic")
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

    #[test]
    fn test_combined_key_value_type() {
        type CombinedU8 = CombinedKeyValue<u8, 4, 4>;
        CombinedU8::safety_check();
    }

    #[test]
    #[should_panic]
    fn test_combined_key_value_type_error_key() {
        type CombinedU8 = CombinedKeyValue<u8, 5, 4>;
        CombinedU8::safety_check();
    }

    #[test]
    #[should_panic]
    fn test_combined_key_value_type_error_value() {
        type CombinedU8 = CombinedKeyValue<u8, 4, 5>;
        CombinedU8::safety_check();
    }

    // #[test]
    // #[should_panic] // should not compile
    // fn test_combined_key_value_type_error_only_uints() {
    //     type CombinedU8 = CombinedKeyValue<i8, 4, 4>; // Replace by doc tests
    //     CombinedU8::safety_check();
    // }

    #[test]
    fn test_combined_key_value_new() {
        type CombinedU8 = CombinedKeyValue<u8, 4, 4>;
        CombinedU8::safety_check();
        let x = CombinedU8::new(4u8, 3u8);
        assert_eq!(x.key(), 4u8);
        assert_eq!(x.value(), 3u8);
    }
}
