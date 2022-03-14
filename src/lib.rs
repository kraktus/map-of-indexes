//! # Map-of-indexes
//!
//! A small utility crate when you have a list of unique but not dense indexes for which to each you want to associates a value.
//! In the documentation the indexes are referred as `key`.
//!
//! It can be considered a slower but more compact version of [`BTreeMap`](std::collections::BTreeMap).
//! # Examples
//! A brief example of the crate's capacities
//! ```
//! use map_of_indexes::{MapOfIndexes, MapOfIndexesError, KeyValue};
//!
//! # fn main() -> Result<(), MapOfIndexesError> {
//! let v = vec![(3, 4), (1, 2), (5, 6)];
//! let mut map: MapOfIndexes::<(u8, u16)> = v.try_into()?;
//!
//! map.push((7,8));
//! let push_res = map.push_checked((0,9));
//! assert_eq!(push_res, Err(MapOfIndexesError::SmallerKey));
//!
//! let old_key_value = map.set((1,9))?;
//! assert_eq!(old_key_value.key(), &1);
//! assert_eq!(old_key_value.value(), &2);
//! # Ok(())
//! # }
//! ```
//! [`CombinedKeyValue`](crate::CombinedKeyValue) is a compact representation when you need to save space.
//! ```
//! # use map_of_indexes::{MapOfIndexes, MapOfIndexesError, KeyValue};
//! use map_of_indexes::{CombinedKeyValue};
//! # fn main() -> Result<(), MapOfIndexesError> {
//! // We have keys that take up to 40 bits, and value up to 24;
//! // Using (u64, u64) would have wasted 8 byte per entry.
//! type CombinedU64 = CombinedKeyValue<u64, 40, 24>;
//! CombinedU64::safety_check(); // ensure that key and value size fit on the unsigned integer.
//!
//! let v = vec![CombinedU64::new(3u64, 4u32), CombinedU64::new(1u64, 2u32), CombinedU64::new(5u64, 6u32)];
//! let map: MapOfIndexes<_> = v.try_into()?;
//! let inner_raw: Vec<u64> = Vec::from_iter(map.iter().map(|x| *x.as_ref()));
//! assert_eq!(inner_raw, vec![2199023255553, 4398046511107, 6597069766661]);
//! # Ok(())
//! # }
//! ```
//! For an even more compact representation, consider using the [`bitvec`](https://docs.rs/bitvec/latest/bitvec/index.html) crate.

#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![allow(clippy::semicolon_if_nothing_returned)]
// #![allow(clippy::missing_panics_doc)]
// #![allow(clippy::missing_errors_doc)]

use std::cmp::Ordering;
use std::fmt::{Debug};
use std::ops::Deref;

use thiserror::Error;

/// Trait that `T` must implement to be able to work with [`MapOfIndexes`](crate::MapOfIndexes) of `T`.
///
/// Can be implemented on your own custom structs. `KeyValue::K` represents the key (index) of the pair, while `KeyValue::V` is the value.
///
/// [`KeyValue`](crate::KeyValue) is already implemented for all 2-tuples, the first element being considered as the key.
/// # Examples
/// ```
/// use map_of_indexes::KeyValue;
///
/// let tuple: (String, i64) = ("Key".to_string(), 123);
/// // In this blanket implementation, both functions return a reference
/// assert_eq!(tuple.key(), &"Key");
/// assert_eq!(tuple.value(), &123i64);
/// ```
///
/// If you need a very compact representation, see [`CombinedKeyValue`](crate::CombinedKeyValue), which stores both the key and the key on a uint of a given size.
// #[doc(notable_trait)]
pub trait KeyValue<'a> {
    type K: Ord;
    type V;
    fn key(&'a self) -> Self::K;
    fn value(&'a self) -> Self::V;
}

impl<'a, KEY: Ord, VALUE> KeyValue<'a> for (KEY, VALUE)
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

#[derive(Error, Debug, PartialEq, Eq, Hash)]
pub enum MapOfIndexesError {
    #[error("At least two elements with same keys. Keys must be uniques.")]
    DuplicateKeys,
    #[error("No elements were found with this key.")]
    KeyNotFound,
    #[error("Attempted to push an element with a lower key than last element.")]
    SmallerKey,
}

/// Basically a sorted vec
#[derive(Clone, Debug)]
pub struct MapOfIndexes<T> {
    inner: Vec<T>,
}

impl<T> Deref for MapOfIndexes<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T: for<'a> KeyValue<'a>> Default for MapOfIndexes<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Under the hood, will sort the vec by key. Will succeed if there are no elements with the same key
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
    #[must_use]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Vec::with_capacity(capacity),
        }
    }

    /// Push an element to the map. Panic if the pushed key is smaller than the last element's one.
    /// # Panics
    /// ```should_panic
    /// use map_of_indexes::MapOfIndexes;
    ///
    /// let mut m: MapOfIndexes<(isize, &'static str)> = MapOfIndexes::new();
    /// m.push((1, "cool"));
    /// m.push((-10, "panic!"));
    /// ```
    #[inline]
    pub fn push(&mut self, element: T) {
        match self.push_checked(element) {
            Ok(()) => (),
            Err(err) => panic!("{}", err),
        }
    }

    /// Push an element to the map. Return an Error if the pushed key is smaller than the last element's one.
    /// # Example
    /// ```
    /// use map_of_indexes::{MapOfIndexes, MapOfIndexesError};
    ///
    /// let mut m: MapOfIndexes<(isize, &'static str)> = MapOfIndexes::new();
    /// m.push((1, "cool"));
    /// let err = m.push_checked((-10, "err!"));
    /// assert_eq!(err, Err(MapOfIndexesError::SmallerKey))
    /// ```
    pub fn push_checked(&mut self, element: T) -> Result<(), MapOfIndexesError> {
        if let Some(last) = self.last() {
            if last.key() >= element.key() {
                return Err(MapOfIndexesError::SmallerKey);
            }
        }
        self.inner.push(element);
        Ok(())
    }

    fn get_idx<'a>(&'a self, key: <T as KeyValue<'a>>::K) -> Option<usize> {
        if self.is_empty() {
            return None;
        }
        let mut idx = self.len() / 2;
        for _ in 0..usize::BITS as usize - self.len().leading_zeros() as usize {
            // We're basing that on usize to handle non 64 bits targets
            match self[idx].key().cmp(&key) {
                Ordering::Less => idx = std::cmp::min(idx * 2, self.len() - 1),
                Ordering::Greater => idx /= 2,
                Ordering::Equal => return Some(idx),
            }
        }
        None
    }

    /// Performs a dichotomial search and returns the value
    pub fn get<'a>(&'a self, key: <T as KeyValue<'a>>::K) -> Option<<T as KeyValue<'_>>::V> {
        self.get_idx(key).map(|idx| self[idx].value())
    }

    /// Find and replace the key-value element, returning the previous key-value if found, or an error otherwise.
    pub fn set(&mut self, element: T) -> Result<T, MapOfIndexesError> {
        self.get_idx(element.key())
            .map(|idx| std::mem::replace(&mut self.inner[idx], element))
            .ok_or(MapOfIndexesError::KeyNotFound)
    }
}

/// A compact struct that implement [`KeyValue`](crate::KeyValue)
///
/// Both the key and value are stored on the same element which can be any unsigned integer.
///
/// # Examples
///
/// ```
/// # use map_of_indexes::{MapOfIndexes, MapOfIndexesError, KeyValue};
/// use map_of_indexes::{CombinedKeyValue};
/// # fn main() -> Result<(), MapOfIndexesError> {
/// // We have keys that take up to 40 bits, and value up to 24;
/// // Using (u64, u64) would have wasted 8 byte per entry.
/// type CombinedU64 = CombinedKeyValue<u64, 40, 24>;
/// CombinedU64::safety_check(); // ensure that key and value size fit on the unsigned integer.
///
/// let v = vec![CombinedU64::new(3u64, 4u32), CombinedU64::new(1u64, 2u32), CombinedU64::new(5u64, 6u32)];
/// let map: MapOfIndexes<_> = v.try_into()?;
/// let inner_raw: Vec<u64> = Vec::from_iter(map.iter().map(|x| *x.as_ref()));
/// assert_eq!(inner_raw, vec![2199023255553, 4398046511107, 6597069766661]);
/// # Ok(())
/// # }
/// ```
///
/// Not working with signed integer
/// ```compile_fail
/// use map_of_indexes::CombinedKeyValue;
///
/// // Will not be able to be instanciated
/// type CombinedI8 = CombinedKeyValue<i8, 4, 4>;
/// let combined = CombinedI8::new(-10, 3);
/// ```
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub struct CombinedKeyValue<T, const KEY_NB_BITS: u8, const VALUE_NB_BITS: u8>(T);

// TODO, make that work
// impl<'a, T, const KEY_NB_BITS: u8, const VALUE_NB_BITS: u8> Debug for CombinedKeyValue<T, KEY_NB_BITS, VALUE_NB_BITS> where CombinedKeyValue<T, KEY_NB_BITS, VALUE_NB_BITS>: KeyValue<'a> + Debug{
//     fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
//         write!(f, "CombinedKeyValue<{},{},{}> {{ key: {:?}, value: {:?} }}", std::any::type_name::<T>(), KEY_NB_BITS, VALUE_NB_BITS, self.key(), self.value())
//     }
// }

impl<T, const KEY_NB_BITS: u8, const VALUE_NB_BITS: u8> AsRef<T>
    for CombinedKeyValue<T, KEY_NB_BITS, VALUE_NB_BITS>
{
    fn as_ref(&self) -> &T {
        &self.0
    }
}

// If `KEY_NB_BITS` and `VALUE_NB_BITS` are compatible with backed type, `TryFrom<u128>` should never fail.
impl<T: TryFrom<u128> + Into<u128>, const KEY_NB_BITS: u8, const VALUE_NB_BITS: u8>
    CombinedKeyValue<T, { KEY_NB_BITS }, { VALUE_NB_BITS }>
where
    <T as TryFrom<u128>>::Error: Debug,
{
    // To be run once after defining a type alias.
    // TODO use Macro instead(?)
    pub fn safety_check() {
        assert!(
            !(std::mem::size_of::<T>() * 8 < (KEY_NB_BITS + VALUE_NB_BITS).into()),
            "KEY_NB_BITS + VALUE_NB_BITS value is higher than the number of bits of the backup type."
        );
    }

    /// panics if `value` has more bits than `KEY_NB_BITS`
    pub fn new<K: Into<u128>, V: Into<u128>>(key: K, value: V) -> Self {
        // TODO assert key and value have less bits than defined in the type
        Self(
            T::try_from(key.into() | (value.into() << KEY_NB_BITS))
                .expect("Run `Self::safety_check` and should never panic"),
        )
    }
}

impl<'a, T: TryFrom<u128> + Ord + Copy, const KEY_NB_BITS: u8, const VALUE_NB_BITS: u8> KeyValue<'a>
    for CombinedKeyValue<T, { KEY_NB_BITS }, { VALUE_NB_BITS }>
where
    u128: From<T>,
    <T as TryFrom<u128>>::Error: Debug,
{
    type K = T;
    type V = T;
    fn key(&self) -> Self::K {
        T::try_from(u128::from(self.0) & (u128::MAX >> (u128::BITS - u32::from(KEY_NB_BITS))))
            .expect("Run `Self::safety_check` and should never panic")
    }
    fn value(&self) -> Self::V {
        T::try_from(u128::from(self.0) >> KEY_NB_BITS)
            .expect("Run `Self::safety_check` and should never panic")
    }
}

#[cfg(test)]
mod test {
    use super::*;

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
            assert_eq!(s.get(&i128::from(i)), Some(&(i as u8)));
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
    fn test_try_from() {
        let s: Vec<(i32, u64)> = vec![(1, 1), (-100, 2), (3, 15)];
        let sorted_map: MapOfIndexes<(i32, u64)> = s.try_into().unwrap();
        assert_eq!(&sorted_map.inner, &[(-100, 2), (1, 1), (3, 15)])
    }

    #[test]
    fn test_try_from_fail_duplicate() {
        let s: Vec<(i32, u64)> = vec![(1, 1), (1, 2), (3, 15)];
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
        let old_key_value = s.set((10, 100)).unwrap();
        assert_eq!(old_key_value, (10, 10));
        assert_eq!(&s.inner, &[(10, 100), (11, 11), (12, 12), (13, 13)]);
    }

    #[test]
    fn test_set_err() {
        let mut s = MapOfIndexes::<(&'static str, &'static str)>::new();
        s.push(("test", "value"));
        let err = s
            .set(("key does not exist", "err must be returned"))
            .err()
            .unwrap();
        assert_eq!(err, MapOfIndexesError::KeyNotFound);
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

    #[test]
    fn test_combined_key_value_new() {
        type CombinedU8 = CombinedKeyValue<u8, 4, 4>;
        CombinedU8::safety_check();
        let x = CombinedU8::new(4u8, 3u8);
        assert_eq!(x.key(), 4u8);
        assert_eq!(x.value(), 3u8);
    }
}
