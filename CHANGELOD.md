# Changelog for map-of-indexes

## v0.1.3


- Rename `MapOfIndexes<T>::get` to `MapOfIndexes<T>::get_element`, not to overshadow `Vec::get`

## v0.1.2


- `MapOfIndexes<T>::get_value` returns `Option<T::V>`. Previous behavior of `MapOfIndexes<T>::get`

- `MapOfIndexes<T>::get` now returns `Option<&T>`


## v0.1.1

- `CombinedKeyValue::new` now panics if `key` or `value` out of assigned bounds