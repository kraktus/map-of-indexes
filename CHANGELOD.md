# Changelog for map-of-indexes

## v0.1.4


- Fix `get_element` and `get_value` search, internally use `Vec::binary_search_by` instead of reinventing the wheel

## v0.1.3


- Rename `MapOfIndexes<T>::get` to `MapOfIndexes<T>::get_element`, not to overshadow `Vec::get`

## v0.1.2


- `MapOfIndexes<T>::get_value` returns `Option<T::V>`. Previous behavior of `MapOfIndexes<T>::get`

- `MapOfIndexes<T>::get` now returns `Option<&T>`


## v0.1.1

- `CombinedKeyValue::new` now panics if `key` or `value` out of assigned bounds