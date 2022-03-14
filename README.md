# Map-of-indexes

[![crates.io](https://img.shields.io/crates/v/map-of-indexes.svg)](https://crates.io/crates/map-of-indexes)
[![docs.rs](https://docs.rs/map-of-indexes/badge.svg)](https://docs.rs/map-of-indexes)

A small utility crate when you have a list of unique but not dense indexes for which to each you want to associates a value.
In the documentation the indexes are referred as `key`. *Not* an indexed map!

It can be considered a slower but more compact version of [`BTreeMap`](std::collections::BTreeMap).
## Examples
A brief example of the crate's capacities
```rust
use map_of_indexes::{MapOfIndexes, MapOfIndexesError, KeyValue};

let v = vec![(3, 4), (1, 2), (5, 6)];
let mut map: MapOfIndexes::<(u8, u16)> = v.try_into()?;

map.push((7,8));
let push_res = map.push_checked((0,9));
assert_eq!(push_res, Err(MapOfIndexesError::SmallerKey));

let old_key_value = map.set((1,9))?;
assert_eq!(old_key_value.key(), &1);
assert_eq!(old_key_value.value(), &2);
```
[`CombinedKeyValue`](crate::CombinedKeyValue) is a compact representation when you need to save space.
```rust
use map_of_indexes::{CombinedKeyValue};
// We have keys that take up to 40 bits, and value up to 24;
// Using (u64, u64) would have wasted 8 byte per entry.
type CombinedU64 = CombinedKeyValue<u64, 40, 24>;
CombinedU64::safety_check(); // ensure that key and value size fit on the unsigned integer.

let v = vec![CombinedU64::new(3u64, 4u32), CombinedU64::new(1u64, 2u32), CombinedU64::new(5u64, 6u32)];
let map: MapOfIndexes<_> = v.try_into()?;
let inner_raw: Vec<u64> = Vec::from_iter(map.iter().map(|x| *x.as_ref()));
assert_eq!(inner_raw, vec![2199023255553, 4398046511107, 6597069766661]);
```
For an even more compact representation, consider using the [`bitvec`](https://docs.rs/bitvec/latest/bitvec/index.html) crate.

License: AGPL-3.0+
