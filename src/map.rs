use paste::paste;

macro_rules! impl_for {
	($($struct_name:ident, $u:ty,)+) => {$(
paste! {
#[derive(Clone, Debug)]
pub struct [<MapOfIndexes $struct_name>] <const KEY_NB_BITS: usize> {
    inner: Vec<$u>,
}

#[derive(Clone, Debug)]
pub struct [<SortedMapOfIndexes $struct_name>]<const KEY_NB_BITS: usize> {
    inner: Vec<$u>,
}

impl<const KEY_NB_BITS: usize> [<MapOfIndexes $struct_name>]<KEY_NB_BITS> {
    pub fn new() -> Self {
        Self {inner: Vec::new()}
    }

    fn push(&mut self, element: $u) {
        self.inner.push(element);
    }
}

impl<const KEY_NB_BITS: usize> From<[<MapOfIndexes $struct_name>]<KEY_NB_BITS>>
    for [<SortedMapOfIndexes $struct_name>]<KEY_NB_BITS>
{
    fn from(mut map_of_index: [<MapOfIndexes $struct_name>]<KEY_NB_BITS>) -> Self {
        map_of_index.inner.sort();
        Self {
            inner: map_of_index.inner,
        }
    }
}

impl<const KEY_NB_BITS: usize> [<SortedMapOfIndexes $struct_name>]<KEY_NB_BITS> {
    fn push(&mut self, element: $u) {
    	if self.inner.last().map(|x| x >= &element).unwrap_or(false) {
    		panic!("Attempted to push a lower element {:?}, last element value is: {:?}", element, self.inner.last());
    	}
    }
}
}
)+}}

impl_for! {U8, u8, U16, u16, U32, u32, U64, u64, U128, u128, Usize, usize,}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn name() {
        MapOfIndexesU8::<12>::new();
    }
}
