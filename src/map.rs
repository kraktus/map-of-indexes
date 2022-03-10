use num_traits::Unsigned;

#[derive(Clone, Debug)]
pub struct MapOfIndexes<T: Unsigned + std::cmp::Ord, const KEY_NB_BITS: usize> {
    inner: Vec<T>,
}

#[derive(Clone, Debug)]
pub struct SortedMapOfIndexes<T: Unsigned + std::cmp::Ord, const KEY_NB_BITS: usize> {
    inner: Vec<T>,
}

impl<T: Unsigned + std::cmp::Ord, const KEY_NB_BITS: usize> MapOfIndexes<T, KEY_NB_BITS> {
    fn push(&mut self, element: T) {
        self.inner.push(element);
    }
}

impl<T: Unsigned + std::cmp::Ord, const KEY_NB_BITS: usize> From<MapOfIndexes<T, KEY_NB_BITS>>
    for SortedMapOfIndexes<T, KEY_NB_BITS>
{
    fn from(mut map_of_index: MapOfIndexes<T, KEY_NB_BITS>) -> Self {
        map_of_index.inner.sort();
        Self {
            inner: map_of_index.inner,
        }
    }
}

impl<T: Unsigned + std::cmp::Ord, const KEY_NB_BITS: usize> SortedMapOfIndexes<T, KEY_NB_BITS> {
    fn push(&mut self, element: T) {
    	if self.inner.last().map(|x| x >= element).unwrap_or(false) {
    		panic!("Attempted to push a lower element {:?}, last element value is: ", element, self.inner.last());
    	}
    }
}