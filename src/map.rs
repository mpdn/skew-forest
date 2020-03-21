use crate::forest::{Index, SkewForest, SkewIndex};
use std::cmp::Ordering;

/// A mapping from the nodes in a `SkewForest` to values.
///
/// # Synchronization
///
/// The `SkewMap` must be kept synchronized with the underlying `SkewForest`. This means that when
/// a node is pushed onto a path in the `SkewForest`, then a value must also be pushed onto this
/// `SkewMap`.
/// 
/// # Example
/// 
/// ```
/// use skew_forest::{SkewForest, SkewPath, SkewPathNode, SkewMap};
/// 
/// let mut forest = SkewForest::default();
/// let mut path = SkewPath::<[SkewPathNode; 8]>::default();
/// let mut map = SkewMap::default();
/// 
/// map.push(forest.push(&mut path), "some value");
/// map.push(forest.push(&mut path), "some other value");
/// 
/// assert_eq!(
///     forest.iter(&path).map(|ix| map[ix]).collect::<Vec<_>>(),
///     vec!["some value", "some other value"],
/// );
/// ```
#[derive(Default, Clone, Debug)]
pub struct SkewMap<T> {
    inner: Vec<T>,
    leaves: Vec<T>,
}

impl<T> SkewMap<T> {
    fn vec(&self, is_leaf: bool) -> &Vec<T> {
        if is_leaf {
            &self.leaves
        } else {
            &self.inner
        }
    }

    fn vec_mut(&mut self, is_leaf: bool) -> &mut Vec<T> {
        if is_leaf {
            &mut self.leaves
        } else {
            &mut self.inner
        }
    }

    /// Synchronizes this `SkewMap` with the given `SkewForest`, inserting new elements by calling
    /// a function.
    /// 
    /// # Example
    /// 
    /// ```
    /// use skew_forest::{SkewForest, SkewPath, SkewPathNode, SkewMap};
    /// 
    /// let mut forest = SkewForest::default();
    /// let mut path = SkewPath::<[SkewPathNode; 8]>::default();
    /// let mut map = SkewMap::default();
    /// 
    /// forest.push(&mut path);
    /// 
    /// // A value has been inserted in the forest without being inserted in the map - they are not
    /// // synchronized!
    /// assert!(!map.is_synchronized(&forest));
    /// 
    /// map.synchronize(&forest, || "some value");
    /// 
    /// // A value for each node has been inserted - we are synchronized again.
    /// assert!(map.is_synchronized(&forest));
    /// ```
    pub fn synchronize<Idx: Index>(&mut self, forest: &SkewForest<Idx>, mut f: impl FnMut() -> T) {
        let (inner_len, leaf_len) = forest.sizes();
        self.inner.resize_with(inner_len, &mut f);
        self.leaves.resize_with(leaf_len, f);
    }

    /// Whether this `SkewMap` is synchronized with the corresponding `SkewForest`.
    pub fn is_synchronized<Idx: Index>(&self, forest: &SkewForest<Idx>) -> bool {
        let (inner_len, leaf_len) = forest.sizes();
        self.inner.len() == inner_len && self.leaves.len() == leaf_len
    }

    /// Pushes a value with the given index onto this map. If the returned index is one that
    /// previously contained a value (due to being reused after garbage collected), then the old
    /// value is returned, otherwise `None`.
    ///
    /// # Panics
    ///
    /// May panic if the `SkewMap` was not synchronized with the `SkewForest` that created the
    /// `SkewIndex` prior to the push operation that created the `SkewIndex`.
    /// 
    /// # Example
    /// 
    /// ```
    /// use skew_forest::{SkewForest, SkewPath, SkewPathNode, SkewMap};
    /// 
    /// let mut forest = SkewForest::default();
    /// let mut path = SkewPath::<[SkewPathNode; 8]>::default();
    /// let mut map = SkewMap::default();
    /// 
    /// map.push(forest.push(&mut path), "some value");
    /// 
    /// assert_eq!(map[path.last().unwrap()], "some value");
    /// ```
    pub fn push<Idx: Index>(&mut self, index: SkewIndex<Idx>, value: T) -> Option<T> {
        let vec = self.vec_mut(index.is_leaf);
        let ix = index.index.index();

        match ix.cmp(&vec.len()) {
            Ordering::Less => Some(std::mem::replace(&mut vec[ix], value)),
            Ordering::Equal => {
                vec.push(value);
                None
            }
            Ordering::Greater => panic!("SkewMap must be synchronized with the forest"),
        }
    }
}

impl<T, Idx: Index> std::ops::Index<SkewIndex<Idx>> for SkewMap<T> {
    type Output = T;

    fn index(&self, index: SkewIndex<Idx>) -> &T {
        let vec = self.vec(index.is_leaf);
        &vec[index.index.index()]
    }
}

impl<T, Idx: Index> std::ops::IndexMut<SkewIndex<Idx>> for SkewMap<T> {
    fn index_mut(&mut self, index: SkewIndex<Idx>) -> &mut T {
        let vec = self.vec_mut(index.is_leaf);
        &mut vec[index.index.index()]
    }
}
