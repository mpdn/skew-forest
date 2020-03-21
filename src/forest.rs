use crate::bits::next_one;
use arrayvec::{Array, ArrayVec};
use debug_tag::DebugTag;
use fixedbitset::FixedBitSet;
use std::cmp::Ordering;
use std::convert::TryInto;
use std::fmt;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::Fuse;
use std::iter::FusedIterator;
use std::marker::PhantomData;

/// A type that can be used as a numeric index.
pub trait Index: Copy + Default + Hash + Ord + Debug + 'static {
    fn new(value: usize) -> Self;
    fn try_new(value: usize) -> Option<Self>;
    fn index(&self) -> usize;
}

macro_rules! impl_index {
    ($type:ty) => {
        impl Index for $type {
            fn new(value: usize) -> Self {
                value as $type
            }

            fn try_new(value: usize) -> Option<Self> {
                value.try_into().ok()
            }

            fn index(&self) -> usize {
                *self as usize
            }
        }
    };
}

impl_index!(u8);
impl_index!(u16);
impl_index!(u32);
impl_index!(u64);
impl_index!(usize);

#[derive(Debug)]
struct SkewTreeNode<Idx> {
    former: Idx,
    latter: Idx,
}

/// The shared structure of a set of skew-binary random access lists. See the module docs for more
/// details.
///
/// The type parameter `Idx` determines the size of the internal index type. This roughly determines
/// the number of nodes in the forest. See `try_push` for more details.
///
/// # Complexity
///
/// All operations on this structure has logarithmic time complexity in the size of the path.
///
/// # Panics
///
/// Any function on this structure having a `SkewPath` parameter expects that the `SkewPath` has not
/// been mutated by another `SkewForest`. I.e. `SkewPath` are implicitly bound to the `SkewForest`
/// that mutated them.
///
/// Failure to follow the above constraint can result in panics or arbitrary values being returned.
/// This is true for any function on this structure, and not just where it is explicitly written.
///
/// # Example
///
/// ```
/// use skew_forest::{SkewForest, SkewPath, SkewPathNode};
///
/// let mut forest = SkewForest::default();
/// let mut path = SkewPath::<[SkewPathNode; 8]>::default();
///
/// let node_a = forest.push(&mut path);
/// let node_b = forest.push(&mut path);
///
/// assert_eq!(
///     forest.iter(&path).collect::<Vec<_>>(),
///     vec![node_a, node_b],
/// );
/// ```
#[derive(Default, Debug)]
pub struct SkewForest<Idx = usize> {
    nodes: Vec<SkewTreeNode<Idx>>,
    inner_next: usize,
    inner_free: FixedBitSet,
    leaf_len: usize,
    leaf_next: usize,
    leaf_free: FixedBitSet,
    tag: DebugTag,
}

/// An error from pushing an element onto a `SkewPath`.
#[derive(Debug)]
pub enum PushError {
    /// The index type was out of bounds
    IndexOutOfBounds,

    /// The path array was out of bounds
    PathArrayOutOfBounds,
}

impl std::fmt::Display for PushError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PushError::IndexOutOfBounds => write!(f, "Index out of bounds"),
            PushError::PathArrayOutOfBounds => write!(f, "Path array out of bounds"),
        }
    }
}

impl std::error::Error for PushError {}

impl<Idx: Index> SkewForest<Idx> {
    /// Returns the inner and leaf sizes.
    pub(crate) fn sizes(&self) -> (usize, usize) {
        (self.nodes.len(), self.leaf_len)
    }

    /// Returns the number of nodes in this forest. The number of nodes in use *and* garbage
    /// collected are returned.
    pub fn size(&self) -> usize {
        let (inner, leaf) = self.sizes();
        inner + leaf
    }

    /// Panics in debug if the path does not come from this `SkewForest`
    fn assert_tag<A>(&self, path: &SkewPath<A>)
    where
        A: SkewPathArray<Idx = Idx>,
    {
        if path.len != 0 {
            assert_eq!(self.tag, path.tag, "Path must stem from this SkewForest")
        }
    }

    /// Tries to push a node onto a path, returning the index of the pushed value.
    ///
    /// This operation will return `Err` in two cases:
    /// - `PushError::IndexOutOfBounds` if `Idx` is out of bounds. This *may* happen when the number
    ///   of nodes exceeds the largest value of `Idx`, but it *may* only happen later.
    /// - `PushError::PathhArrayOutOfBounds` if `A` is out of bounds for the size of this path. This
    ///   *will* happen when `2.pow(A::len()) - 1 == path.len()`.
    pub fn try_push<A>(&mut self, path: &mut SkewPath<A>) -> Result<SkewIndex<Idx>, PushError>
    where
        A: SkewPathArray<Idx = Idx>,
    {
        self.assert_tag(path);

        let (ix, height) = match (path.trees.pop(), path.trees.pop()) {
            (Some(latter), Some(former)) if former.height == latter.height => {
                let node = SkewTreeNode {
                    former: former.node,
                    latter: latter.node,
                };

                let ix = if let Some(ix) = next_one(self.inner_free.as_slice(), self.inner_next) {
                    self.nodes[ix] = node;
                    self.inner_next = ix + 1;
                    ix
                } else {
                    let ix = self.nodes.len();
                    self.nodes.push(node);
                    ix
                };

                (ix, former.height + 1)
            }
            (latter, former) => {
                if let Some(former) = former {
                    path.trees.push(former);
                }

                if let Some(latter) = latter {
                    path.trees.push(latter);
                }

                let ix = if let Some(ix) = next_one(self.leaf_free.as_slice(), self.leaf_next) {
                    self.leaf_next = ix + 1;
                    ix
                } else {
                    let ix = self.leaf_len;
                    self.leaf_len += 1;
                    ix
                };

                (ix, 0)
            }
        };

        let ix = Idx::try_new(ix).ok_or(PushError::IndexOutOfBounds)?;

        path.trees
            .try_push(SkewPathNode { height, node: ix })
            .map_err(|_| PushError::PathArrayOutOfBounds)?;

        if path.len == 0 {
            path.tag = self.tag;
        }

        path.len += 1;

        Ok(SkewIndex {
            is_leaf: height == 0,
            index: ix,
        })
    }

    /// Push a new node onto this path.
    ///
    /// # Panic
    ///
    /// Panics if `Idx` becomes out of bounds or `A` becomes out of bounds. See `try_push` for more
    /// details.
    pub fn push<A>(&mut self, path: &mut SkewPath<A>) -> SkewIndex<Idx>
    where
        A: SkewPathArray<Idx = Idx>,
    {
        self.assert_tag(path);
        self.try_push(path).unwrap()
    }

    /// Clears any nodes in this forest. This forest will be considered a new forest, i.e.
    /// `SkewPath`s referring to the old `SkewForest` should not be used with this `SkewForest`
    /// again.
    pub fn clear(&mut self) {
        self.nodes.clear();
        self.inner_next = 0;
        self.inner_free.set_range(.., true);
        self.leaf_len = 0;
        self.leaf_next = 0;
        self.leaf_free.set_range(.., true);
        self.tag = DebugTag::new();
    }

    /// Removes the last node index from a `SkewPath`. Returns `None` if this `SkewPath` is empty.
    pub fn pop<A>(&self, path: &mut SkewPath<A>) -> Option<SkewIndex<Idx>>
    where
        A: SkewPathArray<Idx = Idx>,
    {
        self.assert_tag(path);
        path.pop(&self.nodes)
    }

    /// Retrieves a node index at an arbitrary offset. Returns `None` if the offset is out of
    /// bounds.
    pub fn try_get<A>(&self, path: &SkewPath<A>, mut offset: usize) -> Option<SkewIndex<Idx>>
    where
        A: SkewPathArray<Idx = Idx>,
    {
        self.assert_tag(path);
        let mut trees = path.trees.iter();
        let mut path_node;
        let mut size;

        loop {
            path_node = trees.next()?.clone();
            size = path_node.size();

            if offset < size {
                break;
            }

            offset -= size;
        }

        loop {
            let child_size = size / 2;
            if offset < child_size {
                path_node.node = self.nodes[path_node.node.index()].former;
            } else if offset < child_size * 2 {
                offset -= child_size;
                path_node.node = self.nodes[path_node.node.index()].latter;
            } else {
                break;
            }

            size = child_size;
            path_node.height -= 1
        }

        Some(SkewIndex {
            is_leaf: path_node.height == 0,
            index: path_node.node,
        })
    }

    /// Retrieves a node index at an arbitrary offset.DebugTag
    ///
    /// # Panics
    ///
    /// Panics if the offset is out of bounds.
    pub fn get<A>(&self, path: &SkewPath<A>, offset: usize) -> SkewIndex<Idx>
    where
        A: SkewPathArray<Idx = Idx>,
    {
        self.assert_tag(path);
        self.try_get(path, offset).expect("index out of bounds")
    }

    /// Truncate this path to the given length. If the length is longer than the current length,
    /// then no changes are made.
    /// 
    /// # Example
    /// 
    /// ```
    /// use skew_forest::{SkewForest, SkewPath, SkewPathNode, SkewMap};
    ///
    /// let mut forest = SkewForest::default();
    /// let mut path = SkewPath::<[SkewPathNode; 8]>::default();
    /// 
    /// let node_a = forest.push(&mut path);
    /// let node_b = forest.push(&mut path);
    /// 
    /// forest.truncate(&mut path, 1);
    /// 
    /// assert!(forest.iter(&path).eq(vec![node_a]));
    /// ```
    pub fn truncate<A>(&self, path: &mut SkewPath<A>, mut len: usize)
    where
        A: SkewPathArray<Idx = Idx>,
    {
        self.assert_tag(path);
        let mut trees = path.trees.iter();
        let mut tree_len = 0;

        let rest = loop {
            if len == 0 {
                break None;
            }

            let path_node = if let Some(path_node) = trees.next() {
                path_node.clone()
            } else {
                return;
            };

            let size = path_node.size();

            if size > len {
                break Some((path_node, size));
            }

            tree_len += 1;
            len -= size;
        };

        path.trees.truncate(tree_len);

        if let Some((mut path_node, mut size)) = rest {
            while len > 0 {
                let tree_node = &self.nodes[path_node.node.index()];
                let child_size = size / 2;

                if len < child_size {
                    path_node.node = tree_node.former;
                } else {
                    path.trees.push(SkewPathNode {
                        node: tree_node.former,
                        height: path_node.height - 1,
                    });
                    len -= child_size;

                    if len < child_size {
                        path_node.node = tree_node.latter;
                    } else {
                        path.trees.push(SkewPathNode {
                            node: tree_node.latter,
                            height: path_node.height - 1,
                        });
                        len -= child_size;
                        debug_assert!(len == 0);
                        break;
                    }
                }

                size = child_size;
                path_node.height -= 1;
            }
        }
    }

    /// Create an iterator over the nodes in a path. Prefer `iter_rev` if possible, as it is
    /// somewhat more efficient.
    pub fn iter<'a, A>(&'a self, path: &'a SkewPath<A>) -> Iter<'a, A>
    where
        A: SkewPathArray<Idx = Idx>,
    {
        self.assert_tag(path);
        Iter {
            nodes: &self.nodes,
            stack: ArrayVec::new(),
            trees: path.trees.iter(),
            len: path.len(),
            last: None,
        }
    }

    /// Create a reverse iterator over the nodes in a path.
    pub fn iter_rev<'a, A>(&'a self, path: &SkewPath<A>) -> IterRev<'a, A>
    where
        A: SkewPathArray<Idx = Idx>,
    {
        self.assert_tag(path);
        IterRev {
            nodes: &self.nodes,
            path: (*path).clone(),
        }
    }

    /// Returns a path of the ancestors of two paths.
    /// 
    /// # Example
    /// 
    /// ```
    /// use skew_forest::{SkewForest, SkewPath, SkewPathNode, SkewMap};
    ///
    /// let mut forest = SkewForest::default();
    ///
    /// // Create a tree like this:
    /// // A - B (path_a)
    /// //   \
    /// //     C (path_b)
    ///  
    /// let mut path_a = SkewPath::<[SkewPathNode; 8]>::default();
    /// let node_a = forest.push(&mut path_a);
    /// let mut path_b = path_a.clone();
    /// let node_b = forest.push(&mut path_a);
    /// let node_c = forest.push(&mut path_b);
    /// 
    /// // Find the ancestors
    /// let ancestors = forest.ancestors(&path_a, &path_b);
    /// 
    /// // Check that the ancestors list is matches the list with node_a
    /// assert!(forest.iter(&ancestors).eq(vec![node_a]));
    /// ```
    pub fn ancestors<A>(&self, a: &SkewPath<A>, b: &SkewPath<A>) -> SkewPath<A>
    where
        A: SkewPathArray<Idx = Idx>,
    {
        self.assert_tag(a);
        self.assert_tag(b);
        let mut a_stack: ArrayVec<A::Array> = a.trees.iter().rev().cloned().collect();
        let mut b_stack: ArrayVec<A::Array> = b.trees.iter().rev().cloned().collect();
        let mut result = SkewPath::default();

        result.tag = self.tag;

        loop {
            match (a_stack.pop(), b_stack.pop()) {
                (Some(a), Some(b)) if a == b => {
                    result.len += a.size();
                    result.trees.push(a);
                }
                (Some(a), Some(b)) if a.height != 0 || b.height != 0 => {
                    for (stack, node, other) in
                        ArrayVec::from([(&mut a_stack, &a, &b), (&mut b_stack, &b, &a)])
                    {
                        if node.height >= other.height {
                            stack.clear();

                            let tree_node = &self.nodes[node.node.index()];

                            stack.push(SkewPathNode {
                                node: tree_node.latter,
                                height: node.height - 1,
                            });

                            stack.push(SkewPathNode {
                                node: tree_node.former,
                                height: node.height - 1,
                            });
                        } else {
                            stack.push(node.clone());
                        }
                    }
                }
                _ => break,
            }
        }

        result
    }

    /// Starts a garbage collection sweep. This allows you to mark what paths you want to keep. Any
    /// nodes that are garbage collected will be reused.
    ///
    /// See `Gc` for more details.
    pub fn gc(&mut self) -> Gc<Idx> {
        self.inner_free.grow(self.nodes.len());
        self.inner_free.set_range(.., true);
        self.inner_next = 0;
        self.leaf_free.grow(self.leaf_len);
        self.leaf_free.set_range(.., true);
        self.leaf_next = 0;
        Gc(self)
    }
}

/// A reverse iterator
pub struct IterRev<'a, A: SkewPathArray> {
    nodes: &'a [SkewTreeNode<A::Idx>],
    path: SkewPath<A>,
}

impl<'a, A: SkewPathArray> Iterator for IterRev<'a, A> {
    type Item = SkewIndex<A::Idx>;

    fn next(&mut self) -> Option<SkewIndex<A::Idx>> {
        self.path.pop(self.nodes)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.path.len(), Some(self.path.len()))
    }
}

impl<'a, A: SkewPathArray> ExactSizeIterator for IterRev<'a, A> {}

impl<'a, A: SkewPathArray> FusedIterator for IterRev<'a, A> {}

/// A forward iterator
pub struct Iter<'a, A: SkewPathArray> {
    nodes: &'a [SkewTreeNode<A::Idx>],
    stack: ArrayVec<A::Array>,
    trees: std::slice::Iter<'a, SkewPathNode<A::Idx>>,
    last: Option<A::Idx>,
    len: usize,
}

impl<'a, A: SkewPathArray> Iterator for Iter<'a, A> {
    type Item = SkewIndex<A::Idx>;

    fn next(&mut self) -> Option<SkewIndex<A::Idx>> {
        let mut path_node = self.stack.pop().or_else(|| self.trees.next().cloned())?;

        while path_node.height != 0 {
            let ix = path_node.node.index();
            let tree_node = &self.nodes[ix];

            if self.last == Some(tree_node.latter) {
                break;
            }

            self.stack.push(SkewPathNode {
                node: path_node.node,
                height: path_node.height,
            });

            self.stack.push(SkewPathNode {
                node: tree_node.latter,
                height: path_node.height - 1,
            });

            path_node = SkewPathNode {
                node: tree_node.former,
                height: path_node.height - 1,
            };
        }

        self.last = Some(path_node.node);
        self.len -= 1;

        Some(SkewIndex {
            is_leaf: path_node.height == 0,
            index: path_node.node,
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, A: SkewPathArray> ExactSizeIterator for Iter<'a, A> {}

impl<'a, A: SkewPathArray> FusedIterator for Iter<'a, A> {}

/// An in-progress mark-and-sweep session.
/// 
/// This allows a `SkewForest` to resuse unsued nodes. Active nodes must be marked using the `mark`
/// function. After marking nodes and sweeping, the nodes unmarked nodes will be reused when
/// pushing.
/// 
/// # Example
/// 
/// ```
/// use skew_forest::{SkewForest, SkewPath, SkewPathNode};
///
/// let mut forest = SkewForest::default();
/// let mut path_a = SkewPath::<[SkewPathNode; 8]>::default();
/// let mut path_b = SkewPath::<[SkewPathNode; 8]>::default();
/// 
/// forest.push(&mut path_a);
/// forest.push(&mut path_b);
/// 
/// assert_eq!(forest.size(), 2);
/// 
/// forest.gc().mark(&path_a);
/// 
/// // `path_b` has now been garbage collected since it was not marked.
/// 
/// // Size is still 2, since `size` includes garbage collected nodes.
/// assert_eq!(forest.size(), 2);
/// 
/// forest.push(&mut path_a);
/// 
/// // But actually pushing a new node reuses the old node
/// assert_eq!(forest.size(), 2);
/// ```
pub struct Gc<'a, Idx = usize>(&'a mut SkewForest<Idx>);

impl<'a, Idx> Gc<'a, Idx>
where
    Idx: Index,
{
    /// Marks a path to be kept. The nodes of the path will be kept in the `SkewForest`.
    ///
    /// An iterator to the marked nodes are returned.
    pub fn mark<'b, A>(&'b mut self, path: &SkewPath<A>) -> Mark<'b, A>
    where
        A: SkewPathArray<Idx = Idx>,
    {
        self.0.assert_tag(path);
        Mark {
            forest: &mut self.0,
            path: path.clone(),
        }
    }

    /// An iterator over all the nodes that this GC session will not be kept.
    /// 
    /// Calling this is optional. Dropping the `Gc` will also garbage collect nodes.
    pub fn sweep(self) -> Sweep<'a, Idx> {
        Sweep {
            leaf_free: self.0.leaf_free.ones().fuse(),
            inner_free: self.0.inner_free.ones(),
            marker: PhantomData,
        }
    }
}

/// An iterator over the nodes that will be marked.
pub struct Mark<'a, A>
where
    A: SkewPathArray,
{
    forest: &'a mut SkewForest<A::Idx>,
    path: SkewPath<A>,
}

impl<A> Iterator for Mark<'_, A>
where
    A: SkewPathArray,
{
    type Item = SkewIndex<A::Idx>;

    fn next(&mut self) -> Option<SkewIndex<A::Idx>> {
        let popped = self.path.pop(&self.forest.nodes)?;

        let free_set = if popped.is_leaf {
            &mut self.forest.leaf_free
        } else {
            &mut self.forest.inner_free
        };

        if free_set[popped.index.index()] {
            free_set.set(popped.index.index(), false);
            Some(popped)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.path.len(), Some(self.path.len()))
    }
}

impl<A: SkewPathArray> ExactSizeIterator for Mark<'_, A> {}

impl<A> Drop for Mark<'_, A>
where
    A: SkewPathArray,
{
    fn drop(&mut self) {
        self.for_each(std::mem::drop);
    }
}

/// An iterator over the nodes that will not be kept.
pub struct Sweep<'a, Idx> {
    leaf_free: Fuse<fixedbitset::Ones<'a>>,
    inner_free: fixedbitset::Ones<'a>,
    marker: PhantomData<Idx>,
}

impl<Idx: Index> Iterator for Sweep<'_, Idx> {
    type Item = SkewIndex<Idx>;

    fn next(&mut self) -> Option<SkewIndex<Idx>> {
        self.leaf_free
            .next()
            .map(|idx| SkewIndex {
                is_leaf: true,
                index: Idx::new(idx),
            })
            .or_else(|| {
                self.inner_free.next().map(|idx| SkewIndex {
                    is_leaf: false,
                    index: Idx::new(idx),
                })
            })
    }
}

/// An opaque node used in the a `SkewPath`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct SkewPathNode<Idx = usize> {
    height: u8,
    node: Idx,
}

impl<Idx> SkewPathNode<Idx> {
    fn size(&self) -> usize {
        (1 << (self.height + 1)) - 1
    }
}

/// An opaque array used in a `SkewPath`.
///
/// The length of this array determines the capacity of the `SkewPath`. The capacity of the path
/// will be `2.pow(array_len) - 1`.
pub trait SkewPathArray: Clone {
    type Idx: Index;
    type Array: Array<Item = SkewPathNode<Self::Idx>>;
}

impl<T, Idx> SkewPathArray for T
where
    T: Array<Item = SkewPathNode<Idx>> + Clone,
    Idx: Index,
{
    type Idx = Idx;
    type Array = Self;
}

/// The index of a node in a `SkewForest`.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct SkewIndex<Idx> {
    pub(crate) is_leaf: bool,
    pub(crate) index: Idx,
}

/// A path in a tree in a `SkewForest`. This can be seen as an index into a path in a specific
/// `SkewForest`, and must therefore only be used with a single `SkewForest`.
///
/// The type parameter `A` denotes the path node array used internally by this path. The capacity of
/// this path depends on the length of the array. If the length of this array is `n` then the
/// capacity will be `2.pow(n) - 1`.
/// 
/// The memory size and the cost of cloning a `SkewPath` is proportional to the length of the array.
pub struct SkewPath<A: SkewPathArray> {
    trees: ArrayVec<A::Array>,
    len: usize,
    tag: DebugTag,
}

impl<A: SkewPathArray> SkewPath<A> {
    fn pop(&mut self, nodes: &[SkewTreeNode<A::Idx>]) -> Option<SkewIndex<A::Idx>> {
        let popped = self.trees.pop()?;

        self.len -= 1;
        let is_leaf = popped.height == 0;

        if !is_leaf {
            let node = &nodes[popped.node.index()];

            self.trees.push(SkewPathNode {
                node: node.former,
                height: popped.height - 1,
            });

            self.trees.push(SkewPathNode {
                node: node.latter,
                height: popped.height - 1,
            });
        }

        Some(SkewIndex {
            is_leaf,
            index: popped.node,
        })
    }

    /// Return the last value in this path or `None` if the path is empty.
    pub fn last(&self) -> Option<SkewIndex<A::Idx>> {
        self.trees.last().map(|node| SkewIndex {
            is_leaf: node.height == 0,
            index: node.node,
        })
    }

    /// The number of nodes of this path.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if there are no nodes in this path and false otherwise.
    pub fn is_empty(&self) -> bool {
        self.trees.is_empty()
    }
}

impl<A: SkewPathArray> Clone for SkewPath<A> {
    fn clone(&self) -> SkewPath<A> {
        SkewPath {
            trees: self.trees.clone(),
            len: self.len,
            tag: self.tag,
        }
    }
}

impl<A: SkewPathArray> PartialEq for SkewPath<A> {
    fn eq(&self, other: &SkewPath<A>) -> bool {
        self.len == other.len && self.trees == other.trees
    }
}

impl<A: SkewPathArray> Eq for SkewPath<A> {}

impl<A: SkewPathArray> PartialOrd for SkewPath<A> {
    fn partial_cmp(&self, other: &SkewPath<A>) -> Option<Ordering> {
        Some(
            self.len
                .cmp(&other.len)
                .then_with(|| self.trees.cmp(&other.trees)),
        )
    }
}

impl<A: SkewPathArray> Ord for SkewPath<A> {
    fn cmp(&self, other: &SkewPath<A>) -> Ordering {
        self.len
            .cmp(&other.len)
            .then_with(|| self.trees.cmp(&other.trees))
    }
}

impl<A: SkewPathArray> Debug for SkewPath<A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        f.debug_struct(stringify!(SkewPath))
            .field("len", &self.len)
            .field("trees", &self.trees)
            .finish()
    }
}

impl<A> Default for SkewPath<A>
where
    A: SkewPathArray,
{
    fn default() -> Self {
        SkewPath {
            trees: ArrayVec::default(),
            len: 0,
            tag: DebugTag::from(0),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::HashSet;

    type Forest = SkewForest<usize>;
    type Path = SkewPath<[SkewPathNode<usize>; 32]>;

    #[test]
    fn iter() {
        let mut f = Forest::default();
        let mut path = Path::default();
        let mut vec = Vec::new();
        for len in 0..64 {
            assert_eq!(path.len(), len);
            vec.push(f.push(&mut path));
            assert_eq!(f.iter(&path).collect::<Vec<_>>(), vec);
        }
    }

    #[test]
    fn iter_rev() {
        let mut f = Forest::default();
        let mut path = Path::default();
        let mut vec = Vec::new();
        for len in 0..64 {
            assert_eq!(path.len(), len);
            vec.insert(0, f.push(&mut path));
            assert_eq!(f.iter_rev(&path).collect::<Vec<_>>(), vec);
        }
    }

    #[test]
    fn get() {
        let mut f = Forest::default();
        let mut path = Path::default();
        let mut vec = Vec::new();
        for len in 0..64 {
            vec.push(f.push(&mut path));

            for i in 0..=len {
                assert_eq!(f.try_get(&path, i), vec.get(i).cloned());
            }
        }
    }

    #[test]
    fn truncate() {
        let mut f = Forest::default();
        let mut path = Path::default();
        let mut vec = Vec::new();
        for len in 0..64 {
            vec.push(f.push(&mut path));

            for i in 0..=len {
                let mut l = path.clone();
                f.truncate(&mut l, i);
                assert_eq!(&f.iter(&l).collect::<Vec<_>>()[..], &vec[..i])
            }
        }
    }

    #[test]
    fn ancestors() {
        let mut f = Forest::default();
        let mut prefix = Path::default();

        for _prefix_len in 0..32 {
            f.push(&mut prefix);
            let mut a_path = prefix.clone();

            for _a_len in 0..32 {
                f.push(&mut a_path);
                let mut b_path = prefix.clone();

                for _b_len in 0..32 {
                    f.push(&mut b_path);
                    assert_eq!(prefix, f.ancestors(&a_path, &mut b_path));
                }
            }
        }
    }

    #[test]
    fn gc() {
        let mut f = Forest::default();
        let mut a = Path::default();
        let mut b = Path::default();

        let mut b_set = HashSet::new();

        for _len in 0..64 {
            f.push(&mut a);
            b_set.insert(f.push(&mut b));
        }

        let mut gc = f.gc();
        gc.mark(&a);

        let mut b_sweep_set = b_set.clone();
        assert!(gc.sweep().all(|d| b_sweep_set.remove(&d)));
        assert!(b_sweep_set.is_empty());

        let mut c = Path::default();
        for _len in 0..64 {
            assert!(b_set.contains(&f.push(&mut c)));
        }
    }
}
