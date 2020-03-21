# skew-forest

An implementation of skew-binary random access lists.

Skew-binary random access lists are a persistent list data structure. They allow logarithmic
time random access. Most notably, online lowest common ancestors can be implemented in
logarithmic time in the length of the path.

These lists are *persistent*, i.e. they allow preserving the old version of itself when mutated
Eg. consider a simple list like this:

```
A - B - C - D    List: ABCD
```

If, after B, we clone the list and append `E` and `F`, we will get the resulting structure:

```
A - B - C - D    First list: ABCD
      \
        E - F    Second list: ABEF
```

Here we can see how `A` and `B` will be shared among the two lists. Thus the "lists" in skew-
binary random access lists can really be seen as paths in a tree instead. To emphasize this,
this implmentations refers to skew-binary random access lists as paths, or more specifically
as the `SkewPath` type.

Since we want to be able to share nodes, the paths themselves do not own the nodes. Instead, the
paths are indexes into a structure that *does* own the nodes. This structure, the `SkewForest`,
encapsulates the shared graph of the paths.

## Topology

An additional wrinkle is that the `SkewForest` and `SkewPath` in this implementation does not
store any actual values. They *only* store the path topology, i.e. the sequence of node indexes
that forms the nodes of a path. When `push` operation is called on a `SkewPath` the index of the
node is returned.

To actually associate a value with a node, a `SkewMap` can be constructed to map these indices
to values.

## Example

The example below demonstrates creating two lists as shown above.

```rust
use skew_forest::{SkewForest, SkewPath, SkewPathNode, SkewMap};

let mut forest = SkewForest::default();
let mut path_a = SkewPath::<[SkewPathNode; 8]>::default();

// Push A and B onto `path_a`
let node_a = forest.push(&mut path_a);
let node_b = forest.push(&mut path_a);

// Clone A to B
let mut path_b = path_a.clone();

// Push C and D onto `path_a`
let node_c = forest.push(&mut path_a);
let node_d = forest.push(&mut path_a);

// Push E and F onto `path_b`
let node_e = forest.push(&mut path_b);
let node_f = forest.push(&mut path_b);

// Check that `path_a` matches ABCD
assert_eq!(
    forest.iter(&path_a).collect::<Vec<_>>(),
    vec![node_a, node_b, node_c, node_d],
);

// Check that `path_b` matches ABCD
assert_eq!(
    forest.iter(&path_b).collect::<Vec<_>>(),
    vec![node_a, node_b, node_e, node_f],
);
```

License: MIT
