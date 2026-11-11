# Finite cycle and forest bridge

**Status: Lean verified research leaves.** These results supply the graph
steps for exact cycle deletion. They do not prove a new MAX obstruction or
an exponential second-hidden-layer lower bound. The separate signed
function expansion is maintained in `../dictionary_bridge/`.

The core declarations are:

- `Forest.exists_leaf` in `Leaf.lean`: a finite acyclic graph containing an
  edge has a vertex with exactly one neighbour. The proof takes a longest
  simple path and uses acyclic path uniqueness.
- `ForestMatching.indexedGraph_oriented_cycle` in `Cycle.lean`: a genuine
  cycle in the simple graph of original edge indices yields a nonempty
  original index subset and fixed orientations for which the coordinate
  differences sum to zero on **every real input**. Parallel indices and
  loops are allowed in the dictionary. The simple graph ignores loops.
- `ForestMatching.exists_cover_matching` in `Konig.lean`: for an acyclic
  graph on `Fin n`, there are an actual original-vertex cover `C` and an
  ordinary vertex-disjoint edge matching `M` with `|C| ≤ |M|`.
- `ForestMatching.cover_card_le_of_no_matching`: if that forest has no
  matching of `r+1` edges, it has a cover of at most `r` vertices.
- `ForestMatching.matching_mono` in `Cover.lean`: deleting graph edges
  preserves every upper bound on the size of a matching.

The cover proof is simultaneous strong induction on the number of edges.
For a leaf `v` with neighbour `w`, remove every edge incident to either
vertex. Add `w` to the recursively obtained cover and add the original
edge `{v,w}` to the recursively obtained matching. The leaf condition
makes the cover extension valid; deleting both endpoints makes the new
matching edge disjoint from all existing ones.

The matching predicate is the existing
`GrowingMatching.matchings`, using literal unordered `Sym2` edges and
pairwise disjoint endpoint sets. It is not an alternate encoding of the
requested cover conclusion. All four matching headline APIs quantify
an arbitrary `DecidableRel G.Adj`; the independent audit found and fixed
an initial API issue that had baked in the classical instance.

`Check.lean` checks the exact cover and matching types, their axioms, and
an explicit nonempty acyclic graph. `CycleCheck.lean` checks the exact
cycle type and a triangle represented by all nine ordered pairs on three
vertices, including loops and both orientations. The only axioms used
are `propext`, `Classical.choice`, and `Quot.sound`.

Reproduce from the repository root:

```sh
python3 research/sN/exponential_push_20261102/forest_matching/recheck.py --run
```

The receipt binds source hashes, checker/control files, build logs, and
axiom audits. These leaves have not been added to a production import root.
No expansion-width estimate or structural conjecture is hidden in the
graph statements.
