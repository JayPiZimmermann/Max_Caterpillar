# Exponential labelled tree families: a renewed shortlist

24 October 2026. **A uniform exponential construction is still open.**
The most useful new candidates are breadth-first/deque traversal families,
balanced hierarchical trees, two-page trees, and trees assembled from a
noncrossing matching. The first two now have exact top-class identities at
five and six inputs. These are finite mathematical certificates, not Lean
results or a uniform formula.

## Common target and counting convention

Put `n=N-1`. Trees use the nonapex labels, with canonical head
`x_root-x_apex`. Every root and every edge orientation is allowed. Include
all five states per edge: omitted, either linear orientation, and either
orientation of `sigma(x_i-x_j)`. The apex is outside the tree.

For a family of `t_n` labelled trees, this gives at most
`N n t_n 5^(n-1)` descriptions. A polynomial number of cyclic starting
positions, reflections, or other fixed choices changes only the polynomial
factor. Bounds below include all five states, so **do not multiply them by
an additional orientation factor**. They count candidate dictionaries; they
are not proved width bounds for the maximum.

The target is a top-class identity for `max_N` in the full-hinge family,
modulo `L_(N-2)`. The reviewed face-closure lemma then gives an exact
two-hidden-layer representation using actual faces of those same pyramids
and linear functions. Its required faces are contained in the five-state
dictionary. No recursive extra hidden layer or factorial face enumeration
is necessary. See [the proof](all_tree_review.md#general-face-closure-sufficiency-lemma).

Counting unlabelled shapes is insufficient: all labelled paths already
number `n!/2`. The label restrictions below are essential. Likewise,
computing a maximum recursively along one binary tree adds depth; it does
not supply the required linear combination of second-hidden-layer units.

## 1. Breadth-first and deque traversals

Choose a rooted plane tree, visit it breadth first, and assign the fixed
nonapex label order to the successive visited vertices. Allow every cyclic
starting position and **both directions** around that order. The structural
root defining the traversal and the head root of the unit are independent.

There are `Catalan_(n-1) <= 4^(n-1)` rooted plane trees. Equivalently, their
breadth-first child counts sum to `n-1`, and after processing each proper
prefix at least one vertex remains in the queue. These are precisely the
usual Catalan prefix inequalities. Thus the decorated dictionary has size
`poly(N) 20^N`.

Enlarge this by keeping a deque of pending vertices. At each step choose
its front or its back, then append the chosen vertex's ordered children.
Assign labels in visit order. A plane tree plus at most `n-1` binary choices
specifies the labelled tree, giving at most `8^(n-1)` descriptions before
rotations/reflection. The decorated bound is `poly(N) 40^N`.

This permits arbitrary branching and many crossings. It includes breadth
first traversal, and also depth first traversal with the sibling order
reversed. It does **not** follow that it contains every noncrossing labelled
tree. The safe larger candidate is the union with all noncrossing trees;
that union still has the existing loose bound `poly(N) 80^N`.

Every pair of labels can occur as an edge even in the breadth-first family:
use a chain up to the earlier endpoint, then make that vertex the centre of
a star on the remaining labels. Thus the first hidden layer is not confined
to one sparse graph. Arbitrary orientations remain available.

**Next test:** the seven-input breadth-first family, or a structured
seven-input coefficient search exploiting its child-count description.
The naive complete matrix already grows substantially, so the decisive
mathematical target is a cancellation identity preserved by queue processing.
For the deque enlargement, a relation between the two possible next visits
would be more useful than a larger unstructured rank calculation.

## 2. Trees with two noncrossing pages

Fix the cyclic label order. Permit every tree whose edges can be coloured
red and blue so that each colour separately has no crossing. This is an
actual enlargement of all noncrossing trees, including arbitrary shapes.

Each page extends to a polygon triangulation. There are fewer than `4^n`
triangulations and fewer than `4^n` edge subsets of one, so a page has fewer
than `16^n` descriptions. Two pages give at most `256^n`; imposing that their
union be a tree only reduces the count. Including all five states gives
`poly(N) 1280^N`. The constant is deliberately loose.

The test for two pages is especially simple: the graph whose vertices are
tree edges and whose adjacencies are geometric crossings must be bipartite.
The family allows precisely the kind of crossings absent from the failed
noncrossing-caterpillar restriction. It is not the same as the deque family;
there are examples in both differences already on six vertices.

**Proof target:** cancel residues using relations supported on two pages,
before trying to reduce crossings. Individual crossing terms cannot be
uncrossed into the one-page span, as the existing alternating-cut pole
obstruction shows. A two-page identity must handle combinations of terms.

## 3. Expand a noncrossing matching

For even `n=2m`, choose a noncrossing perfect matching of the ordered labels.
Contract each matched pair into one block, order blocks by their least label,
and choose any noncrossing tree on those blocks. For each block-tree edge,
choose one endpoint in each of its two blocks. **Retain every matching
edge**, together with these lifted edges. The result is a tree: contracting
the matching recovers a tree, and the expanded graph is connected with
`n-1` edges.

There are at most `4^m` matchings, `16^m` block trees, and `4^(m-1)` endpoint
choices. Their product is at most `16^n`. For odd `n`, choose one unmatched
label, keep it as a singleton block, and apply the same construction to the
others. The bound becomes at most `n 16^n`. Thus the decorated family has
size `poly(N) 80^N`.

This allows crossings after expansion. It also deliberately includes trees
with perfect or near-perfect matchings, making it compatible with the live
matching-separation lower-bound conjecture. That conjecture is motivation,
not a proof that this family suffices. The block order is explicitly fixed;
allowing arbitrary permutations of blocks would lose the exponential count.

**Proof target:** a pair-contraction identity for the tree Fourier fractions,
with the apex frequency retained as a boundary parameter. Ordinary
smaller-arity induction loses that parameter and is known not to close.

## 4. Fixed balanced hierarchy with arbitrary connecting edges

Fix a complete binary hierarchy on `M` ordered leaves, where `M` is the next
power of two at least `n`, and retain the first `n` leaves. At each split with
two nonempty children choose one arbitrary edge between the two child blocks.
Do this recursively. The result is a tree, and every vertex pair is allowed
as a possible edge at its lowest common ancestor.

For `n=2^h`, the number is exactly

`product_(j=1)^h (2^(j-1) 2^(j-1))^(n/2^j) = 4^(n-1)/n^2`.

In fact `H(n) <= 4^(n-1)` holds for every `n`. For a non-power of two, write
`n=a+b` with `a` the largest power of two below `n`, so `1 <= b < a`.
The pruned hierarchy gives `H(n)=H(a)H(b)ab`. The exact formula for `a`
and induction for `b` bound this by `4^(n-2)b/a <= 4^(n-2)`.
Include every cyclic start and both directions of the nonapex label order.
The decorated bound is therefore `poly(N) 20^N` at **every** arity.

The hierarchy is fixed, but its graph is not. All connecting endpoints are
free, so this family avoids the sparse-global-feature-graph obstruction.
It permits crossings and gives a direct two-block recursive structure.

**Proof target:** a gluing identity for two blocks that sums over their
connecting endpoint pair and both hinge orientations. It must be an identity
in the linear span of units, not a composition of two smaller networks.

## 5. Two additional enlargements

**Nonnesting trees.** On a fixed linear label order, disallow pairs of edges
`a< c< d< b`. When edges `(a,b)` are sorted by their first endpoint and then
their second, their second endpoints are nondecreasing. Thus the edge set
lies on a monotone lattice path in an `n` by `n` grid. There are at most
`4^n` such paths and at most `4^n` subsets per path. This gives at most
`16^n` graphs, hence `poly(N) 80^N` decorated trees, also after cyclic starts
and reversal. This includes breadth-first trees but relaxes their parent
condition. One can also allow one noncrossing page and one nonnesting page;
the bound becomes `poly(N) 1280^N`.

**Noncrossing trees in restricted alternative orders.** Permit every
separable permutation of the fixed labels before choosing a noncrossing
tree. A signed binary decomposition gives at most `8^n` separable orders,
so the decorated count is at most `poly(N) 640^N`. Alternatively, two
increasing runs give at most `2^n` orders and the count `poly(N) 160^N`.
This latter family uses arbitrary noncrossing tree shapes and all roots and
orientations; it is larger than the previously refuted one-descent
caterpillar dictionary. Separable orders were already suggested in the
earlier review; what is new here is the explicit enlargement to arbitrary
noncrossing trees in those orders. A primary reference for the separable
enumeration is [Gil, Lopez and Weiner](https://arxiv.org/abs/2603.25528);
the elementary signed-binary-tree overcount suffices for the bound above.

## Finite evidence and its limits

`exponential_families.py` independently checks generated tree sets against
Pruefer enumeration through seven vertices. These are the counts after
cyclic starts **and reversal**, on one fixed nonapex label set:

| Nonapex vertices | All trees | Breadth first | Deque | Balanced hierarchy |
|---:|---:|---:|---:|---:|
| 4 | 16 | 16 | 16 | 8 |
| 5 | 125 | 100 | 115 | 65 |
| 6 | 1,296 | 444 | 870 | 96 |
| 7 | 16,807 | 1,764 | 6,573 | 980 |

The nonmonotone fraction for the hierarchy reflects the fixed padded dyadic
partition; no monotone inclusion across arities is assumed.

`exponential_families_probe.py` includes every head root and orientation,
then forms global dihedral orbit sums. It uses modular arithmetic only to
propose rational coefficients. The existing exact principal-parts verifier
checks the entire resulting Fourier identity, not just sample points.

| Family / inputs | Orbit columns | Nonzero orbit coefficients | Full units in identity | Exact result |
|---|---:|---:|---:|---|
| Breadth first / 5 | 164 | 32 | 320 | Top-class identity |
| Breadth first / 6 | 2,404 | 146 | 1,752 | Top-class identity |
| Balanced hierarchy / 5 | 82 | 12 | 110 | Top-class identity |
| Balanced hierarchy / 6 | 1,562 | 330 | 3,960 | Top-class identity |

The five-input breadth-first test includes every labelled tree, so the
six-input result is its first genuinely restrictive test. These unit counts
are before face corrections, not exact final network widths. Each positive
identity implies finite sufficiency of its face dictionary by the reviewed
face-closure bridge. No uniform coefficient formula follows from these
checks, and six-input success must not be extrapolated: the earlier
noncrossing-caterpillar family passed at six and seven, then failed at eight.

The six-input breadth-first run first stopped at a five-million-entry matrix
cap. That is preserved as `exponential_families_bfs_6_budget5m.*`. Raising
the cap to eight million entries produced the complete exact identity in
14.42 seconds. The hierarchy six-input run completed in 12.47 seconds.

Positive receipts retain the full orbit descriptions and exact coefficients.
The sampled modular matrix is omitted after the exact identity gate; its
canonical JSON SHA256, frequency points, seed and producer are retained for
reproduction. The sampled matrix is not needed to check the exact identity.

The [independent review](exponential_families_review.md) checks the family
counts and model conventions. A separate complete exposed-face-flag checker
confirms breadth first at five and six inputs and the hierarchy at five;
the six-input breadth-first residual vanishes on 127,068 flag coordinates.
Both six-input symbolic identities were also replayed. The review receipts
hash the current compact certificate files. None of these gates is Lean
verification, and no uniform spanning theorem is inferred.

Reproduction (NumPy/python-flint environment):

```sh
python3 research/sN/trees/exponential_families.py
research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/exponential_families_probe.py 6 bfs
research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/exponential_families_probe.py 6 hierarchy
```

Priority: pursue a breadth-first/deque cancellation identity and the
two-block hierarchy identity; retain two-page and matching-expansion trees
as principled enlargements. The unrestricted all-tree exponential lower
bound is still open separately; its latest odd-arity reduction and the
failed fixed-coordinate recursion are in [the lower-bound note](reopen_lower_odd.md).
