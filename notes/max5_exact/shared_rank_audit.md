# Independent audit of the all-five-shared rank filter

Status: PASS, 31 October 2026. This is a partial exclusion within the
two-positive-core, all-five-shared-contact branch of Max5 (9,4). It does
not exclude that whole branch or prove a new unrestricted width bound.

## Mathematical bridge

Let the seven actual invariant first features be `ReLU(a_j.x)`, and set
`B_ij=ReLU(-a_ji)`. The two cores have coefficient vectors c and d in
this actual feature span. Sharing all five contacts `q_i=-e_i` means
`B*c=B*d=0`. The matrix B is five by seven and nonnegative.

If a top triple has no coordinate-difference first hyperplane and
exactly one first row supported on that triple, the local rigidity
lemma in [allfive_shared_rank.md](allfive_shared_rank.md) gives
`c_j^2=d_j^2` for that row j. Its proof was checked independently: on
the side of the one first line containing two target rays, the two
positive folds must carry those distinct rays separately with unit
curvatures. On the opposite side both linear extensions must cross
the sole target ray. Continuity makes their coefficients on the first
feature equal in absolute value. Other global first rows are smooth at
a generic point of that top-triple face and contribute only linear
terms, so they do not alter this conclusion.

Write J for these mandatory row indices, and define `u=c-d`, `v=c+d`.
Then u and v belong to the kernel of B, with `u_j*v_j=0` for every j in J.

Join j and k by an edge whenever the five by five matrix obtained by
deleting columns j,k from B is invertible. For a nonzero kernel vector,
its j-th and k-th coordinates cannot both vanish: otherwise the remaining
five coordinates would lie in the kernel of that invertible matrix.

Suppose both u and v were nonzero. At every vertex in J choose one of
the two vanishing coordinates, thereby coloring the vertex by u or v.
An edge cannot have both endpoints colored u, and cannot have both
colored v, by the preceding observation. Thus this is a proper
two-coloring. Consequently, a non-bipartite graph of certified invertible
minors forces u=0 or v=0, meaning `g=h` or `g=-h` as global functions.

Either equality collapses the two positive folds to one positive fold
modulo a shallow remainder. For `g=-h`, use
`ReLU(g)+ReLU(-g)=2*ReLU(g)-g`. The established arbitrary-direction
one-core Max5 obstruction then gives a contradiction. The argument
does not require the seven feature evaluations to be independent.
Indeed, any certified minor already supplies the needed matrix rank.

## Uniformity in real coefficients and feature orientations

For an exact first-row support, the negative coefficient set is any
nonempty proper subset of that support, because every nonzero invariant
row has both coefficient signs. The producer enumerates all such
subsets for each of the seven rows. These are the signs of the **actual
oriented features**; flipping a row is not silently quotiented out.

Every positive entry of B is left arbitrary. The determinant of a
candidate minor is a signed sum of distinct positive monomials. If at
least one determinant term exists and all existing terms have the same
parity, the determinant is nonzero for every choice of those positive
entries. Magnitude relations required by the original zero-sum rows can
only restrict this already covered domain. Mixed-parity minors are not
used, even when they might be nonzero at particular coefficients.

The resulting graph is therefore a certified subgraph of the graph of
all invertible coordinate minors. Non-bipartiteness of this subgraph is
sufficient for exclusion. A bipartite subgraph says nothing about actual
existence, rank loss, or the signs of the omitted minors.

## Independent replay

The checker
`research/sN/frontier5/max5_shared_rank_pattern_audit.py` imports no
producer code. It differs from the producer in both finite computations:

* Determinant parity is propagated by a row-wise subset dynamic program,
  instead of enumerating all 120 permutations of the columns.
* Bipartiteness is tested by all cuts, fixing one vertex's color, instead
  of a graph traversal.

It reconstructs singleton triples using their two omitted coordinates,
enumerates negative coefficient sets by combinations of labels, and
checks every stored survivor and every excluded profile. It also checks
the source, producer, artifact, and checker hashes.

The independently checked counts are:

| Quantity | Count |
| --- | ---: |
| Support orbits having at least three mandatory singleton triples | 19 |
| Actual oriented negative-support patterns checked | 618,624 |
| Patterns uniformly excluded by the rank argument | 50,988 |

These are support/sign patterns, not solutions or connected components.
The other support orbits and the surviving patterns remain outside this
exclusion. The source support catalog's completeness is supplied by its
existing independent C3/C4 inventory audit; this replay checks the new
filter on that catalog.

Replay:

```
python3 research/sN/frontier5/max5_shared_rank_pattern_audit.py
```

The receipt `max5_shared_rank_pattern_audit.json` reports
`INDEPENDENT_ROW_DP_AND_ALL_CUTS_PASS`. The checked producer hash is
`a72f54d2fedf8c5fb367b5afe17244c5396da0f848c943ec9af91db2dcf149f8`.
No Lean verification is claimed.
