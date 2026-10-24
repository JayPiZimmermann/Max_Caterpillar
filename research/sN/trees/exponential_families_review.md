# Independent semantic review of the exponential tree families

24 October 2026. This review checks the model, description counts, and finite
positive certificates. It proves no uniform spanning theorem. None of the
results below is part of the Lean verification receipt.

## The traversal order includes reversal

Write `N` for the number of inputs and `n=N−1` for the number of nonapex
vertices. The probe first generates trees on a fixed order of these `n`
vertices, includes every cyclic starting position, every head root, and every
edge orientation, and then closes the resulting units under the global
dihedral action on all `N` labels.

The last operation includes **reversal** of the nonapex traversal order. This
is a real enlargement, not a redundant coding step. For example, cyclic BFS
on four nonapex labels gives 14 trees, whereas adding reversal gives all 16
labelled trees. On five nonapex labels the respective BFS counts are 60 and
100, out of 125 labelled trees. Cyclic deque traversal similarly has 14 trees
on four labels and gains two under reversal. The pruned hierarchy first gains
new reflected trees at seven nonapex labels: 658 cyclic trees and 322 additional
reflections.

Thus the positive receipts establish identities for the families with both
traversal directions. They do not by themselves establish cyclic-only
sufficiency. Reversal changes the following bounds only by a factor of two.

## Breadth-first and deque families

A rooted plane tree on `n` vertices is described by its ordered children.
Numbering vertices by breadth-first traversal gives exactly the objects
enumerated by `breadth_first(n)`: the child counts form a queue-valid degree
sequence, and children of each processed vertex receive consecutive labels.
Conversely, the labelled tree recovers the order of children by their labels.
The count is the Catalan number `C_(n−1)≤4^(n−1)`.

The deque procedure uses such a plane tree and chooses at every step whether
to remove the next pending vertex from the front or back. Children are always
appended at the back in plane order. The first choice is irrelevant. Therefore
there are at most `C_(n−1)·2^(n−1)≤8^(n−1)` labelled outputs. Different schedules
can give the same output, which only decreases the number. This precise deque
procedure should not be identified with every possible interpretation of a
deque traversal or with all two-page trees.

Choose an apex, head root, cyclic starting point, and traversal direction.
There are at most `2N n²` choices. Each of the `n−1` unoriented tree edges has
five formal states: omitted, linear in either direction, or a function
`σ(x_i−x_j)` in either direction. This gives the description bounds

\[
\#\mathcal D_{\mathrm{BFS}}
 \le 2Nn^2\,20^{n-1},\qquad
\#\mathcal D_{\mathrm{deque}}
 \le 2Nn^2\,40^{n-1}.
\]

These counts include all genuine faces of each full unit. A zonotope-only
face has support function in the span of the first-hidden-layer functions and
linear coordinate functions. An apex–base face fixes or retains each original
segment and is a unit in the five-state family. Thus the existing face-reduction
theorem applies if a uniform top-class identity is established. The counting
argument itself supplies no such identity.

## Hierarchy count: base 20 suffices at every arity

Let `H(n)` count the exact pruned dyadic family in `hierarchy(n)`. At each split
with two nonempty children, choose one edge joining an arbitrary leaf of each
child. Recursively chosen child trees plus this bridge form a tree. Every edge
belongs to the unique split at the least common ancestor of its endpoints,
so the final tree determines all its bridge choices; there is no hidden
factorial relabelling.

For `n=2^h`, a split at level `k` has `2^(k−1)` leaves in each child, and there
are `n/2^k` such splits. Therefore

\[
H(n)=\prod_{k=1}^{h}(2^{k-1})^{2n/2^k}
     =\frac{4^{n-1}}{n^2}.
\]

Padding to the next power of two gives the valid bound `H(n)<16^n`, but the
actual pruned family admits the better bound `H(n)≤4^(n−1)` for every `n`.
For a non-power of two write `n=a+b`, where `a` is the largest power of two
strictly below `n`, so `1≤b<a`. The complete left child has `a` vertices and
the pruned right child has `b` vertices, hence

\[
H(n)=H(a)H(b)ab
\le \frac{4^{a-1}}{a^2}\,4^{b-1}ab
=4^{n-2}\frac ba
\le 4^{n-2}.
\]

Induction starts at `H(1)=1`, and powers of two use the exact formula. With
all apex/root/start/direction choices and all five edge states, the hierarchy
therefore also has at most `2N n²20^(n−1)` descriptions. The weaker proposed
base 80 was valid but unnecessary for this family.

## Matching contraction and expansion

The definition must explicitly **retain the chosen matching edges** in the
expanded tree. Choose a noncrossing perfect matching when `n` is even, or a
noncrossing matching leaving one vertex unmatched when `n` is odd. Contract
each pair, keep any unmatched singleton as a block, order blocks by their
least original label, choose a noncrossing tree in this block order, and lift
each block edge to one endpoint in each of its two blocks. Add all original
matching edges. The result is connected and has `n−1` edges, hence is a tree.
The lifted tree need not itself be noncrossing in the original label order.

Put `q=floor(n/2)` and `b=ceil(n/2)`. There are at most `4^q` perfect matchings,
or `n·4^q` near-perfect matchings. A noncrossing tree on `b` fixed ordered
vertices extends to a polygon triangulation. Bounding triangulations by `4^b`
and edge subsets within one triangulation by `4^b` gives at most `16^b`
possibilities, with the cases `b≤2` checked directly. Each of its `b−1` edges
has at most four endpoint lifts. Thus the number of expanded trees is at most

\[
4^{n/2}16^{n/2}4^{n/2-1}=\frac{16^n}{4}
\quad (n\text{ even}),
\]
\[
n\,4^{(n-1)/2}16^{(n+1)/2}4^{(n-1)/2}
=n\,16^n
\quad (n\text{ odd}).
\]

Allowing all five states gives `poly(N)·80^N` descriptions. Cyclic starts,
reversal, head roots, and apex choices add only polynomial factors. This count
does not assert that every tree with a perfect or near-perfect matching belongs
to the family, nor that the family spans the target.

## Review of the finite Fourier certificates

For a stored normalized unit, every inner edge is oriented `(u,v)` with `u<v`.
Its head can have several nonzero entries after using
`σ(x_v−x_u)=σ(x_u−x_v)+x_v−x_u`, but it still describes an original canonical
root head with arbitrarily oriented tree edges. The apex remains outside the
inner graph and has head coefficient `−1`.

For each edge, the producer removes it, takes the component `C` containing its
positive endpoint, sets `q=Σ_(i∈C)ω_i` and `H=Σ_(i∈C)h_i`, and uses

\[
R_U(\omega)=
\frac{(-\omega_a)^{N-4}}
 {\prod_e(q_e+H_e\omega_a)(q_e+(H_e+1)\omega_a)}.
\]

The frequency substitution `ω_(N−1)=−Σ_(i<N−1)ω_i` is correct. The target is
`(−1)^(N−1)/∏_iω_i`, so its subtraction in `exact_expression` has the correct
sign at both odd and even arity. Orbit coefficients multiply unnormalized
orbit sums; no missing orbit-size or factorial normalization was found.

The BFS six-input receipt has been replayed with the same exact principal-parts
verifier: 146 nonzero orbits, 1,752 full units, 1,753 rational terms, and 1,890
recursive symbolic calls. This replay is a reproducibility check, not an
independent verification algorithm.

The hierarchy six-input receipt also passes the same symbolic replay, with
330 nonzero orbits, 3,960 full units, 3,961 rational terms, and 3,331 recursive
calls. These checks found no root, orientation, target-sign, or coefficient
normalization discrepancy.

The following identities have also been checked independently using complete
exposed-face flags, without rational Fourier expressions or sampled ranks:

| Family, with reversal | Inputs | Nonzero orbits | Full units | Complete flag coordinates | Residual |
|---|---:|---:|---:|---:|---:|
| BFS | 5 | 32 | 320 | 3,440 | 0 |
| Dyadic hierarchy | 5 | 12 | 110 | 1,390 | 0 |
| BFS | 6 | 146 | 1,752 | 127,068 | 0 |

These are top-class identities. The counts in this table are full units before
face corrections, not final exact-network widths. The standalone checker and
receipts are `exponential_families_review.py` and
`exponential_families_review_flags_*.json`. They use the exact flag machinery
in `all_tree_dfs/complete_flags.py`. A coefficient perturbation is detected by
the same invariant. The source certificate hashes are recorded in the receipts.

Reproduction commands:

```sh
research/sN/dfs/h4-general-neurons/venv/bin/python \
  research/sN/trees/exponential_families_review.py flags bfs 5
research/sN/dfs/h4-general-neurons/venv/bin/python \
  research/sN/trees/exponential_families_review.py flags hierarchy 5
research/sN/dfs/h4-general-neurons/venv/bin/python \
  research/sN/trees/exponential_families_review.py flags bfs 6
research/sN/dfs/h5-growth/venv/bin/python \
  research/sN/trees/exponential_families_review.py symbolic bfs 6
research/sN/dfs/h5-growth/venv/bin/python \
  research/sN/trees/exponential_families_review.py symbolic hierarchy 6
```

The finite positive receipts do not imply any all-arity construction. A uniform
top-class identity is still the missing upper-bound theorem.
