# A reviewable cyclic candidate and its forest normal form

This is a new candidate family, not a sufficiency theorem. For each fixed-order
twin binary-search-tree pair on the nonapex labels, take the union graph and
adjoin every comparison edge from the apex to a nonapex label. Allow every
root head $x_r-x_a$ and all five segment states on this graph.

The graph has at most $3N-5$ edges. The number of twin pairs is at most the
square of a Catalan number, hence at most $16^{N-1}$. Consequently the full
description count, including all formal segment states, is bounded by a
polynomial in $N$ times a constant to the power $N$. There is no hidden
permutation closure. Every genuine exposed face is among the stated segment
choices, apart from shallow zonotope faces and the zero apex.

## Exact top-class normal form

More generally let $G$ have $m$ comparison edges. Normalize every free
function to $\sigma(\ell_e)$ in one fixed orientation. A five-state unit is

\[
 \sigma\left(x_r-x_a+\sum_e t_e\ell_e+
                  \sum_{e\in H}\sigma(\ell_e)\right),
\]

where $t_e\in\{0,-1\}$ on free edges $H$, and
$t_e\in\{-1,0,1\}$ on the other edges.

Its generic top class is a sum of units with exactly $N-2$ free edges
forming a spanning two-component forest $B\subseteq G$. Their normalized
heads still have coefficients $0,-1$ on $B$ and $-1,0,1$ off $B$.
Conversely every such forest unit is already one of the original formal
states. Thus the two families have exactly the same top span.

Here is the geometric proof. If the free generators have rank at most
$N-3$, adjoining the apex leaves a lower-dimensional polytope. If their
rank is $N-2$, tile their zonotope by graphic bases; coning each tile
gives the claim, unless the apex lies in the base affine hull, in which
case the whole unit is lower-dimensional. If the rank is $N-1$, use the
facets of the base zonotope visible from the apex. The convex hull differs
from the zonotope itself by those facet pyramids, modulo lower-dimensional
intersections. The zonotope support function is shallow. Each visible
facet has free-generator rank $N-2$ and is tiled by spanning forests.

A fixed generator contributes either endpoint to a face or tile. Thus its
additional head coefficient is zero or one. Combining this with a formerly
free coefficient zero or minus one gives precisely $-1,0,1$ on edges no
longer in $B$. No unbounded head alphabet is introduced.

The forest descriptions number at most

\[
 N(N-1)\binom m{N-2}2^{N-2}3^{m-N+2}
 \le N(N-1)5^m.
\]

This is only a normal-form and count statement. It does not place the
simplex in the span.

## Explicit coherent tiling

Give normalized generator $\ell_e$ lifting height $2^{\operatorname{index}(e)}$.
For a graphic basis $B$ on each facet component, solve
$u\cdot\ell_b=2^{\operatorname{index}(b)}$ for $b\in B$.
Every nonbasis free edge has nonzero slack
$u\cdot\ell_e-2^{\operatorname{index}(e)}$: graphic circuits have coefficients
$\pm1$, and the largest distinct power of two exceeds the sum of the others.
The tile translation is the sum of the nonbasis generators with positive
slack. These are the projected lower facets of the lifted zonotope, so they
cover the base with disjoint interiors. The sign convention for “lower”
merely selects one coherent tiling.

Facet normals are indicators of nonempty proper label subsets $S$ for which
both induced subgraphs are connected. Their fixed translation is the sum
of generators positive on $1_S$. A facet is visible exactly when its
translated support value is negative.

## Forest atom formula

Let the negative-height component be $S$, set
$a=\sum_{i\in S}\omega_i$, and let its head sum be $-c<0$.
Root the two components separately. For each root-away cut, let $q_e$ be
its frequency sum, $H_e$ its head sum, and $\epsilon_e$ the sign of the
positive endpoint. The kernel is

\[
 \frac{c^{N-1}(-a)^{N-4}}
 {\prod_e(cq_e+aH_e)(cq_e+a(H_e+\epsilon_e))}.
\]

For the full units with canonical root/apex heads, visible facets have
$c=1$. General formal states may have larger integral heights, and the
evaluator retains their powers of $c$.

## Independent finite controls and current status

The evaluator uses graph cuts and lifted spanning forests. The independent
control enumerates all zonotope vertices, obtains every three-dimensional
facet from vertex triples using integer cross products, triangulates each
visible polygon, and evaluates the resulting tetrahedra. Complete facet
inventories and exact rational checks agree, including nonunit heights.
These are finite convention controls of the geometric formula.

For the smallest nontrivial Baxter class, full apex-star/union units alone
give 136 nonshallow columns and augmented rank 137. This excludes that
narrow full-unit span. It does **not** exclude the complete five-state
family: formal frozen-generator pyramids can be full-dimensional even
when they are not exposed faces of a particular full unit.

The complete forest normal form at five inputs has 52 forests and 49676
normalized head descriptions, of which 41136 have nonzero top kernels.
There are 30436 distinct proportional kernel types. Searching only columns
whose denominator poles occur in the target leaves ten types and a gap.
Allowing at most one or two new poles gives filtered ranks 115/116 and
749/750. These are positive-search filters, not exclusions of the full family.
The actual maximum has a separate positive control: the known five-input
network converts to 59 forest atoms in this unchanged family. Every atom
of the established seven-input noncrossing witness also embeds, with
reflection parity used for 31 of its 6909 terms. See
`overnight_upper_baxter_bridges.md` for the exact receipts and their scope.

A uniform top-class identity would still need the lower-dimensional
corrections. The family has exponential face descriptions; adjoining its
instances on every label subset also preserves an exponential count.
No compact circuit is being identified with a network width without this
expansion accounting.
