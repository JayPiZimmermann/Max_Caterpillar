# Ordered augmentation corrections and the normalized graph complex

The ordered recurrence can be arranged without doubling. The existence
argument below uses a standard Eilenberg--Zilber theorem over the
rationals. It does not bound the support of the required primitives, so
it is not an exponential-width construction. The concrete normalized
graph complex isolates the remaining quantitative problem.

## The uniform augmentation lemma

In cosimplicial degree `q`, let

\[
 V^q=\ker(\mathbb Q^{q+1}\xrightarrow{\sum}\mathbb Q).
\]

Every order-preserving map of label sets acts by sending `e_i` to its
image basis vector. In particular a coface omits one label, and a
codegeneracy identifies adjacent labels. These maps preserve `V`.
Let `Z^q` be the cycle space of the complete graph on these labels.
There is a natural isomorphism

\[
 Z^q\simeq\bigwedge^2 V^q.
\]

At root 0, it sends `(e_i-e_0) wedge (e_j-e_0)` to the corresponding
oriented triangle cycle. Under a change of root this is the usual
three-term triangle relation, so the identification is compatible
with every coface and codegeneracy.

Use adjacent gaps `b_i=e_i-e_(i-1)`, `1 <= i <= q`. The codegeneracy
collapsing labels `i-1,i` kills `b_i` and relabels the remaining gaps.
Consequently the normalized cochain complex of `Z` is precisely one
copy of `Q` in degree two: a basis wedge `b_i wedge b_j` can lie in
every codegeneracy kernel only when `q=2` and `{i,j}={1,2}`.

For every `k >= 2`, the cochain complex with terms `Lambda^k Z^q`
and alternating coface differential `delta` is acyclic. Indeed,
Eilenberg--Zilber identifies the cohomology of the levelwise tensor
power `Z^(tensor k)` with that of the tensor product of the normalized
complexes. Its only cohomology is one copy of `Q` in degree `2k`.
Permuting the factors acts trivially on this class, since each factor
has even degree two. Over `Q`, the alternating projector onto
`Lambda^k Z` is an exact direct-summand projector. It kills that
trivial representation for `k >= 2`, proving acyclicity.

The tensor comparison and its compatibility with the Koszul symmetry
are the standard shuffle theorem; the cosimplicial version follows by
duality, since every vector space here is finite-dimensional in each
degree. See [Kerodon, the shuffle product](https://kerodon.net/tag/00RF),
especially its commutativity statement and Eilenberg--Zilber theorem.
The exterior-power conclusion and its application here are deductions
from that theorem, not assertions made by the cited source.

## Removing doubling from the ordered lift

Retain the linear root-lattice facet maps and the explicit starting
lift `X_3=E_01 Gamma_123` from `overnight_upper_ordered_coherent.md`.
Suppose `X_n in C_(n-1)` represents the `n`-simplex and its exact
cubical boundary is the ordered facet sum of the previously corrected
lift. Then

\[
 Y=\delta X_n
\]

is a cycle. Its augmentation `a=epsilon(Y)` belongs to
`Lambda^(n-1) Z^(n+1)`. One can see this directly from the triangular
star-basis change in the Koszul complex: the augmentation of a cycle
has no star-basis component, and is a wedge of the closed triangle
generators. Also `delta a=0`.

Since `n-1 >= 2`, the lemma supplies

\[
 c\in\bigwedge^{n-1}Z^n,\qquad \delta c=a.
\]

Lift `c` to a closed cubical chain `C_n` by taking products of the
corresponding translated triangle cycles. Set

\[
 \widetilde X_n=X_n-C_n.
\]

This does not change the coned top class. Indeed `dC_n=0`, coning
commutes with the boundary in degree `n-1 >= 2`, and injectivity of the
top differential in ambient dimension `n` gives `rho(C_n)=0`.
Furthermore `d tilde X_n=dX_n`, while

\[
 \epsilon(\delta\widetilde X_n)=a-\delta c=0.
\]

Thus the cubical filling theorem supplies `X_(n+1)` with

\[
 dX_{n+1}=\delta\widetilde X_n.
\]

Coning and top-boundary injectivity again prove that it represents
the next simplex. This is a coherent ordered induction with neither
factorial facet averaging nor doubling/subdivision. It retains the
face-direction condition on exact boundaries. The argument is an
existence simplification; it supplies no support estimate for `c`.

## A finite graph model for the missing primitive

In adjacent-gap coordinates, a basis element of `Lambda^k Z^q` is a
simple `k`-edge graph on the `q` gap labels, with an orientation given
by the order of its edge generators. Its normalized subspace consists
exactly of graphs with no isolated vertices. Hence it vanishes for
`q > 2k`.

The normalized differential splits one gap vertex into two adjacent
vertices and distributes its incident edges between them, retaining
only distributions in which neither new vertex is isolated. The
coface sign and the exterior edge-order sign determine the coefficient.
This is an explicit finite graph complex for every `k`.

For `k=2`, order the three source paths as
`(01,02), (01,12), (02,12)` and the three target matchings as
`(01,23), (02,13), (03,12)`. Then

\[
 \delta=\begin{pmatrix}0&1&0\\-1&1&-1\\1&0&-1\end{pmatrix},
 \qquad
 \delta^{-1}=\begin{pmatrix}
 1/2&-1/2&1/2\\1&0&0\\1/2&-1/2&-1/2
 \end{pmatrix}.
\]

Thus every two-edge matching has a primitive using at most three
half-integral path terms. A useful quantitative extension would apply
this local rule while processing each edge endpoint only a bounded
number of times. Iterating an exponentially expensive operation once
per dimension would still be insufficient.

`overnight_upper_ordered_normalized.py` independently checks the graph
differential, `delta^2=0`, and exactness for `k=2,3,4`. The nonzero
normalized dimensions are respectively

\[
 (3,3),\qquad (1,16,30,15),\qquad (15,135,330,315,105).
\]

## Exact chain controls and their limitation

`overnight_upper_ordered_augmentation.py` checks the full `120 by 20`
correction system for the explicit product-homotopy lift `X_4`. Its
ordinary and augmented ranks are both 19. The correction uses 15
triangle-cycle wedges with coefficients in `(2/3) Z`.

`overnight_upper_ordered_undoubled.py` starts corrections already at
`X_3`, then checks every cubical boundary and every augmentation through
simplex dimensions four, five, and six. Clearing rational denominators
gives the following measured supports:

| Simplex dimension | Cleared target scalar | Output cubes |
|---|---:|---:|
| 4 | 2 | 134 |
| 5 | 6 | 3,150 |
| 6 | 12 | 102,187 |

The correction-map ranks are 3, 19, and 195. These tests substantiate
the conventions and the finite implementation, not an asymptotic bound.
The unrestricted graph inventory in the normalized complex is itself
superexponential. An exponential construction still needs a sparse
primitive on the actual ordered obstructions, with a controlled
geometric filling and total expansion across all dimensions.
