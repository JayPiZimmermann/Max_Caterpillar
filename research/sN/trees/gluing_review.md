# Full rooted-kernel gluing: exact identity and failed scalar closures

24 October 2026. The edge-gluing identity below is exact. It does not prove a
uniform hierarchy construction. Two tempting simplifications are excluded by
small exact obstructions. These are mathematical research results with exact
controls, not Lean declarations.

## Exact gluing identity

Let `T` be an oriented tree with a chosen head root `r`. An oriented edge
`(i,j)` means the function `σ(x_i−x_j)`. For each edge, remove it and let `C_e`
be the component not containing `r`. Put

\[
q_e=\sum_{i\in C_e}\omega_i,
\qquad
\varepsilon_e=
\begin{cases}
+1&\text{if the positive endpoint belongs to }C_e,\\
-1&\text{otherwise},
\end{cases}
\]
\[
K_T(\omega;a,r)=
\prod_{e\in E(T)}\frac1{q_e(q_e+\varepsilon_e a)}.
\]

The parameter `a` is external. This definition is a rational function of free
frequencies; no sum-zero constraint is imposed. Empty products, for singleton
trees, equal one.

Join disjoint trees `A,B` by a bridge with endpoints `u∈A`, `v∈B`, and assume
`r∈A`. Write `b=Σ_(i∈B)ω_i`. The bridge sign is `+1` for `σ(x_v−x_u)` and
`−1` for `σ(x_u−x_v)`. Then

\[
\boxed{
K_T(\omega;a,r)=
\frac{K_A(\omega_A+b e_u;a,r)\,
      K_B(\omega_B;a,v)}
     {b(b+\varepsilon_{\rm bridge}a)}.}
\]

To prove this, classify the cuts. The bridge cuts off precisely `B`, giving
the displayed denominator. Removing an edge of `B` cuts off the component
away from `v`, exactly as in the tree rooted at `v`. For an edge of `A`, its
away component gains all of `B` precisely when it contains `u`. Replacing
`ω_u` by `ω_u+b` makes exactly these changes. All cut signs are unchanged.
The factors agree edge by edge. This proves a rational identity; evaluation
requires avoiding the indicated poles.

The same proof gives multiple attachments: attach subtrees of total masses
`b_j` at vertices `u_j` and replace `ω_A` by `ω_A+Σ_j b_j e_(u_j)`. Attachment
order is immaterial at the level of these frequency shifts.

## What a recursive state must retain

The location of the shift matters, as do the head root and the fixed external
parameter. Keeping the entire multivariate kernel with its head root is a
valid state; a gluing operation also specifies the attachment vertex. The
kernel is independent of the root frequency, so a shift at `u=r` happens to
have no effect. Shifts at other vertices generally do affect it.

For example take the path `0–1–2`, root `0`, positive endpoints `1` and `2`,
frequencies `(2,3,5)`, and external parameter `a=7`. Glue `A={0,1}` to `B={2}`
at `u=1`. The correct value is `1/7200`; omitting the shift by `b=5` gives
`1/1800`.

The distinction between `a` and a block's own frequency sum is also essential.
If the whole nonapex frequency vector satisfies `Σω=−a`, then the shifted
`A` vector still has total `−a`, but the unshifted `B` vector has total `b`,
which need not equal `−a`. Replacing the external parameter of `K_B` by its
natural local apex frequency `−b` changes the kernel. Already for a two-vertex
block with frequencies `(2,3)`, root at the first vertex, and an inward edge,
the value is `1/30` at `a=7` and `−1/6` at `a=−5`.

Consequently an ordinary smaller-arity identity on its own conservation
hyperplane cannot simply be inserted for the `B` factor. One must retain the
external parameter, the multivariate attachment dependence, and whatever
additional block functions are needed for a closed linear identity. These
remarks do not assert that finitely many scalar boundary parameters suffice.

For reference, with `n` nonapex vertices the canonical unit has generic Fourier
rational function

\[
R_U=(-a)^{n-3}K_T
\]

on `Σω=−a`, omitting the common factor `i^(−n−1)`. The maximum has
`R_max=(−1)^n/(a∏ω_i)`. Thus its corresponding kernel target is

\[
-\frac1{a^{n-2}\prod_i\omega_i}.
\]

This target normalization is specific to the conservation hyperplane. It is
not an already proved identity for free block frequencies.

## Two-vertex obstruction to a scalar block target

Let `B` have frequencies `x,y`, and write `b=x+y`. Allow either head root and
either orientation of its one edge. Its four kernels are

\[
f_+(x),\ f_-(x),\ f_+(y),\ f_-(y),
\qquad f_\pm(z)=\frac1{z(z\pm a)}.
\]

Over the field `Q(a,b)`, with `y=b−x`, these four functions do **not** span
`1/(xy)`. This is stronger than failure with constant network coefficients.
Their respective exclusive noncoordinate poles occur at
`x=−a,a,b+a,b−a`. The four residues are
`−1/a,1/a,1/a,−1/a`; the target has zero residue at all four. Thus every
coefficient must vanish, whereas the target has residue `1/b` at `x=0`.
The resulting five-by-five augmented residue determinant is

\[
\frac1{a^4b}\ne0.
\]

The argument is over a rational function field, so the pole locations are
generically distinct. Special resonances such as `b=−a` do not imply a free
parameter identity. In fact the smallest ordinary identity illustrates the
resonance: on `x+y=−a`, one has `f_+(y)=−1/(xy)`.

There is an immediate four-input obstruction to a naive fixed-partition
construction. Let `A={r}`, `B={x,y}`, fix the global head root `r`, retain the
edge inside `B`, and permit either attachment endpoint and both orientations
of both edges. Every kernel is `f_±(b)` times one of the four block kernels
above. With the root frequency `t=−a−b`, the four-input maximum would require

\[
\frac1{a(a+b)xy},
\]

a nonzero `Q(a,b)` multiple of the excluded target. Therefore this local
family fails even in the top quotient. This does **not** exclude the full
hierarchy family, which changes partitions, global roots, and apex labels.

Summing the two bridge orientations alone does not remove the issue:

\[
f_+(b)+f_-(b)=\frac2{b^2-a^2},\qquad
f_+(b)-f_-(b)=-\frac{2a}{b(b^2-a^2)}.
\]

A successful gluing proof must arrange cancellation with other terms or
retain more informative block functions than a scalar multiple of a simplex
fraction.

## All edges toward the root: an exact five-input obstruction

Suppose every edge contributes `σ(x_child−x_parent)` for the chosen head root.
Then

\[
x_r+\sum_{\text{child}\to\text{parent}}
\sigma(x_{\rm child}-x_{\rm parent})
=M_T(x)
:=\sum_{\{u,v\}\in E(T)}\max(x_u,x_v)
-\sum_{v\in V(T)}(\deg(v)-1)x_v.
\]

Indeed, replace every function `σ(x_child−x_parent)` by
`max(x_child,x_parent)−x_parent` and count each vertex's children. The right
side is independent of the chosen root. The full unit is therefore
`σ(M_T(x)−x_apex)`, and the normalized quantity
`κ_v=h_v+outdeg(v)` equals one at every nonapex vertex.

At `N=5` the four-vertex inner tree has only two shapes: path and star. Since
the family of all such units is invariant under every label permutation,
any representation of the symmetric target could be averaged over `S_5`.
It would then lie in the span of two full permutation-sum columns.

For the path use edges `(2,1),(3,2),(4,3)` and for the star use
`(2,1),(3,1),(4,1)`, both with apex `0` and head root `1`. The common Fourier
factor is omitted, so each unit contributes `−a K_T`. At the three frequency
vectors

\[
(1,2,3,4,-10),\quad(1,2,4,8,-15),\quad(1,3,9,27,-40),
\]

the two unnormalized permutation sums and the maximum give the exact matrix

\[
\begin{pmatrix}
-461/5292&-26/189&-1/240\\
-169457/7567560&-75553/2162160&-1/960\\
-10191989/13189077720&-801173/676362960&-1/29160
\end{pmatrix}.
\]

Its determinant is

\[
-\frac{108076159}{19163354302226534400}\ne0.
\]

Thus all inward-oriented tree units together fail to span the five-input
maximum in the top quotient. Missing or linear tree-edge states have lower
dimension, so adding all their face states does not repair the obstruction.

### Propagation: every arity at least five fails

In this particular family the five-input obstruction propagates. Let
`U_(T,α)=σ(M_T−x_α)` and use the opposite-face derivative
`D_u=∂_u−∂_(-u)`. For any label `v`, direct differentiation gives

\[
D_{-e_v}U_{T,\alpha}=
\begin{cases}
M_T-x_\alpha,&v=\alpha,\\[2mm]
\displaystyle\sum_{w\sim v}x_w-\deg(v)x_v,
 &v\in T,\ \deg(v)\ge2,\\[2mm]
U_{T-v,\alpha}-M_{T-v}+x_p-x_v+x_\alpha,
 &v\text{ a leaf with neighbour }p.
\end{cases}
\]

For a nonapex vertex, the outer preactivation at `−e_v` is `deg(v)−1` and
at `+e_v` is one. An internal vertex therefore gives a difference of two
active linear pieces; the free-edge maxima cancel and yield the displayed
linear function. At a leaf, the first preactivation is zero, and removing
its edge leaves exactly the smaller inward unit. At the apex the two
preactivations are one and minus one, giving the first case. Each `M_T` is
linear plus a sum of functions `max(x_i,x_j)`, hence belongs to `L_1`.
Consequently only leaf deletion contributes a smaller inward unit modulo
`L_1`.

Meanwhile,

\[
D_{-e_v}\max_N=\max_{i\ne v}x_i-x_v,
\qquad D_u L_k\subseteq L_{k-1}.
\]

The filtration inclusion follows directly from exposed faces: either the
direction is constant on a polytope and its opposite-face difference is zero,
or both exposed faces have dimension at least one less. Thus an `N`-input
inward-tree identity modulo `L_(N−2)` descends to an `(N−1)`-input identity
modulo `L_(N−3)`, after setting `x_v=0`. To formulate this entirely on the
translation quotient, choose a different coordinate as the fixed gauge;
then `−e_v` is an allowed direction and the restriction is the smaller
quotient. Linear precomposition preserves the dimension filtration.

For every step from `N≥6`, the additional `L_1` terms are in `L_(N−3)`.
Iteration would produce the excluded five-input identity. Therefore:

**For every `N≥5`, all inward-oriented canonical tree units, even together
with all their formal face states and all lower-dimensional support
functions, fail to span the maximum in the top quotient.**

Here “lower-dimensional” means `L_(N−2)` on the `(N−1)`-dimensional translation
quotient. This excludes the inward-only simplification at every larger arity,
but says nothing against arbitrary edge orientations.

## Independent checks and trust boundary

`gluing_review.py` checks 3,480 exact rational gluing identities. This exhausts
all labelled trees, orientations, head roots, and bridge choices at two,
three, and four nonapex vertices, each at a free external parameter and on
the global conservation hyperplane. It adds 256 exact controls at five through
eight nonapex vertices. It checks both erroneous substitutions above and the
symbolic two-vertex residue determinant.

`gluing_review_inward.py` independently enumerates all 16 four-vertex labelled
trees, confirms the two possible degree types, checks 5,184 exact instances
of the root-independence formula, and regenerates the full `S_5` rational
evaluation matrix and its nonzero determinant. It also checks 19,440 exact
directional-derivative instances of all three deletion cases, using the CPWL
chain rule separately from the displayed deletion formula. No modular
reconstruction or floating-point computation is used.

```sh
research/sN/dfs/h4-general-neurons/venv/bin/python \
  research/sN/trees/gluing_review.py
python3 research/sN/trees/gluing_review_inward.py
```

The receipts are `gluing_review_receipt.json` and
`gluing_review_inward_5.json`. The mathematical reductions are the cut
classification, rational residue calculation, root-independence identity,
permutation averaging, and the existing Fourier-to-top-class bridge. The
finite arithmetic is trusted ordinary Python/SymPy arithmetic, not a Lean
kernel certificate.

## Later hierarchy and orientation-subclass certificate reviews

The seven-input full fixed-hierarchy candidate fails. The root producer
checked 296 independent exact rational kernel identities among 5,392 orbit
columns, giving ordinary rank at most 5,096; the repeated modular augmented
rank is 5,097. These exclude that complete family, including all roots and
orientations and its formal face states.

The independent review in `gluing_review_gates.py hierarchy7` reconstructs
the family without the hierarchy generator. On six nonapex labels, a tree
belongs precisely when it contains one of the two cyclic adjacent perfect
matchings. There are 96 such trees: after contracting a chosen matching,
there are three labelled trees on the three blocks and four endpoint choices
for each of their two edges, hence `3·4²=48` for each matching. A tree cannot
contain both matchings because their union is a six-cycle. The pruned hierarchy
and all cyclic starts give all of these three block-tree possibilities.

Independent Prüfer enumeration and all apex/root/orientation choices reproduce
exactly 75,264 normalized units, partitioned into the stored 5,392 disjoint
dihedral orbits. The review checks the actual group orbit of every column,
all 296 identity free coordinates proving independence, all exact-gate passed
indices, and the source/checker hashes. It also regenerates every entry of
the first 5,393-entry augmented Fourier row via an independent general-head
DFS calculation, without the batch factor engine. Every entry matches, and
all 296 proposed relations vanish on the independent row. This review does
not repeat the large rank calculation or all 296 symbolic proofs; those are
supplied by the root producer and its exact gate. The normalization and
independence audit found no discrepancy.

The independent DFS roots the normalized tree at an arbitrary nonapex vertex.
For a child subtree `C`, it computes `q=Σ_Cω`, `H=Σ_Ch`, and the sign `ε`
according to whether the positive edge endpoint lies in `C`. Its denominator
factor is `(q+aH)(q+a(H+ε))`. For `ε=−1`, this follows from the positive-endpoint
formula by complementing `C`, using `Σ_nonapexω=−a` and `Σ_nonapexh=1`.
The numerator remains `(−a)^(N−4)`. Thus the entire-row comparison checks
complement choices and head normalization as well as arithmetic.

There is also a much smaller positive BFS witness at six inputs: seven
dihedral orbit coefficients, all `±1/6`, give 84 full units. Each unit is
inward, or differs from an inward unit by the linear shift `x_i−x_j` along
one tree edge. The independent command `gluing_review_gates.py edge6` checks
the defect condition, all 11,796 complete flag coordinates, and an exactly
zero residual. This is a top-class identity; 84 is not a final width after
face corrections.

The review receipts are `gluing_review_hierarchy7.json` and
`gluing_review_bfs_edge6.json`. Use the NumPy/python-flint research environment
for `hierarchy7` and the SymPy research environment for `edge6`:

```sh
research/sN/dfs/h5-growth/venv/bin/python \
  research/sN/trees/gluing_review_gates.py hierarchy7
research/sN/dfs/h4-general-neurons/venv/bin/python \
  research/sN/trees/gluing_review_gates.py edge6
```

The BFS single-edge-shift family fails at seven inputs: the root exact gate
checks five independent identities on 2,444 orbit columns, giving ordinary
rank at most 2,439, while the modular augmented rank is 2,440. The independent
`gluing_review_edge7.py` checker enumerates all six-vertex labelled trees by
Prüfer codes, tests breadth-first visit order directly under cyclic starts
and reversal, and obtains 444 trees. For each apex it then forms `M_T−x_apex`
and every shift by either orientation of one tree edge. This independently
reproduces exactly the 34,188 normalized units in the stored family. The
checker verifies the five identity free coordinates, gate provenance, and
every entry of the first 2,445-entry augmented Fourier row through the same
independent DFS method. All checks pass; the receipt is
`gluing_review_bfs_edge7.json`.

### Bounded-path shifts and BFS leaf deletion

The single-edge obstruction also propagates. More generally fix `k` and
consider

\[
U_{T,\alpha;i,j}
=\sigma(M_T-x_\alpha+x_i-x_j),
\qquad \operatorname{dist}_T(i,j)\le k,
\]

including the unshifted inward unit. This is exactly the inward function
after reversing the directed path from `j` to a head root `i`. It is a
canonical-root tree unit, not an arbitrary new head extension.

Write `δ=e_i−e_j`. For a nonapex vertex `v`, the preactivations at `−e_v`
and `+e_v` are respectively `deg(v)−1−δ_v` and `1+δ_v`. Consequently:

- Deleting an unmarked leaf gives the same shift on the smaller tree,
  modulo `L_1`.
- Deleting the positive marked leaf gives only `L_1`.
- Deleting the negative marked leaf with neighbour `p` gives minus the
  smaller unit shifted by `x_i−x_p`, modulo `L_1`. Its marked path is one
  edge shorter; if `i=p`, the shift vanishes.
- An unmarked internal vertex gives a linear function. A marked internal
  vertex either does the same, or leaves an outer maximum whose free
  generators are precisely edges of the forest obtained by deleting `v`.
  That forest has `N−2−deg(v)` edges, so the support dimension of its outer
  pyramid is at most `N−1−deg(v)≤N−3`.
- Deleting the apex gives only `L_1`.

Thus only leaf deletion contributes in the smaller top quotient, and the
path-length bound never increases.

Breadth-first labelled trees are closed under deleting a leaf while retaining
the induced order. A nonroot leaf never appends children to the queue, so
removing it leaves the relative visit order of every other vertex unchanged.
If the traversal root is a leaf in the unrooted tree, it has a single child;
that child becomes the traversal root and again the remaining order is
unchanged. Cyclic starting points and reversal are preserved after deleting
a label. This structural traversal root is independent of the unit's head
root.

The preceding opposite-face argument therefore propagates any finite
obstruction for BFS bounded-path shifts to every larger arity, keeping `k`
fixed. In particular, **the single-edge-shift BFS face dictionary fails
for every `N≥7`**, despite its exact six-input identity. The same implication
applies to the separately certified seven-input path-length-two obstruction.
This does not exclude full arbitrary-orientation BFS or deque families.

`gluing_review_edge_deletion.py` independently checks 4,800 exact directional
derivative instances, including 780 marked-internal-vertex cases with the
required forest dimension bound. It checks 9,414 BFS leaf deletions through
nine nonapex vertices. The uniform proof is the queue argument and derivative
case distinction above; the finite controls do not replace it. Reproduce with

```sh
python3 research/sN/trees/gluing_review_edge_deletion.py
research/sN/dfs/h5-growth/venv/bin/python \
  research/sN/trees/gluing_review_edge7.py
```
