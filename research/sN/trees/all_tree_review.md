# Unrestricted tree bound: independent review, 24 October 2026

Later upper-bound result: the proposed noncrossing restriction of the original
caterpillar dictionary is now rigorously refuted at eight inputs, including
rooted-star faces. Its successes at six and seven inputs remain valid finite
results. The proposed saturation statement for that restricted family below
is therefore a failed route, not a live conjecture. See
[the current DFS ledger](all_tree_dfs/CURRENT.md) and the exact aggregate receipt
`all_tree_dfs/nc_obstruction_8_certified.json`. Larger noncrossing tree families
with additional marked head positions or orientations remain unresolved.

The live target is an exponential lower bound, uniform over all original tree
shapes and edge orientations, for expansions by `Trees.TreeFace.unit` plus
`A_N`. It is **not proved here**. Two useful deductions are proved below: a
canonical-head reduction for the top-dimensional germs, and an exponential
count of connected subsets with no twin leaves. Together they reduce the
unrestricted bound to a precise local separation statement with no arbitrary
head parameters. The exact five-label separation certificate has also passed
an independent vertex-based check.

## 1. Canonical-head reduction (mathematical proof)

Let the original tree have vertex set `[N] \\ {a}`, root `r`, and each edge
omitted, linear in either orientation, or a function `σ(x_i-x_j)` in either
orientation. Its unit is

\[
U(x)=\sigma\bigl(x_r-x_a+\sum_e\operatorname{term}_e(x)\bigr).
\]

Fix a top tie set `T`, with coordinates zero on `T` and distinct sufficiently
separated negative integral powers of `B` outside. Freeze the edges whose
endpoints do not both belong to `T`. In a neighbourhood of this point the
preactivation has the form

\[
b\cdot x+\sum_{(i,j)\in H_T}\sigma(x_i-x_j),
\]

where `H_T` consists of the original hinge edges with both endpoints in `T`.
If the preactivation is nonzero at the base point, the outer ReLU is locally
zero or redundant, so the germ is a sum of functions of at most two
coordinates. Otherwise the usual base-`B` digit argument gives `b_o=0` for
all `o` outside `T`. The apex coefficient is always `b_a=-1`, hence `a∈T`.

If `H_T` is disconnected on `T \\ {a}`, it has at most `|T|-3` edges. Its
pyramid therefore has dimension at most `|T|-2`. Its support function
vanishes in the top quotient `L_(|T|-1)/L_(|T|-2)`.

Suppose instead that `H_T` is connected. Then it is a connected subtree of
the original tree. It already has `|T|-2` edges, so every original edge with
both endpoints in `T \\ {a}` is one of these retained hinge edges. There are
no internal omitted or linear edges. Each component `C` of the original
tree outside this subtree attaches at exactly one vertex `t_C` of it.
Summing the coefficients `b` over `C`, all internal edge contributions cancel:

\[
0=\sum_{o\in C}b_o=\mathbf 1_{r\in C}
  +\text{contribution at the outside end of the unique boundary edge}.
\]

Thus the boundary contribution at `t_C` is `+1` exactly when `C` contains
`r`, and zero otherwise. It follows that

\[
b=e_{r'}-e_a,
\]

where `r'=r` if `r∈T`, and otherwise `r'` is the attachment of the unique
outside component containing `r`. The top germ is therefore a canonical
root-head tree unit on `T`, with all its subtree edges retained as hinges.
There are **no arbitrary large integer heads** in this top-dimensional case.

This reopens the path/twin separation route. The previous experiment with
arbitrary heads up to five at a five-label tie does not refute separation
of these realizable top germs modulo lower-dimensional functions.

### Definition-level checks

`dfs_review_flow_check.py` independently enumerates labelled original trees,
all five effective edge states, all tie sets of size at least three, and all
orders outside the tie. It checks freezing directly against integral
preactivation evaluation, outside balance, the canonical head, and the
attachment formula. Apex and root are fixed to `0,1`, without loss by
relabeling. No sampling is used.

| N | configurations | zero preactivations | connected germs | root outside |
|---|---:|---:|---:|---:|
| 5 | 52,000 | 8,216 | 1,160 | 432 |
| 6 | 12,265,625 | 664,053 | 65,872 | 31,936 |

All checks passed. These finite checks supplement the proof above.
Producer: `python3 research/sN/trees/dfs_review_flow_check.py N`; corresponding
logs are `dfs_review_flow_5.log` and `dfs_review_flow_6.log`.

## 2. Counting no-twin connected subtrees (mathematical proof)

This count does not require a degree bound, a head-size bound, or a count of
orders outside the tie set. Let `G` be any tree on `n` vertices, and consider
nonempty vertex subsets `S` such that `G[S]` is connected and can support a
canonical-root germ without twin leaves. Twin leaves have the same neighbour,
the same edge orientation, and the same head coefficient. All leaves except
possibly the root have head zero. Thus at most **three original leaves** at
any vertex of `G` can be selected: at most one nonroot leaf of each of the two
orientations, and possibly the root leaf.

Let `ν` be the matching number of `G`.

* If `ν≥n/10`, fix a vertex `v∈S` and root `G` at `v`. Connectedness forces
  `S` to be ancestor-closed. On each edge of a maximum matching, the pattern
  parent absent / child present is forbidden. The matching edges are disjoint,
  so the number of such subsets is at most
  `3^ν 2^(n-2ν)=2^n(3/4)^ν`. Sum over the at most `n` choices of `v`.
* If `ν<n/10`, choose a minimum vertex cover `C` of size `ν` (a tree is
  bipartite). Its complement is independent. At most `ν-1` vertices of the
  complement have degree at least two, because their total degree is at most
  `n-1`; consequently it contains at least `n-2ν+1` original leaves. These
  leaves attach to the `ν` vertices of `C`. Group the leaves at each vertex
  into disjoint groups of four. There are at least
  `(n-2ν+1-3ν)/4=(n-5ν+1)/4≥n/8` groups. No group can be entirely selected.
  Each group admits at most 15 of its 16 membership patterns, so there are
  at most `2^n(15/16)^(n/8)` subsets.

Therefore the total number of such subsets is at most

\[
n\,2^n e^{-cn},\qquad c=\frac18\log\frac{16}{15}>0,
\]

for nontrivial trees; small arities can be handled separately. Here
`(3/4)^(n/10)≤e^(-cn)`.

The original hinge graph may be a forest rather than a tree, but a surviving
connected tie set is still connected in the original spanning tree, so this
count applies unchanged.

### Exact remaining lemma sufficient for the unrestricted exponential bound

For every `m≥m0`, the simplex support function is outside the span, modulo
`L_(m-2)`, of canonical-root tree pyramids on `m` labels whose underlying
hinge tree has a pair of twin leaves.

If this separation holds, each tie set of size at least `m0` in any maximum
expansion must have at least one surviving non-twin top germ. The preceding
count bounds the tie sets covered by a fixed original unit. Covering all
`2^N-O(N^(m0-1))` tie sets then proves an unrestricted exponential lower bound,
with base at least `exp(c)>1` up to polynomial factors. The lower-bound proof
would consume only this separation statement; no uniform all-head
mixed-difference functional is needed.

A stronger path-separation lemma would give a much better bound: every
connected induced path is specified by its two endpoints, so one original
tree has only polynomially many eligible tie subsets.

## 3. Coordinate flags are insufficient, even with canonical heads

`dfs_review_root_flags.py` exhausts all 640 labelled rooted oriented stars on
five labels (one apex, four tree vertices) and all 60 coordinate-deletion
flags. Their modular evaluation rank is 30, unchanged on adding the simplex.
This diagnostic was strengthened to an exact rational identity: a 12-term
integer combination of these star-unit flag vectors equals the simplex vector.
The script solves a rational subsystem and checks all 60 equations exactly.
The complete witness is in `dfs_review_root_flags_5.log`.

This refutes only the coordinate-flag separation route. It does **not** prove
that the corresponding functions represent the maximum, nor that their
classes span the simplex in the full top quotient.

Producer (SymPy is supplied by the existing research environment):
`OPENBLAS_NUM_THREADS=1 research/sN/dfs/h4-general-neurons/venv/bin/python research/sN/trees/dfs_review_root_flags.py 5`.

## 4. Independent verification of the five-label complete-flag separator

The coordinator's `all_tree_dfs/complete_flags.py` constructs six subspace
flags with weights `(-1,3,30,3,-3,-12)` whose symmetrized functional annihilates
all canonical-root star pyramids and is nonzero on the simplex. At five labels,
these are all nonpath tree shapes.

`dfs_review_flag_certificate.py` checks the result by a different mechanism:
it reconstructs the six fixed direction sequences from the saved subspaces,
then applies successive maximum-face minus minimum-face operations directly
to each complete vertex list, ending with segment width. It never calls the
producer's recursive pyramid-facet invariant. All 640 labelled rooted oriented
stars give exactly zero after symmetrization over 120 label permutations; the
simplex gives exactly 120. Explicit lower-dimensional controls in dimensions
one, two, and three also vanish.

Every flag functional annihilates `L_3`: each exposed-face difference lowers
the support-function dimension filtration by one, and final width annihilates
linear functions. Thus this is a finite exact separation result modulo `L_3`,
not merely a point-sampling result. It is not yet a uniform theorem in `m`, and
it has not been formalized in Lean.

Producer:
`OPENBLAS_NUM_THREADS=1 research/sN/dfs/h4-general-neurons/venv/bin/python research/sN/trees/dfs_review_flag_certificate.py`.
Receipt: `dfs_review_flag_certificate.log`.

## 5. Unconditional cubic consequence of the five-label certificate

For every expansion by arbitrary `Trees.TreeFace.unit` terms plus `A_N`,
with `N≥5` and unit index set `K`, the preceding canonical-head reduction and
the independently verified five-label separator give the mathematical bound

\[
\binom N5\ \leq\ \left\lfloor\frac{(N-3)^2}{4}\right\rfloor |K|.
\]

Indeed, for every five-element top tie set `T`, its maximum germ is the
five-label simplex. All lower-dimensional germs disappear in the quotient.
The certificate annihilates every surviving star germ, so at least one
original unit must have its nonapex tied vertices forming a four-vertex path.
One unit's apex is fixed, so its possible tie sets are counted by the
four-vertex paths in its original tree `G` on `n=N-1` vertices. A path has a
unique middle edge, giving

\[
P_4(G)=\sum_{uv\in E(G)}(\deg u-1)(\deg v-1).
\]

For the bipartition `A,B` of `G`, this is at most

\[
\left(\sum_{u\in A}(\deg u-1)\right)
\left(\sum_{v\in B}(\deg v-1)\right)
=(|B|-1)(|A|-1)
\leq\left\lfloor\frac{(n-2)^2}{4}\right\rfloor.
\]

Covering all five-element tie sets proves the assertion. Its asymptotic form
is `|K|≥(1/30+o(1))N^3`. This result uses a finite exact certificate and a
mathematical reduction; it has not been formalized in Lean. It improves the
existing unrestricted quadratic bound once `N≥9` (equality at `N=8`).

## 6. Fourier instrument and six-label twin separation

Put `n=m-2` and `g(t,s)=σ(t+Σ_j σ(s_j))`. Distributionally,

\[
\partial_t^2\prod_j\partial_{s_j}g
=\left(\prod_j H(s_j)\right)\delta^{(n)}(t+\sum_j s_j).
\]

Consequently, away from its polar hyperplanes, its Fourier transform is
`i^(-m)` times `ω_t^(m-4)/Π_j[ω_sj(ω_sj-ω_t)]`. The canonical tree change of
coordinates is unimodular. If `a` is the apex and `q_e` is the sum of
frequencies on the component away from the root after deleting edge `e`,
the associated generic rational function is

\[
R_U(\omega)=\frac{(-\omega_a)^{m-4}}
 {\prod_e q_e(q_e+\varepsilon_e\omega_a)},\qquad \sum_i\omega_i=0,
\]

where `ε_e=+1` for orientation away from the root and `−1` for orientation
towards it. With this common normalization the simplex gives
`R_max=(-1)^(m-1)/Π_i ω_i`. The sign does not affect a separation test.
Every function in `L_(m-2)` has Fourier transform supported on finitely many
proper subspaces, and therefore vanishes generically. Thus a finite exact
rational evaluation separator is a valid top-quotient separator.

`dfs_review_fourier.py` enumerates rooted oriented tree isomorphism classes
and sums each over every label permutation. It proposes rows modulo a prime,
then computes and verifies the separator exactly over the rationals against
every orbit column and the target. At five labels it reproduces nonpath
separation (10 orbits, ranks 5 and 6). At six labels, all canonical units with
twin leaves have 37 orbits; a 21-point exact rational separator annihilates
all 37 and evaluates to one on `1/Π_i ω_i`. The complete exact rows and
separator are saved in `dfs_review_fourier_6_twin.json`, with its producer
log in `dfs_review_fourier_6_twin.log`. This proves the six-label instance
of the twin separation lemma, subject only to the Fourier derivation above;
it is not a uniform theorem and has not been formalized in Lean.

### Six-label nonpath obstruction and normalization control

The stronger assertion that every arity needs a path germ fails at six
labels, at the level of every complete flag. Let `ΣU` denote the unnormalized
sum of a canonical unit over all `6!` label permutations. All units below
have apex `0`, root `1`; `(i,j)` denotes generator `e_i-e_j`.

| Unit | Oriented tree edges | Coefficient |
|---|---|---:|
| A | (2,1),(3,1),(4,2),(5,2) | 1/240 |
| B | (2,1),(3,1),(2,4),(2,5) | −1/240 |
| C | (2,1),(1,3),(4,2),(5,2) | −1/120 |
| D | (2,1),(1,3),(4,2),(2,5) | 1/120 |
| E | (2,1),(3,2),(4,2),(5,2) | −1/720 |

The sum with these coefficients has exactly the same complete-flag array as
the six-label simplex. Every shape is a fork or a star. The exact check
enumerates all label permutations and all nonzero full chains of exposed
face direction subspaces, with rational arithmetic. Receipt:
`dfs_review_fullflag_witness_6.json`. Its status is
`ALL_COMPLETE_FLAGS_NEGATIVE_TARGET` because the input Fourier witness file
uses the opposite coefficients, normalized to `1/Π_i ω_i`; the table above
includes the necessary minus sign for `m=6`.

The reconstruction argument in the paper (the subsection “Reconstruction
from opposite exposed faces”) extends from the displayed caterpillar sum to
any finite sum of polytope support functions, by triangulation and the same
linear sweep operator. Applying it recursively shows that vanishing complete
flags imply membership in `L_(m-2)`: nonfacet directions already expose
dimension at most `m-3`, while facet-normal directions reduce to the next
flag level. At dimension one, zero width means a linear function. With this
mathematical reconstruction result, the table is a nonpath representation of
`max_6` modulo `L_4`. No explicit decomposition of the remainder into
lower-dimensional support functions, nor a Lean proof, is supplied here.
Unit D has no twins, so this does not refute twin separation.

### Seven-label diagnostic and the uniform residual

`dfs_review_fourier_fast.py` evaluated all 176 six-tree-vertex canonical twin
orbits at 200 frequency points modulo the prime 1,000,003. The ranks were
83 and 84 after adding the maximum column. The run took 15 seconds, within
its declared 110-second budget. Files:
`dfs_review_fourier_fast_7_twin.json` and `.log`. This is **only a modular
diagnostic**, not a rational certificate. It supports the same pattern as
the exact five- and six-label results.

The exact unresolved analytic statement is the twin separation lemma in
Section 2, uniformly in `m`. Equivalently, it suffices to prove that the
rational function `1/Π_i ω_i` is not in the rational span of the symmetric
canonical twin-tree fractions displayed above. No such uniform proof is
provided here. Coordinate residues alone are too weak; the five-label exact
coordinate-flag counterexample already proves that. Evaluating at all
`m`th roots of unity also fails as a proposed functional: several five-label
twin orbit sums are nonzero there. Noncoordinate cut poles remain a viable
source of information, but their cancellations across different tree
topologies have not been classified.

One useful simplification is exact. For `m≥4`, every canonical-tree fraction
has only simple coordinate poles. A cut sum `q_e` is a coordinate precisely
when its away-root component is one leaf. A shifted cut `q_e+ω_a` is a
coordinate up to sign precisely when the complementary tree component is
the singleton root. A shifted cut `q_e-ω_a` is never a coordinate. The two
types cannot duplicate a coordinate pole, because the root cannot also be
a nonroot leaf. Therefore any linear combination of these fractions whose
noncoordinate poles cancel has denominator dividing `Π_i ω_i`. Its
homogeneity degree is `-m`, so multiplication by that product leaves a
degree-zero polynomial: the combination is necessarily `c/Π_i ω_i`.
This statement does not even require symmetrization. Thus the universal
twin problem can be stated sharply: **if every noncoordinate cut pole
cancels in a combination of twin-tree fractions, prove that `c=0`.**

## 7. The one-descent upper dictionary: a precise algebraic test

Permutations with at most one descent are exactly concatenations of two
increasing runs. There are `2^N-N` distinct such permutations. Including all
nonempty cuts and all three face states therefore gives at most
`(2^N-N)(2^(N-2)-1)3^(N-2)=O(12^N)` units. Thus a uniform spanning theorem
for this dictionary would give the requested exponential upper bound.
The five-label dictionary does span the maximum, but the six-label dictionary
does **not**, as certified by the exact obstruction below. Thus this family
cannot provide a uniform exponential construction.

Independent certificate audit: `dfs_review_upper_certificate.py` reconstructs
the equations from the saved 270 nonzero records only. All 1,970 regenerated
exact equations across all 120 chambers pass. A separate direct evaluation
at all 3,125 points of `{-2,-1,0,1,2}^5` also passes, checking the convention
that unit features are `σ(x_i-x_j)` while auxiliary pair terms are maxima.
The three nonzero auxiliary coefficients form one function in the first
layer's span; carrying it through the second hidden layer uses two ReLUs.
Thus the certificate gives second width **272**, including those channels.
Receipt: `dfs_review_upper_certificate_5.json` and `.log`.

Six-label obstruction: the full-hinge dictionary has 717 distinct functions.
At 747 generic frequency points its modular evaluation ranks are 711 and
712 after adjoining the maximum. The coordinator found six independent
relations with coefficients in `{-1,0,1}` among the rational-function columns
and verified each as a formal polynomial identity after clearing
denominators. These prove rational rank at most 711, while the augmented
modular rank proves rational rank at least 712. Hence no rational or real
coefficient solution exists. Every omitted or linear edge state lowers the
polytope dimension below six-label top dimension, so no face-state term can
repair this obstruction.

`dfs_review_upper_obstruction.py` independently regenerates all 717 units,
recomputes graph cuts, checks all 747 modular evaluation rows, recomputes
both ranks, and verifies the six exact polynomial identities and their
rational independence. All checks pass. Receipt:
`dfs_review_upper_obstruction_6.json` and `.log`.

The most direct shuffle shortcut has a concrete limitation. In the group
algebra let

\[
T_2=\sum_{S\subseteq[N]}[\operatorname{inc}(S)\operatorname{inc}(S^c)].
\]

This is the inverse two-riffle-shuffle operator: the identity permutation
occurs `N+1` times, and every one-descent permutation occurs once. It acts
on the symmetric target by the scalar `2^N`. However, it does not itself
project arbitrary units to symmetric functions. It is invertible over the
rationals (its descent-algebra eigenvalues are positive powers of two), so
averaging a single nonsymmetric orbit seed with `T_2` cannot remove its
nonsymmetric component. This invertibility has an elementary proof: for
integer `a≥1`, define `T_a` by assigning each label one of `a` colours and
stably sorting by colour. The coefficient of a permutation with `d` descents
is `binom(a+N-d-1,N)`, a polynomial in `a`. Two stable sorts compose to
`T_a T_b=T_(ab)`. Writing `T_a=Σ_(k=1)^N a^k E_k` and comparing coefficients
gives `E_i E_j=δ_(ij)E_i` and `Σ_k E_k=T_1=1`. Hence
`T_2^(-1)=Σ_k 2^(-k)E_k`; also `E_N=(1/N!)Σ_π π` is the full symmetrizer.
A proof must use relations among different cuts or
face states, or find a suitable invariant combination before this averaging.
The full symmetrizer can be expressed by a polynomial in `T_2`, but powers
allow successively more increasing runs, so that identity alone loses the
exponential-size support restriction. This is an obstruction to the naive
shuffle argument, not a disproof of the dictionary.

The six-label exact obstruction above supplies the separate disproof of the
dictionary. The group-algebra calculation identifies why the proposed
generic shuffle proof was insufficient even before that obstruction.

### Exponential candidate families after the shuffle shortcut

An alternative is all noncrossing trees for one fixed cyclic order of labels,
with every apex, root, orientation, and face state. This is exponentially
large without any unproved enumeration formula: every noncrossing tree
extends to a triangulation; there are at most `4^n` triangulations on `n`
vertices, each with fewer than `2n` edges, hence at most `16^n` possible
noncrossing trees. The five allowed edge states give at most a further
`5^(n-1)` factor. This family is preserved by restricting to a connected tied
subtree, which is a useful structural property for a possible induction.

It remains necessary to establish an actual dictionary identity. The fact
that an associahedral/Cambrian fan can refine the simplex fan only says that
the maximum is linear on its cones; it does not express the maximum as a
signed sum of the permitted tree pyramids. Likewise, recursively writing a
maximum along a fixed planar binary tree gives additional depth. The convex
hull operation on polytopes is not linear on virtual polytopes, so a
lower-dimensional class identity cannot simply be substituted into that
recursion while preserving two hidden layers.

Another candidate is all separable permutations, generated by repeated
direct and skew sums of intervals, together with all cuts and face states.
Their recursive description is better suited to induction than a bound on
the number of descents. But a uniform identity is still missing, and these
families are not nested: for example `2413` has one descent and is not
separable. No positive result at five labels for the one-descent family
automatically transfers to the separable family.

### General face-closure sufficiency lemma

The paper's error-peeling argument applies to an arbitrary finite family of
polytopes `P_j`, not just the symmetric caterpillar sum. Let `Δ` be a
`d`-simplex and suppose

\[
h_\Delta\in\operatorname{span}\{h_{P_j}\}+L_{d-1}.
\]

Then `h_Δ` belongs to the span of support functions of **all faces of the
same `P_j`**, together with linear functions. To prove this, successively
apply opposite exposed-face differences that delete vertices of `Δ`. Each
operation lowers the dimension filtration, producing for every simplex
face `Δ_T` an error in `L_(|T|-2)` whose other terms are original-polytope
face functions. Induct on `|T|`. At a fixed size, choose one direction
orthogonal to each maximal-dimensional residual direction space while
avoiding orthogonality to the simplex direction space and the other residual
spaces. The sum of those derivatives preserves each maximal residual term
exactly once, so subtraction lowers its dimension. On the displayed
expression, those same derivatives produce only proper simplex faces and
faces of the original `P_j`, already in the desired span. Iteration leaves
a linear error and proves the claim.

Consequently a certified top-class identity for the noncrossing family is
enough for exact dictionary sufficiency at that arity; no separate chamber
LP is needed once the top-class statement is established. A uniform
top-class identity would prove an exponential upper construction. Merely
passing a modular Fourier test does not establish that identity. Complete
flag equality plus reconstruction is one available exact certification.

### Next discriminating analytic lemma: cancellation before uncrossing

Term-by-term planar uncrossing cannot hold in the top quotient. Removing an
edge of a noncrossing tree splits its nonapex cyclic order into two cyclic
intervals: interleaving vertices in the two connected components would force
their connecting paths to cross. Thus its unshifted cut poles are interval
sums, allowing for the omitted apex. For example, at six labels the
alternating cut `{0,2,4}|{1,3,5}` can occur in a crossing tree but in no
noncrossing tree with any apex. The shifted factors do not repair this:
`q+ω_a` corresponds to adjoining the apex to an interval, while `q-ω_a`
has three coefficient levels and cannot equal an ordinary subset sum.
A crossing unit carrying such a pole cannot individually belong to the
noncrossing rational span.

A suitable replacement is a **pole-local saturation lemma**. Let `V_N` be
the rational span of all canonical caterpillar fractions, let `V_N^NC` be
the noncrossing subfamily's span, and let `A_N^NC` be its denominator
hyperplane arrangement. Ask whether

\[
V_N\cap\mathbb Q[\omega,\{\ell^{-1}:\ell\in A_N^{NC}\}]
=V_N^{NC}
\quad\text{in homogeneous degree }-N.
\]

The weaker statement only for the coordinate-pole line `Q/(Π_i ω_i)`
already suffices. The existing full caterpillar class identity puts that
line in `V_N`; saturation would put it in the noncrossing span. A concrete
induction target is the kernel of the residue at a minimal alternating cut:
show that pole-cancelling combinations are generated by terms avoiding the
cut and local cancellation identities that decrease crossings. This is
strictly weaker than the false termwise uncrossing claim. No such kernel
classification is proved here.

There is an exact residue factorization worth preserving. At an ordinary cut
`q_A=0`, let `B` be the root-side tree component and write `a=ω_apex`. Then

\[
\operatorname{Res}_{q_A=0}R_T
=\frac{(-a)^{N-4}}{\varepsilon_e a}\,K_A(a)K_B(a),
\qquad
K_C(a)=\prod_{f\in E(C)}\frac1{q_f(q_f+\varepsilon_f a)}.
\]

The component `A` is rooted at its attachment to the deleted edge. On the
residue hyperplane its total frequency is zero, while the total on `B` is
`-a`. Cuts in `B` that formerly contained `A` reduce to the same cut sums
with `A` deleted; this proves the displayed factorization directly. The
remaining obstacle is now explicit: `K_A` is a zero-total tree kernel with
an external shift parameter `a`, not a smaller canonical tree fraction with
an apex among its labels. An induction must include these boundary-charge
kernels rather than silently invoke the smaller canonical theorem.

## 8. Eight-label coverage audit and the first missing tree topology

The completed eight-label noncrossing-caterpillar diagnostic has 4,165
dihedral-orbit columns and modular ranks 4,097 and 4,098 at 4,232 test rows.
At the time of this entry, exact right-kernel identities are being checked
to promote that modular obstruction. This entry does not itself claim the
rational obstruction.

`dfs_review_nc8_coverage.py` independently checks the family and orbit
coverage without regenerating the large Fourier matrix. Original caterpillar
descriptions have an intrinsic characterization: orient a tree away from
a source `s`, choose a distinct marked root `r`, and require the `s`–`r`
path to contain every nonleaf vertex. Reversing that path and exchanging
its endpoints gives the same normalized function, so unordered endpoint
pairs suffice. Every such description is realized by listing successive
spine vertices with their intervening leaves in a word `π`, and taking
the spine positions for `S`; conversely the original `π,S` construction
has exactly this form.

The independent Prüfer enumeration gives exactly **66,416** normalized
functions, matching the coordinator's input with no missing or extra unit.
Every one of its **4,165** D8 orbits also matches the direct dihedral action.
Among the **1,428** noncrossing trees on seven cyclically ordered vertices,
**1,372** are caterpillars and **56** are subdivided claws. The complete
audit takes four seconds; receipt `dfs_review_nc8_coverage.json`.

Eight labels are the first arity at which a noncaterpillar hinge tree is
possible. Such a tree needs a nonleaf vertex with three nonleaf neighbours,
and therefore at least seven vertices. At exactly seven vertices its shape
is forced: a degree-three centre with three length-two arms. Thus the first
observed NC-caterpillar obstruction coincides with the appearance of this
single omitted topology; this coincidence suggests a specific enlargement,
but is not a proof that it repairs the obstruction.

`dfs_review_nc8_claw.py` independently enumerates the shape by choosing its
centre, matching the remaining six vertices into three arms, and choosing
the inner endpoint of each arm. It keeps the 56 noncrossing embeddings,
then permits an arbitrary source and arbitrary marked root, including
source=root. The resulting exact extension has **12,544** labelled units
and **784** D8 orbits, including 3,136 diagonal source=root units. Its JSON
contains every oriented edge, cut sum, and orbit for subsequent tests:
`dfs_review_nc8_claw.json`.

This extension has a useful orientation-free formula. For any tree `T`,
set

\[
B_T(x)=\sum_{uv\in E(T)}\max(x_u,x_v)-\sum_{v\in T}x_v.
\]

The tree unit oriented away from source `s` with marked root `r` is
`σ(B_T(x)+x_s+x_r-x_a)`. Indeed, each non-source vertex appears once as
a child in the oriented tree, and `σ(x_u-x_v)=max(x_u,x_v)-x_v`.
This proves source/root symmetry directly. Moreover,

\[
B_T(\mathbf1_S)=\#\operatorname{components}(T[T\setminus S])-1,
\]

with zero components for the empty graph. Thus a uniform planar-tree
construction can be studied through forest component counts, while retaining
an exponentially sized family and avoiding arbitrary edge orientations.

The Boolean top coefficient has an equally explicit formula. For `N≥3`,
the full alternating Boolean sum annihilates the preactivation because it
has degree at most two on Boolean inputs. If the apex coordinate is zero,
that preactivation is nonnegative. If the apex coordinate is one and `C`
is the set of zero-valued tree labels, it equals
`cc(T[C])-1_(s∈C)-1_(r∈C)`. It is negative precisely when `C` is connected
and contains both marked vertices, in which case it is `-1`. Therefore

\[
\ell(U_{a,s,r})=
\sum_{\substack{C\subseteq V(T),\ T[C]\text{ connected}\\s,r\in C}}
(-1)^{n-|C|},\qquad n=N-1.
\]

Let `P` be the source–root path, allowing a singleton when source=root.
Every connected `C` containing its endpoints contains `P`. Off the path,
each branch can be selected in an ancestor-closed way. If `F(v)` is the
alternating sum of these selections, including the empty choice, then
`F(v)=1-Π_child F(child)` and `F(leaf)=0`. Consequently

\[
\ell(U_{a,s,r})=(-1)^{n-|P|}\prod_{\text{branches off }P}F(\text{branch}).
\]

For an original caterpillar description, all off-path branches are single
leaves, so this coefficient vanishes unless the marked path covers the
whole tree. For the subdivided claw with its source and root at two outer
leaves, the remaining branch has length two and `F=1`; its top coefficient
is therefore `+1`. The claw is the first **noncaterpillar topology**, not
the first branching unit with nonzero Boolean top weight once arbitrary
marked pairs are allowed. For example, in a five-vertex fork, marking its
two short leaves leaves a length-two off-path branch and also gives `+1`;
that marked path omits a nonleaf vertex, so the original construction
excludes it. An alternative small enlargement is therefore to retain the
noncrossing caterpillar shapes but remove the spine-cover restriction on
the marked pair. These formulas identify useful new units, but do not
themselves cancel their non-braid
crossings or prove an upper construction.

## 9. Exact rational verifier audit and the Fourier-to-class bridge

The coordinator's `all_tree_dfs/rational_identity.py` is an exact identity
algorithm, not a sampling test. Regard an expression as a rational function
of one selected variable over the rational-function field in the others.
Canonical affine forms identify equal poles. At each pole of multiplicity
`r`, the code expands the numerator and every other denominator to Taylor
order `r-1`, collecting every Laurent principal coefficient recursively.
After those vanish, the expression is a polynomial of degree at most the
maximum numerator-minus-denominator degree `D` of its terms. If `D<0` it
is zero; otherwise vanishing at `D+1` distinct legal constant sections
proves it is zero. Recursion decreases the number of variables. Memoization
only identifies expressions differing by a nonzero rational scalar.
This establishes the algorithm's correctness.

The independent controls in `dfs_review_rational_verifier.py` check affine
partial-fraction identities, their repeated derivatives, and binomial
quotient identities in one, two, and three variables. Each identity passes
and each perturbation by `7/13` fails: 96 exact checks in total. Receipt:
`dfs_review_rational_verifier.json` and `.log`.

`dfs_review_nc7_identity.py` separately rebuilds the seven-label expression
from the saved graph edges and coefficients, checking the orbit partition,
tree validity, noncrossing, and every cut sum before invoking the audited
verifier. The identity passes exactly: 6,909 supported labelled units,
6,910 normalized terms including the simplex, 5,202 recursive calls, and
23 seconds. Receipt: `dfs_review_nc7_identity.json` and `.log`.

There is a short rigorous bridge from the generic Fourier identity to the
dimension quotient. Let `f` be a finite real linear combination of polytope
support functions on a `d`-dimensional vector space, and let `R_f` denote
the ordinary rational part of its Fourier transform, away from its polar
hyperplanes. Then

\[
R_f=0\quad\Longleftrightarrow\quad f\in L_{d-1}.
\]

The reverse implication follows because a support function of a
lower-dimensional polytope, modulo a linear function, is constant along a
nonzero direction; its Fourier transform is supported on a proper
subspace. For the forward implication, the key exact identity is

\[
\operatorname{Res}_{\eta=0}R_f(\xi,\eta)
=-i\,R_{(D_u f)|_{u^\perp}}(\xi),\qquad u=e_d,
\]

with the Fourier convention `exp(-i〈ω,x〉)`. Only the nonzero scalar matters
for vanishing. Here the residue is the coefficient of `η^(-1)`, and the
right side is the generic transform in dimension `d-1`.

To prove the residue identity, triangulate each polytope. The support
cutting identity expresses its support function as a sum of full-dimensional
simplex support functions modulo `L_(d-1)`. That remainder vanishes on the
left; its opposite-face derivative belongs to `L_(d-2)`, so it also vanishes
on the right. Thus it suffices to check a simplex. Its rational transform
has simple poles precisely at the facet direction spaces. If `u` is not a
facet normal, both sides vanish. Otherwise translate the opposite vertex
to zero and write the facet vertices as `(w_j,h)`, `1≤j≤d`, with `h≠0`.
Let `T` have those vertices as rows, and let `B` have rows `w_j-w_d`,
`1≤j<d`. Put `(λ_1,…,λ_d)=T^(-T)(ξ,η)` and `λ_0=-Σ_j λ_j`.
The simplex Fourier formula gives

\[
R_{h_P}=\frac{(-1)^d i^{-d-1}}{|\det T|\prod_{j=0}^d\lambda_j},
\qquad
\lambda_0=-\eta/h,\qquad |\det T|=|h|\,|\det B|.
\]

At `η=0`, the remaining `λ_j` are exactly the quotient frequencies for the
facet simplex. Taking the residue cancels `h` and gives `-i` times its
Fourier formula, multiplied by `sgn(h)`. This sign is precisely the sign
with which that facet occurs in `D_u h_P`. Hence the residue identity holds
for every direction and every finite support-function sum.

Now induct on `d`. In dimension one, a continuous homogeneous piecewise
linear function is a linear function plus `c|x|`; its generic transform
vanishes exactly when `c=0`. In higher dimensions, `R_f=0` implies by the
residue identity and induction that every `D_u f` lies in `L_(d-2)` (its
component along `u` is linear and immaterial). The paper's simplex
reconstruction argument then gives `f∈L_(d-1)`. The same reconstruction
argument applies in dimension two; it uses segment facets and the sweep
map taking linear functions to `L_1`.

Equivalently, successive residues recover the opposite-face differences
along a complete flag. The final one-dimensional coefficient of `ξ^(-2)`
is proportional to segment width. Thus an exact rational identity also
certifies equality of every complete flag directly.

Consequently the exact seven-label rational identity certified by
`nc_rational_identity_7.json` does imply a genuine noncrossing top-class
identity modulo `L_5`, and the general face-closure lemma gives exact
seven-label dictionary sufficiency. This is a mathematical consequence of
the audited exact identity and the bridge just proved; it has not been
formalized in Lean and remains a finite-arity result.

## 10. Evidence corrections

The old Step 13 in `PROGRESS.md` labels the nonexistence of a finite uniform
all-head mixed-difference functional as a consequence of bounded-resolution
measurements. Those experiments alone do not prove the universal assertion.
They show failure of the tested instruments. A rational functional at a
previously untested resolution remains logically possible.

Likewise, modular rank inclusion is not real functional inclusion. Even a
rank increase modulo a prime needs a rational check or an independent upper
bound on the rational rank of the old matrix before it certifies real
separation: a rational dependence can have a denominator divisible by the
prime. The exact rational witness and exact vertex certificate above avoid
this problem.

## 24 October 2026 continuation: exact lower-bound scope and a sharper residual

### Semantic scope of the current Lean statements

The exponential headline is a statement about specified dictionary
expansions, not arbitrary two-hidden-layer ReLU networks. A `TreeFace`
has a tree on all nonapex labels, head `x_root-x_apex`, and one state per
edge: omitted, a signed coordinate difference, or `σ(x_i-x_j)` in either
orientation. Every edge coefficient is one and all biases are zero. Output
coefficients may be arbitrary signed reals. The auxiliary term belongs to
the explicitly defined first-layer span. Repeated edges, genuine cycles,
and arbitrary heads or inner weights are not part of this model.

`tree_reduced_exponential_two` gives `|K|≥(7/6)^N/(N+1)` when every
description has reduced degree at most two. The reduction deletes the
hinge-degree-one vertices with `κ=0` **once**, not iteratively. More
generally, `tree_reduced_exponential` has base `1+1/(2Δ+2)` with fixed
`Δ≥2` and threshold `N≥6Δ+8`. Its class includes the paper's caterpillar
faces and the rooted-star faces used for the comparison with Brunck et al.

`CoverageMain.lean` is already imported by the stable public root. It gives
an exponential bound under a fixed bound `s` on the number of adjacent
hinge leaves with `κ=1`, with base `1+3/(16(s+1))`. This permits arbitrary
internal branching. The new, currently untracked `Unified.lean` and
`UnifiedMain.lean` strengthen the count using
`ω(v)=# adjacent κ=1 hinge leaves +1[there is a nonleaf hinge neighbour]`.
Their exact conclusion is

\[
\binom Nm\le(2\Delta+2)^m(|K_1|+|K_2|),\qquad
|K_1|+|K_2|\ge\frac{(1+1/(2\Delta+2))^N}{N+1}
\]

for `N≥3`, `Δ≥2`, an existing caterpillar expansion family `K1`, and
additional tree faces `K2` satisfying `ω≤Δ`. Letting `Δ` or `s` grow with
`N` does not give a fixed-base exponential theorem. In particular these
statements still do not cover arbitrary tree orientations and face states
without a structural hypothesis. The unrestricted all-tree bound presently
proved in public Lean is quadratic; the cubic improvement above uses its
separately checked finite certificate and mathematical bridge.

### A degree-two cover for arbitrary source/root full-hinge trees

There is a stronger mathematical corollary than the direct `ω≤3` estimate.
Take any tree shape, orient every generator from parent to child in the
rooting at a source `s` (the function is `σ(x_parent-x_child)`), retain
**every edge as a hinge**, and use an arbitrary marked head root `r`.
For nonapex vertices,

\[
\kappa_v=\deg_T(v)-1+\mathbf1_{v=s}+\mathbf1_{v=r}.
\]

Thus the only possible out-leaves are `s` and `r`, when they are distinct
tree leaves. If they do not share a neighbour, then `ω≤2`. If they do
share a hub `v`, only that hub can have `ω=3`. Use the existing heir
relation, with its child selector taken from the tree rooted at the marked
head root `r`. The hub is not poor because it has out-leaf neighbours.
No poor vertex can have heir `v`: the unique parent of `v` is `r`, whose
degree is one, whereas a poor vertex has degree at least two. Therefore
the hub's covering edges are just its two out-leaf edges. The entire
covering relation has maximum degree at most two. The existing general
cover theorem consequently gives the same per-unit factor `6^m`, and the
same exponential base **7/6**, for these full-hinge units.

This can be combined with the existing caterpillar and rooted-star face
dictionary, yielding a nonvacuous larger vocabulary with arbitrary tree
shapes. No assertion is made here that full-hinge source/root units alone
span the maximum in every arity. Nor does this argument cover all faces of
the newly added trees. A decisive counterexample to that extension is a
centre with `k` length-two arms: retain each centre–middle edge as
`σ(x_c-x_m)` but make each middle–outer edge linear `x_m-x_l`. Every
middle vertex then has hinge degree one and `κ=1`, so `ω(c)=k`. Both the
fixed-`ω` hypothesis and the degree-two covering relation can fail.

`dfs_review_continue_checks.py` exhaustively checks all 46,656 labelled
seven-input full-hinge trees with ordered source/root pairs. It computes
the normalized head and `κ` directly, builds the heir cover rooted at `r`,
and checks its covering property and maximum degree two. Genuine `ω=3`
instances are included and a witness is saved. The same run checks the
leaf rules below on all 52,000 five-input tree/state/tie/outside-order
configurations. All checks pass in 16.8 seconds, within a declared
30-second budget; receipt `dfs_review_continue_checks.json` and `.log`.

### Weaker local separation suffices, with a better exponential count

The all-tree exponential route needs only the following **out-twin
separation statement**, which is weaker than the earlier all-orientation
twin statement: for every `m≥m0`, `max_m` is outside the span modulo
`L_(m-2)` of canonical tree units having two distinct nonroot leaves
`l1,l2` at one hub `v`, both carrying `σ(x_li-x_v)`. Apex, root, tree,
and all other edge orientations may vary among units in the span. The
five- and six-label certificates already establish these finite cases;
no uniform proof is claimed.

Assume this statement. A connected top germ of an original tree unit must
then be free of such outward twin leaves for at least one summand at each
large tie set. Let `S=T\{apex}` and fix a nonroot original leaf `l` with
hub `v`. The head-flow reduction gives these exact necessary conditions:

* An omitted original leaf is outside `S`.
* A nonroot linear original leaf prevents any connected top germ: outside
  it has a nonzero frozen coefficient; inside it is isolated in the hinge
  graph.
* If its hinge is `σ(x_v-x_l)`, then `l∈S` iff `v∈S`. The reverse
  implication uses that a tied hub and untied negative leaf activate that
  hinge, giving the untied leaf coefficient `-1`, which cannot balance.
* If its hinge is `σ(x_l-x_v)`, then `l∈S` implies `v∈S`; two such
  nonroot leaves at the same hub cannot both be selected.

A selected nonroot original leaf cannot become the effective germ root:
its only neighbour is already in `S`, so no outside component can attach
there. The original head root is excluded from pairing, losing at most
one leaf. The apex is not a vertex of the original tree and causes no
additional loss.

Hence **every pair of nonroot original leaves at one hub forbids at least
one of its four membership patterns**. Two inward leaves must agree; an
outward leaf cannot be selected without an inward partner; two outward
leaves cannot both be selected; an omitted leaf is fixed absent.

Let the original tree have `n=N-1` vertices and matching number `ν`.
If `ν≥n/5`, connected subsets containing a fixed vertex are ancestor-closed
and each matching edge forbids one of four patterns, giving at most
`n·2^n(3/4)^(n/5)` subsets after summing over the fixed vertex. If `ν<n/5`,
take a minimum vertex cover of size `ν`. Its independent complement
contains at least `n-2ν+1` original leaves, hence at least `n-2ν` after
removing the possible head-root leaf. Pair leaves at each of the at most
`ν` hubs. There are at least `(n-3ν)/2>n/5` disjoint pairs, each allowing
at most three patterns, giving the same bound without the factor `n`.

Thus each unit covers at most

\[
n\,2^n(3/4)^{n/5}
\]

large tie sets. Covering all `2^N-O(N^(m0-1))` such sets yields

\[
|K|\ge\frac{2-o(1)}{N-1}(4/3)^{(N-1)/5}.
\]

The conditional exponential base is approximately **1.0592**, improving
the earlier conditional count while requiring a weaker local lemma.
The five-input finite control above includes 1,160 connected top germs,
1,126 without outward twins, and 438 original-leaf pair checks, all exact.

### Cubic and head-flow boundary audit

The cubic deduction survives rechecking: use `B=N+2` to dominate every
frozen integer coefficient; the apex coefficient is always `-1`; every
outside tree component has exactly one attachment to a connected tied
subtree. Disconnected retained hinges have at most `m-3` edges, so their
pyramid dimension is at most `m-2`. Auxiliary and nonzero-preactivation
germs belong to `L_1`. The five-label separator therefore forces an
induced four-vertex original-tree path, whose count is exactly
`Σ_(uv edge)(deg u-1)(deg v-1)` and at most `floor((N-3)^2/4)`.
The latter bound is sharp for balanced double stars. This reasoning does
not extend automatically to cyclic units: an outside component can have
several attachments, destroying the canonical-head transport argument.

### Local Lean verification receipt for the unified theorem

The commands `lake env lean MaxCaterpillar/Simplify/Unified.lean` and
`lake env lean MaxCaterpillar/Simplify/UnifiedMain.lean` both completed with
exit code zero. A separate stdin check imported `UnifiedMain` and printed
the fully explicit types of `unified_exponential` and
`treeFace_card_passes_le`; they retain the mixed-expansion and fixed
`OmegaLe` hypotheses stated above. `#print axioms` for
`unified_exponential` and `card_passes_le_unified` reports exactly
`propext`, `Quot.sound`, and `Classical.choice`. At this audit the two files
are untracked and not imported by the stable root: this is local Lean
verification, not public integration. The arbitrary-source/root degree-two
refinement above is a mathematical corollary, not a new Lean declaration.

### Cyclic formula audit and a global first-layer obstruction

The new `research/sN/cycles/cycle_fourier.py` general-head tree formula is
correct under `Σh_i=0`, `h_apex=-1`. With `t=h·x` and one difference
coordinate per oriented tree edge, the change of coordinates has determinant
of magnitude one. For the cut component `C` containing the positive edge
endpoint, write `q=Σ_(i∈C)ω_i`, `H=Σ_(i∈C)h_i`, and `a=ω_apex`.
Then the dual coordinates are `ω_t=-a` and `ω_s=q+aH`, giving denominator
factors `(q+aH)(q+a(H+1))` exactly as implemented.

For a consistently directed simple cycle, its generators sum to zero.
Every cube representative `t∈[0,1]^m` may be replaced by
`t-min_j(t_j)·1`, so the zonotope is tiled by the `m` deleted-edge path
zonotopes. Generic representatives have a unique zero coordinate, giving
disjoint interiors; coning to the common apex preserves this subdivision.
Thus their support functions add modulo lower dimension, as required for
the generic Fourier sum. Reversing an edge changes the head by minus its
original generator. Zero or one nonhinge cycle edge can contribute in top
dimension; two or more cannot. These observations justify the scope of the
coordinator's cycle tiling and formula, beyond its finite point controls.

Independently, a fixed sparse global first-layer graph cannot support the
maximum with two hidden layers, regardless of the second-layer coefficients.
If an independent triple exists, choose a generic point where exactly those
coordinates tie for the maximum. All first-layer pair features are locally
affine, so the network germ is one-hidden-layer. Its odd part is linear,
whereas `max_3(z)+min_3(z)` is not. Hence `α(G)≤2`, giving the elementary
Mantel bound on the number of distinct pair features.

The existing, stronger C4′ lemma in `research/sN/frontierN/PROOFS.md`
improves this specifically for pair features: for every four-set `I` and
`a∈I`, a first-layer edge joins `a` to some vertex of `I\{a}`. Thus every
vertex has at most two nonneighbors, and

\[
\delta(G)\ge N-3,\qquad |E(G)|\ge\binom N2-N.
\]

Consequently fixed `C_N` fails from `N=6`, and fixed `C_N^2` fails from
`N=8`, even with unrestricted second-layer weights. This is a corollary of
the already recorded support-claw lemma, not a new general first-width
headline. The general arbitrary-weight first-width result already recorded
as Theorem Q there is stronger than the elementary triple-tie/Mantel count.
