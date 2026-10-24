# Cyclic units: exact reductions and obstructions

Model: linear channels and first-hidden-layer functions sigma(x_i-x_j);
arbitrary real output coefficients. The fixed-cycle experiment below uses
positive inner coefficients, canonical head x_r-x_a, and a cycle on every
label except the apex a. A directed pair (u,v) denotes sigma(x_u-x_v).

## General-head tree formula

Let h_a=-1, sum h_i=0, and let E be an oriented spanning tree on the other
N-1 labels. For U=sigma(h.x+sum_E sigma(x_u-x_v)), use coordinates
`t=h.x`, `s_e=x_u-x_v` on the quotient by common translations. They form a
unimodular coordinate system: fixing x_a=0, the tree differences determine
all nonapex coordinates up to a common constant, and sum_(i!=a)h_i=1 fixes
that constant with coefficient one.

Let sum omega_i=0 and a0=omega_a. For edge e=(u,v), let C_e be the component
containing u after removing e, q_e=sum_(i in C_e)omega_i, and H_e=sum_(i in C_e)h_i.
The Fourier coordinates satisfy

    omega_t=-a0,  omega_(s_e)=q_e+a0 H_e.

Indeed sum the covector equation omega=omega_t h+sum_e omega_(s_e)(e_u-e_v)
over C_e. Integrating first in t and then independently on s_e>=0 and s_e<=0
therefore gives the generic rational Fourier function, with the common factor
i^(-N) omitted,

    R_U=(-a0)^(N-4) / product_e ((q_e+a0 H_e)(q_e+a0(H_e+1))).

This specializes to the earlier canonical-head formula. The exact controls in
`controls.json` compare this expression with a separately implemented integral
over all braid chambers, for N=4,5 and arbitrary small integer heads. These are
checks of the implementation; the coordinate-change argument proves the formula.

For the independent chamber calculation, on x_(pi1)>=...>=x_(piN) let A_j be
the cumulative frozen preactivation coefficient and O_j the cumulative Fourier
frequency, for j=1,...,d=N-1. The chamber contribution is

    sum_(j:A_j>0) A_j^d / (O_j^2 product_(k!=j)(A_j O_k-A_k O_j)).

This follows by integrating the positive part of a linear combination of
independent exponential variables and expanding its Laplace transform into
partial fractions. We avoid removable coincident poles in point controls.

## A cycle is a sum of translated tree atoms in the top quotient

For a consistently directed cycle g_1,...,g_m, sum g_j=0 and this is the
only relation. Project the cube [0,1]^m along the all-ones vector. Subtracting
the minimum coordinate gives a representative on one of the facets t_j=0.
Consequently its zonotope is tiled by the m zonotopes obtained by omitting
one generator. The interiors are disjoint because, generically, the minimum
coordinate is unique.

All these translated zonotopes lie in x_a=-1. Coning to the apex0 preserves
the subdivision, and intersections have dimension below N-1. The support-
function valuation thus gives, modulo L_(N-2), the sum of the corresponding
m tree pyramids. Reversing g_j uses sigma(-g_j.x)=sigma(g_j.x)-g_j.x, shifting
the common head by -g_j. These heads need not be canonical root differences.

Among all face states on the cycle, only full retention or one fixed edge can
contribute in dimension N-1. With at least two fixed/omitted edges, at most
N-3 segment generators remain, giving pyramid dimension at most N-2. A fixed
edge contributes either0,+g_j,or-g_j to the head. These are exactly the cases
included by `cycle_fourier.family`; permitting infeasible combinations only
enlarges the family, so a negative result remains valid for genuine faces.

## Exact failure at five inputs

At N=5 there are1040 normalized functions, grouped into106 D5 orbit sums.
If any combination represented the symmetric target modulo L3, averaging over
D5 would produce such an orbit-sum representation. The checker recomputes every
finite-field row from cuts, proves32 independent rational-function identities
using exact recursive principal parts, and verifies their independence by a
nonzero integer determinant. Thus the rational-function column rank is<=74.
The target-augmented matrix has rank75 modulo1000003, so its characteristic-
zero rank is>=75. The target is outside the span over R as well: the relation
vectors and all rational evaluation rows are rational and rank is unchanged
under scalar extension. Receipt: `cycle_obstruction_5.json`.

This refutes the fixed-cycle family including all its face functions. It does
not refute arbitrary graphs with cycles, different cyclic orders in different
units, cycles through the apex, or signed inner coefficients.

## Why one globally sparse comparison graph cannot scale

There is a stronger general obstruction than the preceding particular family.
Suppose all first-hidden-layer nonlinear features are pair differences on a
single graph G, with arbitrary linear channels. The existing four-label claw
lemma (`../frontierN/PROOFS.md`, C4') implies that every vertex a has a neighbour
in every three-set Y avoiding a. Thus every vertex has at most two nonneighbors:

    delta(G)>=N-3,  |E(G)|>=binom(N,2)-N.

For completeness, if a has three nonneighbors Y, localize at a generic point
where {a} union Y tie at the top. Every retained first-layer nonlinearity is
independent of x_a. The resulting identity has the form

    max(x_a,max_Y x)=L(x)+S(x_Y)+sum_k d_k sigma(m_k x_a+g_k(x_Y)),

where S and g_k are one-hidden-layer functions. For each fixed x_Y, compare
slope jumps as x_a varies, then their first moments. This expresses max_Y as
a linear combination of the g_k and a linear function, which would be a one-
hidden-layer representation of max_3. That is impossible: its odd part is
max_3+min_3, which is not linear, whereas the odd part of any homogeneous
one-hidden-layer function is linear.

Hence a single global C_N fails for N>=6; its square C_N^2 fails for N>=8.
This does not exclude using a different cyclic graph in each second-layer
unit: their union may supply all pair comparisons. The present paper already
uses a quadratic first hidden layer, compatible with this necessary condition.

## A larger exponential-size candidate that permits cycles

Fix one cyclic order of the labels. For each apex a, take all noncrossing
simple graphs on the other n=N-1 labels, arbitrary edge orientations, and
canonical heads x_r-x_a. Include every face function. This permits cycles
and contains the noncrossing-tree candidate; the apex-to-root head is not
required to be noncrossing.

Every such graph extends to a triangulation of the n-gon. There are at most
4^n triangulations, each with 2n-3 edges, including polygon boundary edges.
At each edge permit five states: absent, linear in either orientation, or
sigma in either orientation. For a fixed triangulation these states include
all oriented subgraphs and all their face functions (possibly extra infeasible
face states, which only enlarge the dictionary). Therefore the number of
normalized descriptions is at most

    N(N-1) 4^n 5^(2n-3) <= N^2 100^N.

Base faces are zonotopes and belong to the auxiliary span; faces containing
the apex have the indicated fixed/retained edge states. This is an unconditional
count of a candidate dictionary, NOT a proof that it represents the maximum.

The precise remaining upper lemma is, for every N,

    h_simplex in span{h_Q : full noncrossing graph pyramids Q} + L_(N-2).

The general face-closure lemma already proved in `../trees/all_tree_review.md`
then gives an exact expansion by this dictionary and linear functions, hence
second width at most N^2 100^N+2 and the existing quadratic first hidden layer.
Thus cycles can be allowed while keeping the candidate family exponential.
Neither the fixed-cycle obstruction nor the NC8 caterpillar obstruction
settles this larger sufficiency question. The missing step is the uniform
identity, not the number of available graphs or the face corrections.

A relevant finite example is Myrisiotis's [hexagon identity](https://arxiv.org/html/2610.04256),
which uses maxima on the six polygon edges and six short diagonals, with signed
linear combinations inside the second hidden layer. That is a broader atom
model than the positive-inner-coefficient cycle test above. The author's
suggested heptagon analogue remains compatible with the graph condition; a
uniform analogue using only edges and short diagonals fails the necessary
degree condition from eight inputs onward. This last obstruction follows from
the repository's claw lemma, not from a claim made in that paper.
