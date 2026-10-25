# A second minimal-first-width construction family: C5 plus two anchors

The live construction target is `(9,6)`. No such network is claimed here.
This branch explores the still possible first-layer row-sum split `(2,2,5)`;
it does not assume that every width-nine first hidden layer is the P4 star
layer already studied.

Fix the five undirected cycle edges

```
{0,1}, {1,2}, {2,3}, {3,4}, {4,0}
```

and choose an orientation `(i,j)` for each, meaning the feature
`σ(x_i-x_j)`. Add the four coordinate-anchor features

```
σ(x0), σ(-x0), σ(x2), σ(-x2).
```

There are 32 orientations. Exactly six pass the following complete feature
factorization check:

* the edges incident to vertices3 and4 point `3→2` and `4→0`;
* vertex1 has at least one outgoing edge to an anchor, `1→0` or `1→2`;
* the edge between3 and4 may point either way.

## Twenty-six direct impossibility witnesses

For every other orientation, the certificate provides two rational inputs
with identical values of all nine physical first-layer features but different
maxima. No function of these nine features can recover the maximum. In
particular no finite second hidden layer works for that first layer. The
independent verifier only evaluates the explicit feature values; it does
not import the row-span producer or trust a numerical rank calculation.
Arbitrary biases in a finite ReLU network cannot evade this obstruction:
the recession limit of an exact homogeneous maximum representation has
the same matrices and zero biases.

The original row-span gate uses all 30 acyclic comparison cells. The direct
witness construction subtracts a common coordinate shift from its kernel
direction, leaving both anchor coordinates fixed. Thus the final witness
is an obstruction to the actual nine physical features, not merely a
translation-invariant tail approximation.

## The surviving orientations factor globally

Write `l=x2-x0`. The invariant core W is the span of the five oriented
comparison functions and the genuine linear function l. Let

```
z3 = l + σ(x3-x2),
z4 = σ(x4-x0),
z1 = σ(x1-x0)                    if the edge1→0 is available,
     l + σ(x1-x2)                otherwise.
```

Then, for every input,

```
max(x0,x1,x2,x3,x4)-x0 = max(z1,z3,z4).
```

Indeed z4 already dominates0, z3 already dominates l, and each remaining
term replaces one coordinate by its maximum with an anchor that is already
included. This gives a continuous factorization through W. It does not
by itself give a finite one-hidden-layer ReLU completion on the feature
image; that is the construction question being tested.

Swapping labels0 and2 and simultaneously3 and4 pairs the six orientations
into three symmetry classes. The first joint search uses both outgoing
edges from1, the orientation3→4, and the mandatory anchor edges.

## Four-free-term core and physical compilation

A core identity

```
max5-x0 = R + sum_(k=1)^4 d_k σ(g_k),   R,g_k in W,
```

would give an actual `(9,6)` network: two opposite second-layer neurons
encode `x0+R`, and four more encode the displayed core terms. If a core
coefficient on l is b, its physical anchor coefficients are
`(-b,b,b,-b)` in the order `(σx0,σ(-x0),σx2,σ(-x2))`. For the head `x0+R`
they are `(1-b,-1+b,b,-b)`.

This is a constructive upper-bound compilation. **No lower-bound equality
`h2_min=k_W+2` is asserted for four anchors.** The previous two-carrier
lower bridge cannot be copied here: the positive and negative translation
tails can have different invariant linear intercepts.

## Independent global verification

`overnight_fixed_anchor_verify.py` reads the actual physical network, checks
all anchor-pair coefficients, reconstructs the input gradients on all120
braid cones, cancels every interior hyperplane, and compares the remaining
linear gradient with the maximizing coordinate. Continuity covers the
boundaries. It accepts any number of full coordinate-anchor pairs and
imports no SMT solver, model producer, or numerical package.

It passes the existing `(10,6)` and `(9,14)` networks. A further exact control
moves nonzero antisymmetric comparison coefficients in the `(10,6)` network
into a second coordinate-anchor pair, using
`σ(x2-x1)-σ(x1-x2)=x2-x1`; the resulting physical `(12,6)` control passes.
Two deliberate mutations are rejected. This control is a verifier test,
not a new width construction result.

The orientation certificate and checker are
`overnight_fixed_cycle9_witnesses.json` and
`overnight_fixed_cycle9_witnesses_verify.py`. All32 cases pass the independent
replay. Joint construction runs have separate files and remain diagnostic
until a rational physical network passes the global verifier.
