# Five open patches rule out eight natural five-term completion formulas

These are exact failures of selected construction routes. They do not
exclude an arbitrary five-term formula in W7. The target remains a
matching `(9,7)` construction for the now certified lower bound.

Use the feature order `(a,b,p,c,d,q,r)` with

```
a=σ(u), b=σ(v), p=σ(v-u), c=σ(s), d=σ(t),
q=σ(s-t), r=σ(v-t).
```

We considered three positive carriers P, followed by two arbitrary
negative outer ReLUs and an arbitrary W7 remainder. In each of the eight
cases below, write

```
P = σ(a-c+P13*p)
  + σ(a-d+P14*p+Q14*q+R14*r)
  + σ(q-r).
```

The checked parameter choices `(P13,P14,Q14,R14)` are

```
(0,0, 0,-1), (0,0,-1,-1), (0,1, 0, 0), (0,1, 0,-1),
(1,0, 0, 0), (1,0, 0,-1), (1,0,-1,-1), (1,1, 0, 0).
```

For each, **there are no arbitrary real R,h1,h2 in W7** satisfying

```
max(0,u,v,s,t) = P + R - σ(h1) - σ(h2).
```

This includes the particularly simple candidate with carriers
`a-c, a+p-d, q-r`. The prospective correction is convex on each first-layer
cell and has at most one internal hyperplane there, but that local fact is
not sufficient for two globally available preactivations. A direct
cell-assignment DFS reached its declared node budget and was stopped. The
following smaller geometric obstruction resolves it exactly.

## The five-patch argument

Set `G=P-max(0,u,v,s,t)`. If the formula existed, then G would be a linear
remainder plus two positive outer ReLUs. As a function of the seven features
z, this is

```
R0(z)+σ(h1(z))+σ(h2(z))
  = max{R0, R0+h1, R0+h2, R0+h1+h2}(z).
```

Thus four feature-linear planes would suffice. Equivalently these planes
are the vertices of a translated parallelogram; even the parallelogram
condition is unnecessary for the obstruction below.

For each selected carrier choice, the certificate gives five small integer
input points. The five coordinates are distinct, so the first hidden layer
has a fixed linear map on an open neighborhood of each point. Every
positive-carrier preactivation is either strictly nonzero or identically
zero on that first-layer cell. The target maximum has a unique maximizing
coordinate. Hence G is linear on an open neighborhood of each point.

Write A_i for the active first-layer matrix and g_i for G's input gradient
on the ith neighborhood. A feature-linear plane with coefficient vector v
can agree with G on an open subset of that neighborhood only if

```
A_i^T v = g_i.
```

The checker verifies that each individual system is consistent, but every
pair of these five systems is inconsistent over the rationals, hence over
the reals. One plane therefore cannot serve two of the five neighborhoods.
At least five planes are needed, contradicting the four-plane expression.

The passage from a maximum of four planes to one agreeing plane is exact:
on an open neighborhood where G is linear, the four equality sets cover
the neighborhood. A finite union of proper linear hyperplanes cannot cover
an open set. At least one plane agrees there identically. Repeating this
on five neighborhoods and applying pigeonhole gives the contradiction.

## Independent verification and scope

The standalone checker hardcodes the seven first-layer directions. It
reads only the small five-point certificate, recomputes the actual active
matrices and gradients of P and the maximum, checks the smoothness
conditions, and verifies all eighty pairwise linear inconsistencies with
an independent Gaussian-elimination implementation. It imports no search
code, network producer, fan generator, or numerical solver.

```
python3 research/sN/best5/overnight_fixed_p4_fivepatch_verify.py
```

All eight certificates passed. The required input points have integer
coordinates of magnitude at most five. These are certificates based on
open neighborhoods, not assertions inferred from finitely sampled values.

Other signs, different positive carriers, changed carrier amplitudes,
four-positive/one-negative arrangements, and coordinated changes to all
five preactivations remain open. No further selected-coefficient sweep is
justified by these failures alone. A useful reopening condition is a
continuous carrier choice whose complete correction geometry admits four
compatible feature planes and then the parallelogram relation.
