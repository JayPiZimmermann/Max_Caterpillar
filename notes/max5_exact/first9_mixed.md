# Max5 first width nine: mixed two-core exclusion

Status: 31 October 2026. **Proved; independent audit PASS.** The mixed
two-core branch is excluded for arbitrary real first directions and
coefficients. The [independent audit](contact_bound_audit.md) covers both
the finite support/sign reduction and the final actual-span argument.
The two-positive-core case remains separate, so this is not by itself
a lower bound five for all physical Max5 networks at first width nine.

## Exact target and physical feature span

The singleton-carrier branch has one positive-row-sum first neuron, one
negative-row-sum first neuron, and seven invariant first neurons. The two
carriers form an opposite pair. The signed-coordinate cost theorem in
`research/sN/frontierN/translation_gate_tools.md`, section 2, reduces a
physical second width four to a residual identity with at most two outer
ReLUs. In the mixed case, absorb the nonzero output magnitudes and write

```
Max5 = ell + R + ReLU(g) - ReLU(h),
R, g, h in V,
V = span{ReLU(a_j.x): j=1,...,7},
a_j.ones = 0.
```

The feature span V is the actual seven-feature span. In particular, it
has **no freely adjoined linear forms**. This distinction is essential
in the final contradiction. All original biases are first removed by
homogeneous recession, without changing either physical width.

The negative-one-core Max4 theorem implies

```
g(-e_i) = 0  for each of the five labels i.
```

Indeed, otherwise the positive outer gate is locally affine at that
four-way top tie. The remaining local identity would have a single
negative outer core or would be shallow; neither represents Max4.

## Why missing target facets constrain the positive core

If the dictionary does not contain the root hyperplane x_i=x_j, the
positive core g vanishes on the whole relatively open top-tie facet

```
F_ij = {x_i=x_j > x_k for every k outside {i,j}}.
```

At a generic point of that facet, every first feature is affine. If g
were nonzero there, the right side would be affine minus a ReLU of an
affine function, hence concave locally. The target has a strict convex
crease. This is impossible. Generic points are dense and g is continuous.

Now consolidate g's nonzero ridge coefficients by hyperplane. A used
normal a intersects the relative interior of F_ij exactly when its
coefficients outside {i,j} have both signs. Because g is identically
zero on F_ij, its restricted ridge must cancel another used normal b.
Consequently

```
b = c*a + d*(e_i-e_j),  c nonzero.
```

For distinct hyperplanes d is nonzero. Thus the outside support and
signs of a,b agree up to a simultaneous reversal, and their union of
supports contains both i and j. These are necessary conditions, even
when the actual magnitudes make the proposed pairing impossible. They
therefore give a safe finite relaxation. Iteratively deleting rows with
an unpartnered required restricted ridge never deletes a genuinely used
ridge.

The support/sign filter also uses the independently established C3/C4
support covers, the local positive-core capacity constraints on three-way
ties, and the fact that g cannot have a linear germ at any four-way tie.
If its germ were linear, its outer ReLU would be shallow, again leaving
a forbidden negative-one-core Max4 identity.

## Exhaustive finite reduction

The checked starting inventory has 431 support-multiset orbits under
input permutations. The local triple-capacity condition leaves 171.
The program enumerates every zero-sum-compatible coefficient sign profile
up to reversal of each normal; no real magnitude is discretized.
There are 6,497 such profiles in that cover.

After the necessary restricted-ridge and local-capacity filters, the
current output has 41 profiles in nine support orbits:

* Three orbits contain only root hyperplanes. They are already excluded
  by the complete-comparison residual theorem, even with arbitrary
  free invariant linear functions.
* Every other orbit consists of six distinct root hyperplanes
  `01,02,03,04,12,34` and one genuinely nonroot hyperplane. The possible
  nonroot supports, up to the displayed symmetries, are
  `012,013,123,0123,1234,01234`.
* For every surviving nonroot sign profile, the only possible nonzero
  ridge coefficients of the positive core g are on the two disjoint
  root hyperplanes `12` and `34`.

These are necessary-condition profiles, not network or fiber counts.
The producer and output are
`research/sN/frontier5/max5_exact_contact_support.py/.json`.

## The final contradiction uses the physical span

In each nonroot survivor, all seven first hyperplanes are distinct.
Therefore a zero consolidated ridge coefficient means that the
corresponding coefficient in the actual feature expression for g is
zero. There are no opposite-row pairs capable of leaving an uncanceled
linear term.

It follows that, in the actual feature orientations,

```
g = u*ReLU(s*(x_1-x_2)) + v*ReLU(t*(x_3-x_4)),
s,t in {+1,-1},
```

after positive rescalings. Evaluate at the negative coordinate vector
for the endpoint on which the first displayed feature is positive. The
second feature is zero there because the two supports are disjoint.
The already proved equation g(-e_i)=0 forces u=0. The analogous
endpoint of the second pair forces v=0. Hence g is identically zero.

This is impossible: the residual would then contain only negative
outer gates. Convexity on each strict first-arrangement cell forces
all ten root hyperplanes into the first dictionary, whereas it has only
seven rows. Equivalently, the positive core must be effective.

Thus the mixed two-core residual is excluded; the independent audit and
exhaustive-subset replay both pass. The all-negative case was already
excluded. The remaining physical (9,4) obligation is the two-positive
residual with arbitrary nonroot invariant features.

## Trust boundary

No Lean files were changed. The final contradiction is a direct linear
independence/evaluation argument. The [independent audit](contact_bound_audit.md)
and exact replay `research/sN/frontier5/max5_exact_contact_support_check.py`
verify the finite reduction. Its adjacent JSON receipt reports
`INDEPENDENT_EXHAUSTIVE_SUBSET_FILTER_PASS`. The checker enumerates all
127 nonempty used-row subsets per profile, independently of the
producer's iterative deletion. The theorem uses neither a coefficient
grid nor an empirical network fit.
