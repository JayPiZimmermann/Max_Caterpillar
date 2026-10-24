# Canonical cycle units fail at every arity at least seven

25 October 2026. The exact finite gate and the uniform deletion argument are
complete. This is a mathematical proof with exact rational certificates,
not a Lean theorem. It excludes the following unit-length canonical family;
it does not exclude arbitrary heads, signed inner weights, or general graphs.

## Family and conclusion

Choose distinct labels `a,r`, a Hamiltonian cycle on the `N-1` labels other
than the apex `a`, and a state for each edge. The head is `x_r-x_a`. An edge
state is zero, either signed linear difference, or the ReLU of either signed
difference. The unit is the ReLU of the head plus all edge states. Allow every
cycle order, every root, and arbitrary real output coefficients.

For every `N>=7`, the maximum on `N` inputs is not in the span of these
units modulo `L_(N-2)`. In particular there is no exact construction in this
family, even if an arbitrary `L_(N-2)` remainder is supplied for free.
Arbitrary biases in this same finite network model do not help: recession
removes them and preserves an exact homogeneous target.

Only the following top-dimensional states need consideration:

1. A full cycle with every edge a unit-length ReLU, in any orientation.
2. A path on all nonapex labels, with all its edges retained as unit-length
   ReLUs and head `x_r-x_a+s(x_u-x_v)`, where `u,v` are its endpoints and
   `s` is `-1,0,1`.

With at least two nonhinge states there are at most `N-3` free segments.
Their convex hull with the apex has dimension at most `N-2`, so these states
are already in the remainder class.

## Full cycles reduce to the endpoint-shifted paths

Give the cycle a consistent traversal, with vectors `g_1,...,g_(N-1)` whose
sum is zero. If `J` is the set of reversed ReLUs, reversing their segments
translates the head from `h_0` to `h_0-sum_(i in J) g_i`. The cycle zonotope
tiles into the `N-1` zonotopes obtained by omitting one generator. Coning
these tiles to the apex gives the same support-function class modulo
`L_(N-2)`: the intersections of the pyramids have lower dimension.

In the tile omitting generator `g_j`, restore the original orientations of
the remaining generators. The resulting head is exactly

`h_0 - 1[j in J] g_j`.

The endpoints of the omitted edge are the endpoints of the path. Thus this
head has the required endpoint shift, and every full cycle class belongs
to the span of the path family. The reduction is uniform in `N`; it is not
inferred from a sampled relation at seven inputs.

## Exact obstruction at seven inputs

Permutation averaging is necessary because the target is symmetric. The
complete path family has 138 distinct orbit types under `S_7`. The inventory
is independently recovered from raw root, orientation, and endpoint-shift
choices. Reversing the path is its only possible nonidentity graph
automorphism; the stabilizer of each normalized head/edge unit has size one
or two. Dividing its full permutation sum by that stabilizer gives the
distinct-orbit column used throughout the certificate.

For a path unit with normalized head `h` and apex `a`, remove an edge and
let `C` be the component containing its positive endpoint. Put
`q_C=sum_(i in C) omega_i` and `H_C=sum_(i in C) h_i`. Its generic rational
Fourier function, with the common Fourier normalization omitted, is

`(-omega_a)^3 / product_edges
 [(q_C+H_C omega_a)(q_C+(H_C+1)omega_a)]`.

The frequencies satisfy `sum_i omega_i=0`. The corresponding maximum
function is `1/product_i omega_i`. Functions in `L_5` have zero generic
Fourier function, so a rank obstruction here excludes the top-class identity.

The exact certificate has two complementary parts:

- Twelve independent rational-function identities among the 138 orbit
  columns give ordinary rank at most 126. Each vector has its own free
  coordinate equal to one and all other free coordinates zero. Each identity
  is rebuilt from direct edge cuts and all permutations. Exact invariance
  under a seven-cycle and a transposition transports principal-part checks
  across all pole orbits. Every principal part vanishes by recursive exact
  rational arithmetic. The remaining function is a polynomial homogeneous
  of degree `-7`, hence zero. All twelve identities passed, in 939 seconds.
- A 127-row evaluation matrix has augmented rank 127 modulo the prime
  `1000000007`. A separate subset dynamic program regenerated every one of
  its 138 ordinary entries in every row, with the correct stabilizer factor,
  and matched the direct-cut native matrix. Independent scalar Gaussian
  elimination gives ranks `126/127`. Every evaluated denominator is nonzero
  modulo the prime, so the augmented rank over the rationals is at least 127.

Thus the symmetric maximum lies outside the orbit-column span. Symmetrizing
any proposed nonsymmetric representation would contradict this conclusion.
The full cycle reduction then gives the seven-input obstruction for all
five-state cycles as well.

## Propagation to every larger arity

The complete uniform case proof is in
`../trees/overnight_upper_cycle_delete.md`. Opposite-face differences followed
by restriction of the deleted coordinate send the maximum to the maximum on
one fewer label and send `L_(N-2)` into `L_(N-3)`.

For these units, deleting the apex gives only a zonotope support function.
Deleting an internal path vertex freezes two edges and leaves a lower-class
term. Deleting an endpoint leaves either a lower-class term or an
endpoint-shifted path of the same type. Deleting a cycle vertex leaves such
a path with canonical head; when necessary the head root moves to its
neighbor. The case proof retains all roots and both edge orientations.
Independent raw-coordinate controls exhaust these choices at arities four
through nine.

Consequently a representation at any larger arity would descend to the
excluded seven-input representation. This proves the all-arity conclusion.

## Compact replay

The retained proof needs the small orbit inventory, twelve rational vectors,
the 193 KB independently regenerated minor, and exact checker sources. It
does not require the 99 MB expanded unit family or native matrix caches.

```
research/sN/dfs/h5-growth/venv/bin/python research/sN/cycles/overnight_cycle_certificate.py
research/sN/dfs/h5-growth/venv/bin/python research/sN/cycles/overnight_cycle_certificate.py --prove --budget 1800
```

The first command regenerates the complete minor and checks coverage, ranks,
kernel independence, and archived proof integrity. The second also rebuilds
all twelve rational identities and proves them afresh, without reusing a
completed symbolic step. Neither command treats a finite-field rank alone
as an ordinary-rank upper bound.

Separate weighted-cycle and arbitrary-head probes remain modular diagnostics
unless their own exact gates pass. Their conclusions must not be folded into
the theorem above.
