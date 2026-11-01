# Affine closures of sparse cyclic graphs

25 October 2026. Research only. The uniform exponential construction is open.
The five-input top identity below is exact; it is not a width-optimal network
and is not added to the paper. The seven-input test has a modular rank gap.
A separate locality argument now excludes this family for every `N>=31`,
including all larger primes.

## Family and exponential description count

For each omitted apex `a`, take the cycle on the other `N-1` labels in their
induced cyclic order in `Z/NZ`. Choose a nonapex head root and assign each
cycle edge one of five states: omitted, either linear orientation, or either
ReLU orientation. Close the family under the permutations
`i -> u*i+v mod N`, with `gcd(u,N)=1`.

The affine group has `N*phi(N)<=N^2` elements. Thus there are at most
`N^2*(N-1)*phi(N)*5^(N-1) <= N^4*5^(N-1)` descriptions. This includes all
formal edge states. Taking a face of a translated zonotope either fixes a
segment endpoint or retains the segment; consequently the family contains
every apex-containing face of each of its pyramids. Base-only faces have
linear-plus-first-hidden-layer support functions. The reviewed face-closure
lemma therefore converts a top identity into exact dictionary sufficiency
at that arity.

Only the full cycle and states with exactly one nonhinge edge can contribute
to the top quotient. With two nonhinge edges there are at most `N-3` remaining
segments, so the pyramid has dimension at most `N-2`. This justifies using
the existing complete top-state inventory in `cycle_fourier.py`.

Every full cycle zonotope tiles into its `N-1` path zonotopes. Tiling a
reoriented cycle requires the corresponding head shift. The experiment
retains those shifts exactly; the resulting tree atoms need not have
canonical heads. The canonical all-tree lower bound cannot silently be
applied to this cyclic construction model.

## Locality obstructions, including all larger primes

For odd `N`, the only comparisons available anywhere in this family have
label differences coprime to `N`. Indeed, removing the apex from the basic
cycle leaves steps of size one and a single step of size two; multiplication
by a unit preserves this property, and two is a unit for odd `N`.

If odd `N` is composite, choose a prime divisor `p` and the three labels
`0,N/p,2N/p`. None of their pair differences is a unit modulo `N`. Thus the
comparison graph has an independent triple. At a generic point where exactly
those three coordinates tie at the maximum, all available first-hidden-layer
functions are linear in a neighbourhood. The second hidden layer is then a
finite sum of ReLUs of affine functions on that neighbourhood. It cannot
represent a maximum of three independent affine coordinates: a shallow ReLU
kink occupies an entire local hyperplane, whereas the maximum's kink on a
pair-equality hyperplane occupies only the portion where that pair dominates
the third coordinate. Coincident shallow hyperplanes cancel everywhere or
nowhere. Hence this exact family fails at every odd composite arity, regardless
of second width. The first such case is `N=9`, with labels `0,3,6`.

The independent-triple obstruction alone would leave prime padding open:
sufficiency at every prime arity, followed by duplicating inputs at a prime
`N<=p<2N`, would give a `poly(N)*25^N` construction. A stronger locality
argument closes that route for this family. For every `N>=31`, take the five
tied labels `{1,2,4,8,16}`. Their ten positive differences are distinct and
at most 15, so they remain distinct up to sign modulo `N`. A single affine
cycle has only the difference class `+/-u` and at most one gap edge of
difference `+/-2u`. Thus it induces at most two edges on these five labels.
Every unit's local nonlinear germ depends on those two comparisons and one
linear head, so belongs to `L3`; the maximum's four-dimensional simplex
germ does not. This holds even for arbitrary heads and signed inner weights.
See [the independent proof and controls](../trees/overnight_upper_cycle_locality.md).

## Exact five-input control and seven-input discriminator

At five inputs the affine family has 2,080 normalized units in 106 orbits.
The full top-state inventory before affine closure has 1,040 units. The
138-row diagnostic has ordinary and augmented rank 72. Rational reconstruction
gives 39 nonzero orbit coefficients, representing 780 full units. The exact
principal-parts checker verifies the rational Fourier identity. Its status is
`EXACT_TOP_IDENTITY` in `overnight_cycle_affine_5.rank.json`.

Four complete evaluation rows agree between the native evaluator and an
independent NumPy factor evaluator. Four original cyclic/path units are also
checked against direct integration over all braid chambers, independently of
the zonotope tiling. These controls accompany the symbolic identity; they do
not replace it. Face corrections are not counted in the figure 780.

At seven inputs the inventory has 38,304 units in 916 affine orbits, with
58,464 path-atom occurrences after tiling. The 948-row modular diagnostic
has ranks 724/725. No characteristic-zero certificate for this particular
seven-input gap has been produced; the uniform `N>=31` obstruction above
is an independent mathematical argument.

Reproduce the phases with the existing `h5-growth` Python environment:

```sh
research/sN/dfs/h5-growth/venv/bin/python research/sN/cycles/overnight_cycle_affine.py inventory 5
research/sN/dfs/h5-growth/venv/bin/python research/sN/cycles/overnight_cycle_affine.py prepare 5
research/sN/dfs/h5-growth/venv/bin/python research/sN/cycles/overnight_cycle_affine.py generate 5
research/sN/dfs/h5-growth/venv/bin/python research/sN/cycles/overnight_cycle_affine.py solve 5
```

Replace the final argument by seven for the next test. Frequency points and
source hashes are retained. Large native matrices and engine binaries are
reproducible caches. No Lean certificate is claimed.
