# Positive-circuit cores with attached leaves

24 October 2026. This is a genuinely cyclic, exponential-size construction
candidate with an exponential first hidden layer. The three complete fixed-head
families below fail exactly, and deletion propagates their failure to all larger
arities. Arbitrary heads, weighted circuit generators, and multiple circuits
remain outside these exclusions.

Choose an apex `a`, a nonempty core `S` among the other labels, and
`mu_S = sum_(i in S) x_i / |S|`. Every nonapex label supplies the generator
`g_i(x)=x_i-mu_S`. The core generators have the single positive dependence
`sum_(i in S) g_i=0`; generators outside the core are independent leaves.
The full unit is

\[
U_{a,S,h}(x)=\sigma\!\left(\mu_S-x_a+
 \sum_{i\ne a}h_i(x_i-\mu_S)+
 \sum_{i\ne a}\sigma(x_i-\mu_S)\right).
\]

For a fixed head set of size `K`, full descriptions number at most
`N(2K)^(N-1)`. Three states per generator—free, fixed at zero, fixed at its
other endpoint—give an exponential face-description bound
`N(6K)^(N-1)`. All first-hidden-layer functions have the form
`sigma(x_i-mean_S(x))`, so at most `N 2^N` nonlinear features are needed,
in addition to linear channels. These are counts only.

Adding a common constant to all core head values changes no function.
For the integer range `H={-1,0,1}`, normalize the minimum core coefficient
to zero; its core coefficients then lie in `{0,1,2}`. A permutation-sum column
is specified by core and leaf head histograms. At arity `N`, the number of
such columns is `binom(N+3,5)`; at five inputs it is 56.

## Exact Fourier formula

Put `s=|S|`, `a0=omega_a`. The positive-circuit projection of the cube is
tiled by the `s` zonotopes obtained by omitting one core generator. The
tiling has no translations: subtracting the least core cube coordinate
reaches a zero-coordinate facet because the core generators sum to zero.
The outside leaf coordinates are unchanged. The tiles meet in lower
dimensions, and coning from the common apex with the common head preserves
this top-class valuation identity.

For the tile omitting `j in S`, use coordinates

\[
t=\mu_S-x_a,\qquad y_i=x_i-\mu_S\ (i\in S\setminus\{j\}),
\qquad z_l=x_l-\mu_S\ (l\notin S\cup\{a\}).
\]

Their inverse has absolute determinant `s`. The Fourier covector components
are `-a0`, `omega_i-omega_j`, and `omega_l`. After absorbing the head into
the first coordinate, define

\[
q_i=\omega_i-\omega_j+a_0(h_i-h_j)\quad(i\in S\setminus\{j\}),
\qquad q_l=\omega_l+a_0h_l\quad(l\notin S\cup\{a\}).
\]

The full unit's generic Fourier function, with the common Fourier factor
omitted, is therefore

\[
R_{a,S,h}=s(-a_0)^{N-4}
 \sum_{j\in S}\prod_{i\ne a,j}\frac1{q_i(q_i+a_0)}.
\]

For a two-label core this reduces to the midpoint-centre formula; for a
singleton core it reduces to the ordinary general-head star. An independent
review by the parent derived the Jacobian and the unshifted tiling separately.
The finite checker also inverts each full atom's coordinate matrix and checks
its determinant, dual covector, and Fourier term on an entire evaluation row.

## Complete finite exclusions

All rows were computed as exact rational evaluations. Compact receipts retain
their frequency points, deterministic rational-row hashes, and independently
checked modular images. Null vectors are rational-function
identities verified by recursive principal parts; their free-column identity
submatrix proves independence. Thus the ordinary rank upper bound and the
augmented evaluation rank lower bound give a characteristic-zero obstruction.

| Five-input family | Columns | Ordinary / augmented rank | Independent exact kernels |
|---|---:|---:|---:|
| Core-normalized `H={-1,0,1}` | 56 | 54 / 55 | 2 |
| `H={-2,-1,0,1}` | 120 | 118 / 119 | 2 |
| First family union core steps `1/2` | 77 | 75 / 76 | 2 |

The third row genuinely enlarges the first: it permits normalized core head
coefficients `{0,1/2,1}` while keeping outside leaf heads `{-1,0,1}`, then
takes the union and removes identical columns. The two separate families'
failure is not used as a substitute for testing their union.

Receipts are `overnight_upper_circuit_5_h3.json`,
`overnight_upper_circuit_5_h4.json`, and
`overnight_upper_circuit_5_h3_half_union.json`. The corresponding runner logs
and exit records document the bounded commands. These are finite symbolic
certificates and mathematical arguments; no Lean theorem is claimed.

## Why the failures propagate

Delete one label using the signed directional derivative at `-e_v`.
If `v` lies outside the core and is not the apex, only its own generator
changes along this direction. The two preactivation values are `-h_v` and
`h_v+1`; modulo the first-hidden-layer span, the only surviving smaller unit
occurs for `h_v=0` or `h_v=-1`, with sign respectively positive or negative.
It has the same core and all the same remaining head values.

If `v` belongs to a core of size at least two, every generator is nonzero
in this direction, so all inner functions freeze to linear functions and
both germs belong to the first-hidden-layer span. A singleton core is the
ordinary star centre and has the same conclusion. Deleting the apex also
leaves only the first-hidden-layer preactivation. Hence this deletion maps
each tested family into the smaller same family plus first-hidden-layer
functions. The target becomes the maximum on the other labels minus a
linear function. Together with the directional filtration rule, a top-class
representation at any `N>5` would descend to one at five inputs. The exact
obstructions therefore exclude all three families, including their face
closures, for every `N>=5`.

## The tempting mean-only circuit is even weaker

If the core is always the entire nonapex set, every coordinate deletion gives
only first-hidden-layer germs. Therefore this family cannot represent the
top class of the maximum for any `N>=4`, even with arbitrary heads and fixed
inner coefficients. Proper-subset units without attached outside leaves have
lower dimension and do not change the top span. Proper faces do not change
it either. The three-input boundary works because the mean of two coordinates
plus their positive deviations is their maximum. This explains why attached
outside leaves were essential to make the test above discriminating.

Reproduction:

```sh
research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_upper_circuit.py 5 3
research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_upper_circuit.py 5 4
research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_upper_circuit.py 5 3 half_union
```
