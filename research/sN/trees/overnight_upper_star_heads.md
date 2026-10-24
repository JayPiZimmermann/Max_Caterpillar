# General-head stars: exact exclusions and deletion propagation

24 October 2026. This is a genuine noncanonical-head construction branch,
but the two fixed head sets tested here fail. It does not exclude arbitrary
real heads, other inner graphs, or signed inner coefficients.

For distinct apex `a` and centre `b`, choose numbers `h_i` for every other
label and define

\[
U_{a,b,h}(x)=\sigma\!\left(-x_a+
 \left(1-\sum_{i\ne a,b}h_i\right)x_b+
 \sum_{i\ne a,b}h_i x_i+
 \sum_{i\ne a,b}\sigma(x_i-x_b)\right).
\]

If every `h_i` lies in a fixed finite set `H`, there are at most
`N(N-1)|H|^(N-2)` full descriptions. Permitting each segment to stay free or
be fixed at either endpoint gives at most `N(N-1)(3|H|)^(N-2)` apex-face
descriptions. Base faces have first-hidden-layer support functions. Thus
this is an exponential candidate even after face closure, with the existing
quadratic first hidden layer. Its generic Fourier function is

\[
R_{a,b,h}(\omega)=(-\omega_a)^{N-4}
 \prod_{i\ne a,b}
 \frac1{(\omega_i+h_i\omega_a)(\omega_i+(h_i+1)\omega_a)}.
\]

Full permutation-sum columns depend only on the histogram of head values.
The producer evaluates them by multiplying one short generating polynomial
per leaf, then extracting all histogram coefficients. Assignments are summed
once each; multiplying a histogram column by the factorials of its counts
would instead give the full permutation sum, and does not change its span.

At five inputs the exact results are:

| Head set | Histogram columns | Ordinary / augmented rank | Exact independent kernels |
|---|---:|---:|---:|
| `{-2,-1,0,1}` | 20 | 18 / 19 | 2 |
| `{-2,-1,-1/2,0,1}` | 35 | 29 / 30 | 6 |

The second set adds reciprocal pole ratios: the nonzero endpoint shifts are
`±1/2, ±1, ±2`. It therefore changes the integer-only pole pattern rather
than merely extending its range. Nevertheless it also fails.

The rank lower bounds were computed from exact rational evaluation rows; the
compact checkpoint stores independently checked modular images of those rows,
their frequency points, and the deterministic rational-row hash. The ordinary
rank upper bounds use explicit rational-function null vectors checked by
recursive principal parts, with identity submatrices on their free columns
proving independence. Three entire rows are independently recomputed from
normalized heads using DFS cuts. One representative per histogram is also
checked by direct integration over every braid chamber. These are finite
symbolic certificates, not Lean theorems.

## The exclusions hold at every larger arity

Fix a leaf `v`. The preactivation of its unit in directions `-e_v` and `e_v`
has values `-h_v` and `h_v+1`, respectively. A strictly negative value gives
zero germ; a strictly positive value gives a first-hidden-layer function.
Only a zero preactivation can leave a smaller star:

- If `h_v=0`, the germ at `-e_v` deletes leaf `v` and gives a star with the
  remaining head values.
- If `h_v=-1`, the germ at `e_v` fixes its segment at the nonzero endpoint;
  this cancels the coefficient of `x_v` and again gives the smaller star.

Consequently, modulo the first-hidden-layer span, the signed derivative in
direction `-e_v` is respectively the smaller star, its negative, or zero.
Deleting the centre freezes every segment, and deleting the apex leaves the
inner preactivation; both cases give only first-hidden-layer functions.

The maximum's derivative in this direction is the maximum on the other
labels minus the linear function `x_v`. The standard directional filtration
rule sends the lower-dimensional remainder into the next lower filtration.
Therefore any top-class identity for this fixed head set at arity `N>5`
would descend to such an identity at arity five. The two exact exclusions
above thus rule out both fixed-head-set star constructions, including all
their face functions, for every `N>=5`.

Reopening requires changing the permitted head values or the inner graph
family. The claim does not extend from these two finite sets to all real heads.

Reproduction:

```sh
research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_upper_star_heads.py 5
research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_upper_star_heads.py 5 reciprocal
```

The receipts are `overnight_upper_star_heads_5.json` and
`overnight_upper_star_heads_reciprocal_5.json`; runner logs and exit records
have matching prefixes.
