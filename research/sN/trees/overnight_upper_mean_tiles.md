# Individual mean tiles and the five-state circuit enlargement

25 October 2026. The complete widened mean-tile family below fails exactly
at five inputs and therefore at every larger arity. This closes a stronger
candidate than the full positive-circuit units plus their genuine faces.
It does not cover arbitrary real head values, arbitrary mean weights, or
individual tiles from multiple interacting circuits.

Choose an apex `a`, an omitted core label `j`, and a core set `S` containing
`j` and avoiding `a`. Put `mu=mean_S(x)`. For every `i != a,j`, retain the
independent generator `x_i-mu`; its label is a core label when `i in S` and
an outside leaf otherwise. The unit is

\[
\sigma\!\left(\mu-x_a+
 \sum_{i\ne a,j}h_i(x_i-\mu)+
 \sum_{i\ne a,j}\sigma(x_i-\mu)\right).
\]

It is an individual tile of a circuit zonotope, with its own coefficient.
The omitted generator is generally **not** an exposed face operation: removing
one generator from a positive circuit preserves the full base rank. Thus a
failure for the sum over all tiles cannot be used as a failure for this family.

If `G` is the core head set and `H` the outside head set, descriptions number
at most `N(N-1)(|G|+|H|)^(N-2)`. The first hidden layer needs at most `N 2^N`
mean-comparison functions. The generators are independent, so adjoining
genuine faces costs at most another `3^(N-2)` descriptions. These are
unconditional counts, not sufficiency statements.

With `s=|S|` and `a0=omega_a`, its generic Fourier function is

\[
s(-a_0)^{N-4}\prod_{i\ne a,j}\frac1{q_i(q_i+a_0)},\qquad
q_i=\begin{cases}
\omega_i-\omega_j+a_0h_i,&i\in S\setminus\{j\},\\
\omega_i+a_0h_i,&i\notin S\cup\{a\}.
\end{cases}
\]

The factor `s` is the inverse Jacobian of the atom's coordinates. Exact
coordinate-matrix inversion checks this independently on one entire row of
each finite certificate. Full permutation-sum columns are indexed by the
histogram of core/leaf roles and head values; their values are extracted from
a short generating-polynomial product.

| Five-input family | Columns | Ordinary / augmented rank | Exact independent kernels |
|---|---:|---:|---:|
| `G=H={-1,0,1}` | 56 | 44 / 45 | 12 |
| `G={-4,...,3}`, `H={-2,...,1}` | 364 | 262 / 263 | 102 |

Frequency points, deterministic rational-row hashes, and independently checked
modular images are retained in the compact checkpoint. The producers regenerate
the original rational matrices. Every null vector passes the exact
principal-parts verifier, with free-coordinate identity matrices proving
independence. The widened test, including its full-row coordinate check and
all 102 identities, finished in 151 seconds. Receipts are
`overnight_upper_mean_tiles_5.json` and
`overnight_upper_mean_tiles_wide_5.json`.

## Why the wider range covers the original five-state circuit candidate

Start from the attached single-circuit family with all original head values
in `{-1,0,1}`. Independently allow each generator to be absent, linear in
either direction, or a positive-part function in either direction.

Only full retention or deletion of one core generator can contribute to the
full top quotient. Deleting an outside leaf lowers the rank; deleting two
core generators also lowers it. A retained reversed generator is normalized
using `sigma(-g)=sigma(g)-g`, so its head coefficient lies in `{-2,...,1}`.
At a deleted core label `j`, the linear states shift its original head by
`-1,0,1`, giving a coefficient in `{-2,...,2}`. Subtracting that coefficient
from all core heads changes no function and puts every remaining core head
in `{-4,...,3}`. Outside heads stay in `{-2,...,1}`.

The fully retained circuit is tiled by omitting each core generator in turn;
its corresponding differences lie in the same wider range. Therefore the
widened mean-tile dictionary contains the entire top span of the original
five-state circuit candidate. Its obstruction rules out that candidate as
well, including arbitrary generator deletions that are not genuine faces.

## Deletion propagates the obstruction

For an outside leaf `v`, the preactivation values at `-e_v` and `e_v` are
`-h_v` and `h_v+1`. Only heads 0 and -1 leave a smaller mean tile modulo the
first-hidden-layer span; all remaining labels retain their roles and heads.
If `v` belongs to the core, every retained generator is nonzero on that
direction, including when `v` is the omitted label `j`, so both germs are
first-hidden-layer functions. Deleting the apex also has this property.
The target derivative is the smaller maximum minus a linear function.
The directional filtration rule therefore descends any larger-arity top
identity to arity five. Both failures hold for all `N>=5`.

Reproduction:

```sh
research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_upper_mean_tiles.py 5
research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_upper_mean_tiles.py 5 wide
```

These are exact research certificates and mathematical bridges, not Lean
declarations. The remaining cyclic reopening includes individual tiles from
two or more joined circuits, with their own head and orientation freedoms.
