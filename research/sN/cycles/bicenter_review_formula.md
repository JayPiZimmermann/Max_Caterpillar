# Independent review of the bicentre upper-construction candidate

24 October 2026. This is an exploratory mathematical reduction with exact
finite controls. It does **not** establish a uniform exponential construction,
and is not part of the Lean verification receipt.

## Model and conditional size bound

Choose an apex label `a`, two different nonapex centre labels `c,d`, and a
nonapex root `r`. The underlying inner graph is the complete bipartite graph
between `{c,d}` and the other `N−3` nonapex labels, optionally including `{c,d}`.
Every present edge may have either orientation. The full unit is

\[
U(x)=\sigma\!\left(x_r-x_a+
       \sum_{(u,v)\in E}\sigma(x_u-x_v)\right).
\]

The larger formal face-state family allows each potential edge to be omitted,
linear in either orientation, or a hinge in either orientation. It has at most

\[
N(N-1)\binom{N-1}{2}\,5^{2N-5}
\]

descriptions. This is polynomial times a fixed exponential, with exponential
base 25. Duplicate descriptions only reduce the count. All its coordinate
channels and functions `σ(x_i−x_j)` fit in the existing quadratic first hidden
layer.

For a fixed full unit, write its polytope as the convex hull of the origin and
a translated zonotope. Every exposed face lying entirely in the zonotope has
support function equal to a linear function plus a sum of some of the original
functions `σ(x_i−x_j)`. Every face containing both apex and base points has,
for each original segment, either the initial endpoint, the final endpoint,
or the entire segment. Its support function is therefore another unit in the
formal face-state family. The same holds after taking further faces.

Consequently, a **uniform top-class identity** for the full units would imply
an exact exponential construction by the existing face-reduction theorem.
The count alone proves no span identity. Nor does failure for the full units
exclude the larger formal face-state family: independently assigned edge states
can describe new full-dimensional pyramids which are not actual faces of any
full unit.

## A conditional-leaf Fourier formula

The formula applies more generally to an integer or rational head
`h·x`, where `h_a=−1` and `sum h=0`. Keep every edge of the complete bipartite
graph and optionally the centre edge. Let `L` be the leaf set, so `|L|=N−3`.
For frequencies with `sum ω=0`, define

\[
 A=\omega_a,\qquad
 \kappa_v=h_v+\operatorname{outdeg}_E(v),\qquad
 B_l=\omega_l+A(\kappa_l-1),
\]
\[
 D_0=\omega_d+A\kappa_d,\qquad
 D_1=-\omega_c-A\kappa_c.
\]

Here an edge `(u,v)` contributes `σ(x_u−x_v)`, so `u` is its source. Omitting
the common Fourier factor `i^(−N)`, the generic Fourier rational function is

\[
\boxed{
R_U(\omega)=(-A)^{N-5}
\sum_{S\subseteq L}
\frac{
 (D_0+\sum_{l\in S}B_l)^{-1}
 -(D_1-\sum_{l\in S}B_l)^{-1}
}{
 \displaystyle\prod_{l\in L}B_l
 \prod_{l\in S}(B_l+A)
 \prod_{l\in L\setminus S}(B_l-A)
}.}
\]

Thus the calculation uses `2^(N−3)` summands instead of `N!` braid chambers.
As usual, the displayed expression is initially evaluated away from its poles;
some partial-fraction poles can cancel in the final rational function.

The complete orientation information enters only through `κ`. This is also
immediate from

\[
\sigma(x_u-x_v)=\sigma(x_v-x_u)+(x_u-x_v).
\]

### Derivation

Fix the translation gauge `x_c=0`, put `x_d=z`, and denote a leaf coordinate
by `t`. Integrating the apex coordinate first gives

\[
\int e^{-iAx_a}\sigma(F-x_a)\,dx_a
   =(iA)^{-2}e^{-iAF},
\]

in the generic Fourier rational calculation. Absorb the head in the remaining
frequencies by setting `Ω_v=ω_v+A h_v`.

For a leaf, let `p=1` mean the edge points from the leaf to `c`, and let `q=1`
mean it points from the leaf to `d`. Its three interval slopes, in increasing
order of `t`, are `B−A,B,B+A`, where `B=Ω_l+A(p+q−1)`. At either breakpoint the
integral has a coefficient equal to the difference of inverse adjacent slopes.
The two coefficients are

\[
 C_-=-\frac{A}{B(B-A)},\qquad
 C_+=-\frac{A}{B(B+A)}.
\]

For `z>0`, the accompanying exponential frequencies in `z` are respectively
`A(1−q)` and `Ω_l+Ap`. For `z<0`, they are respectively
`Ω_l+A(p−1)` and `−Aq`. A factor `i^(−1)` is common to the leaf integral.

Choose the second coefficient precisely for leaves in `S`. On the positive
half-line, the remaining `z` frequency is

\[
\Omega_d+A\mathbf 1_{d\to c}
+\sum_{l\notin S}A(1-q_l)
+\sum_{l\in S}(\Omega_l+Ap_l)
=D_0+\sum_{l\in S}B_l.
\]

On the negative half-line it is

\[
\Omega_d-A\mathbf 1_{c\to d}
+\sum_{l\notin S}(\Omega_l+A(p_l-1))
-\sum_{l\in S}Aq_l
=D_1-\sum_{l\in S}B_l.
\]

Integrating the positive half-line gives `i^(−1)/D`, and the negative half-line
gives `−i^(−1)/D`. The powers of `i` total `i^(−N)`. The coefficient numerator is
`(−A)^(N−3)/A²=(−A)^(N−5)`, giving the formula.

## Formal face states and controls

`bicenter_review_fourier.py` implements the displayed formula in `full_value`.
It also implements `subgraph_value`, which independently retains the interval
breakpoints present at each leaf and so handles omitted and linear edge states.
Linear states are absorbed in the head. An isolated leaf makes the generic
Fourier transform zero; one retained leaf edge gives one breakpoint, and two
retained edges give the two breakpoints above. A missing centre connection or
other disconnected retained graph is handled by cancellation in the remaining
half-line integrals.

The command

```sh
python3 research/sN/cycles/bicenter_review_fourier.py control
```

checks 36 exact rational examples at `N=4,5,6` against the independently
implemented all-braid-chamber integration in `cycle_fourier.chamber_value`.
The examples include both orientations, present and absent centre edges,
general heads, all five formal edge states, and vanishing low-dimensional
cases. All checks pass. These finite controls catch normalization and sign
errors; they do not replace the uniform derivation or establish a spanning
identity.

`full_mod_batch` evaluates the same formula on a NumPy array of frequency
vectors using a modular inverse table. It rejects a singular input explicitly.
A modular span failure is only diagnostic unless an exact ordinary-rank upper
bound or rational separator accompanies it.

The command `bicenter_review_fourier.py control-mod`, using the research Python
environment, additionally checks 190 modular batch outputs against the exact
rational formula at `N=4,5,6,7`. One singular batch is explicitly rejected.

## Full-unit obstruction and the next boundary

The full-leaf-hinge candidate already fails at five inputs, even modulo the
lower-dimensional space. This statement includes all roots, every orientation,
and all five states for the centre edge. It does not include independently
chosen missing or linear states for the leaf edges.

At five inputs the complete symmetric family has 38 orbit representatives.
`bicenter_review_top5_certificate.py` independently enumerates all labelled
root/orientation choices, reduces by the centre and leaf automorphisms, and
checks seven independent exact identities on all 120 sorted-chamber profiles.
Consequently the ordinary functional rank, and hence the top-class rank, is at
most 31. A 32-by-32 augmented Fourier minor has determinant 527233 modulo
1000003, so its rational rank is at least 32. The two bounds give an exact
obstruction. The finite checker is

```sh
research/sN/dfs/h5-growth/venv/bin/python \
  research/sN/cycles/bicenter_review_top5_certificate.py check
```

The complete checks include the family enumeration, exact kernel identities,
their independence, primality of 1000003, regeneration of the selected Fourier
minor, and a separate elementary modular determinant calculation. The trust
boundary remains ordinary Python/NumPy arithmetic and the proved Fourier and
symmetrization reductions; there is no Lean claim.

At seven inputs there are 120 orbit columns. The sampled augmented matrix has
rank 121 modulo 1000003. Its ordinary rank is at most 120 simply by the number
of columns, so this also proves exact exclusion. The 121-by-121 minor recorded
in `bicenter_review_top7_minor.json` has determinant 92268 modulo 1000003.
Its data and reproducible producer are `bicenter_review_top_7.json` and
`bicenter_review_top_probe.py`. At six inputs the sampled ranks are 71/72 on
72 orbit columns, which alone is only diagnostic.

These rank arguments concern symmetric orbit sums because the family is closed
under all label permutations and the target is symmetric. Any representation
can therefore be averaged over the permutation group. Frequency tuples stored
modulo the prime lift to rational frequency tuples of exact sum zero by
replacing the final coordinate with the negative sum of the others. Every
denominator used in the selected modular minors is nonzero, so specialization
gives a valid rational-rank lower bound.

The larger formal leaf-face-state family remains open. In particular it already
contains every canonical tree unit at five inputs, so the full-unit obstruction
must not be reported as an obstruction to that larger family.
