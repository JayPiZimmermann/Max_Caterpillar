# Fixed-size matching witnesses without a square-root loss

This addendum sharpens the fixed-size matching-mixture argument. It is a
mathematical proof, not a Lean certificate. The graph class and locality
bridge are the ones in `overnight_weighted_matching.md`: arbitrary real
heads and inner/output weights are allowed, and a contributing top germ
on a tied set `T` requires `c(G[T]) <= 2`.

Suppose every added graph has a specified matching of size at least `k`,
where `0 <= k <= N/2`. For pseudoforests put `s=2`. More generally, suppose
each graph admits a spanning pseudoforest preserving this matching and
obtained by deleting at most `b` edges; put `s=b+2`. For a parent-oriented
matching edge, the event that its child is selected and parent is absent
starts a distinct component of the induced pseudoforest. The `k` events
use disjoint pairs of labels. Thus `c(G[T]) <= 2` implies at most `s` such
events. The bounded-excess reduction, rather than matching size alone,
is essential for graphs with multiple cycles.

Let

\[
 m=\lfloor N/4\rfloor,\qquad \rho=13/16,\qquad
 D_{k,s}=\sum_{j=0}^{\min(k,s)}\binom kj(3/13)^j.
\]

For `N >= 8` and `s <= N/4`, the proportion of size-`m` tied sets covered
by any added graph is at most

\[
 12\rho^kD_{k,s}.                                      \tag{1}
\]

The constant is absolute, uniformly in `k`, `j`, and `s` in this range.
In particular, for pseudoforests,

\[
 D_{k,2}=1+3k/13+9\binom k2/169.
\]

## The exact counting polynomial

The number of selected subsets with exactly `j` matching events and
total size `m` is

\[
 [z^m]\binom kj z^j(1+z+z^2)^{k-j}(1+z)^{N-2k}.       \tag{2}
\]

For each event edge, the selected child contributes `z`. On a non-event
edge, the allowed choices are neither endpoint, only the parent, and
both endpoints, giving `1+z+z^2`. The remaining labels are independent
singletons. Thus (2) is exact and does not assume that the matching
edges exhaust the graph.

Set `y=1/3`. Normalizing the nonnegative polynomial in (2) at `y`
identifies its weighted coefficient with the point probability of a
sum of `N-2k` Bernoulli variables with probabilities `(3/4,1/4)` and
`k-j` variables with probabilities `(9/13,3/13,1/13)` on `{0,1,2}`,
followed by the deterministic shift `j`.

## A uniform elementary Fourier bound

For either random variable above, its characteristic function `phi`
satisfies, for real `theta`,

\[
 |\phi(\theta)|\le
 \exp\{-c(1-\cos\theta)\},\qquad c=30/169.             \tag{3}
\]

For the Bernoulli variable,
`|phi|^2=1-(3/8)(1-cos theta)`; taking a square root and using
`1-u <= exp(-u)` gives exponent `3/16 >= c`. For the three-point
variable,

\[
 |\phi(\theta)|^2
 =1-\frac{60}{169}(1-\cos\theta)
    -\frac{18}{169}(1-\cos 2\theta)
 \le \exp\{-\tfrac{60}{169}(1-\cos\theta)\}.
\]

There are `L=N-k-j` random factors. Fourier inversion, the triangle
inequality, and `1-cos theta >= 2 theta^2/pi^2` for `|theta| <= pi`
therefore bound every point probability by

\[
 \frac1{2\pi}\int_{-\pi}^{\pi}
       e^{-cL(1-\cos\theta)}\,d\theta
 \le \sqrt{\frac{\pi}{8cL}}.
\]

Since `k <= N/2` and `j <= s <= N/4`, one has `L >= N/4`, so this is
at most `3/sqrt(N)`; indeed `pi/(2c)=169 pi/60 < 9`. This includes
`k=0`, `k=N/2`, and every `j <= min(k,s)` without a degeneracy at an
endpoint.

The polynomial in (2), evaluated at `y`, equals

\[
 (1+y)^N\rho^k\binom kj(3/13)^j.
\]

Summing the coefficient bound over `j <= s` gives

\[
 B_m\le\frac3{\sqrt N}\,y^{-m}(1+y)^N\rho^kD_{k,s},   \tag{4}
\]

where `B_m` counts all size-`m` sets with at most `s` matching events.

For `X ~ Bin(N,1/4)`, the integer `m=floor(N/4)` is a mode. Its mass
`P_m` is at least `1/(4 sqrt(N))`: Chebyshev gives probability at least
`3/4` in `|X-N/4| < 2 sqrt(3N/16)`, an interval containing at most
`sqrt(3N)+1 <= 3 sqrt(N)` integers, and the mode has the largest mass.
Since `P_m=binom(N,m)y^m/(1+y)^N`, division of (4) proves (1).

## Mixtures with the original dictionaries

Use the previously proved normalized size-`m` capacity `6^m` for each
function in either original dictionary. Its proportion of tied sets
is at most

\[
 \frac{6^m}{\binom Nm}
 =\frac{(3/4)^N2^m}{P_m}
 \le 4\sqrt N\,\rho^{N/2}(162/169)^{N/4}.
\]

The last exponential factor absorbs `sqrt(N)` uniformly. In fact,

\[
4\sqrt N(162/169)^{N/4}
 \le4\sqrt N e^{-7N/676}
 \le4\sqrt{338/(7e)}<20.
\]

Because `k <= N/2`, this original-dictionary capacity is at most
`20 rho^k`, while (1) is at most `20 rho^k D_{k,s}`. Therefore, if `Z`
counts all nonfree functions in the mixture, covering every size-`m`
tie gives the explicit bound

\[
 \boxed{\displaystyle
 Z\ge\frac{(16/13)^k}{20D_{k,s}}.}                    \tag{5}
\]

Here `N >= 8`, `s <= N/4`, and `m` must reach the applicable locality
separator threshold. These thresholds are `3` without an additional
free class, `5` with all canonical rooted/oriented star face functions
free, and `7` with all canonical rooted/oriented tree face functions of
matching number at most two free. The existing propagated separator
forces some counted term to cover each size-`m` tie; the counting above
is unchanged. Arbitrary real-head or real-weight stars are not members
of either free class. Terms in an overlap are assigned to the free
class before counting `Z`.

For pseudoforests, (5) yields

\[
 Z=\Omega\!\left((16/13)^k/(1+k^2)\right),
\]

with no additional factor depending on `N`. The exact binomial-mode
argument using `P_m >= 1/(N+1)` remains a simpler proof with a weaker
polynomial denominator.

Finally, if `k=Omega(N)` and `b=o(N)`, then `s=b+2=o(N)` eventually
satisfies `s <= N/4`. Moreover
`log D_{k,s}=O(s log(e k/s)+log(s+1))=o(N)` (with the finite cases
interpreted directly). Hence (5) gives

\[
 Z\ge (16/13)^k\exp\{-o(N)\}.
\]

This last statement retains the specified excess bound and is not an
unrestricted all-tree exponential theorem: small-matching trees remain
outside its hypothesis.
