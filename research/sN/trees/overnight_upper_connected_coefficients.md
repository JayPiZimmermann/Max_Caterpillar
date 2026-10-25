# A coefficient sharpening of the bounded-degree lower bound

This is an independent mathematical addendum to the connected-set
argument. For every fixed maximum degree `Delta >= 3`, it removes the
polynomial loss from the pure bounded-degree bound:

\[
|K|=\Omega_\Delta\!\left((1+y_\Delta)^N\right),\qquad
y_\Delta=\frac{(\Delta-2)^{\Delta-2}}{(\Delta-1)^{\Delta-1}}.
\]

It uses the existing locality statement: at an `m`-label top tie, with
`m >= 3`, at least one comparison graph must induce at most two connected
components on the tied labels. Thus it applies with arbitrary real
heads and inner/output weights, a shallow remainder, and biases removed
by recession. It also counts distinct comparison graphs. It does not
apply this conclusion to unrestricted-degree trees.

## Connected sets of a fixed size

Put `d=Delta-1` and `alpha=1/y_Delta=d^d/(d-1)^(d-1)`. Fix neighbor orders
in a graph of maximum degree `Delta`. The deterministic breadth-first
tree of any connected set containing a specified root lifts to a finite
subtree of the nonbacktracking universal cover. The lift has exactly
the same number of vertices, and its projection recovers the original
set. This is an injection. The root has at most `Delta` child slots;
every other vertex has at most `d`.

Let `B(z)` be the formal planted-tree series and `R(z)` the root series.
They satisfy

\[
B=z(1+B)^d,\qquad
R=z(1+B)^{d+1}=B+B^2.
\]

Lagrange inversion gives, for every `m >= 1`,

\[
\begin{aligned}
r_m:=[z^m]R
 &=\frac1m\left\{\binom{dm}{m-1}
                    +2\binom{dm}{m-2}\right\}\\
 &=\frac{d+1}{dm+1}\binom{dm+1}{m-1},
\end{aligned}
\]

where a binomial coefficient with negative lower index is zero.
Stirling's formula yields

\[
r_m\sim
\frac{(d+1)\sqrt d}{\sqrt{2\pi}(d-1)^{5/2}}
\,\alpha^m m^{-3/2}.
\]

Consequently `r_m <= A_Delta alpha^m m^(-3/2)` uniformly for `m >= 1`,
after increasing the constant to cover the finitely many small sizes.
If `C_m(G)` counts connected vertex sets of size `m`, count each set
once at each of its `m` possible roots to obtain the essential factor:

\[
C_m(G)\le\frac{N r_m}{m}
\le A_\Delta N\alpha^m m^{-5/2}.
\]

Every induced set with exactly two components determines an unordered
pair of connected sets. Discarding disjointness and nonadjacency only
increases the count, so the number `P_m(G)` of size-`m` sets with at most
two components obeys

\[
P_m(G)\le C_m(G)+\frac12\sum_{j=1}^{m-1}C_j(G)C_{m-j}(G).
\]

Splitting the sum at `m/2` gives

\[
\sum_{j=1}^{m-1}j^{-5/2}(m-j)^{-5/2}
 \le 2^{7/2}m^{-5/2}\sum_{j\ge1}j^{-5/2}.
\]

The final series converges (it is at most `5/3` by an integral bound).
Thus, with a constant depending only on `Delta`,

\[
P_m(G)\le D_\Delta N^2\alpha^m m^{-5/2}.
\tag{1}
\]

## The pure graph family

Covering all size-`m` ties and using (1) gives

\[
|K|\ge\frac{m^{5/2}}{D_\Delta N^2}
             \binom Nm y_\Delta^m.
\]

Take `m` to be an integer nearest `pN`, where
`p=y_Delta/(1+y_Delta)`. For large `N` this has `m >= 3`.
The central weighted binomial estimate is

\[
\binom Nm y_\Delta^m
 \sim\frac{(1+y_\Delta)^N}{\sqrt{2\pi Np(1-p)}}.
\]

Since `m^(5/2)/N^2` is a constant times `N^(1/2)`, the polynomial factors
cancel. This proves the stated pure exponential lower bound.

## Mixtures with both original dictionaries

The caterpillar and rooted-star face dictionaries each have normalized
size-`m` locality capacity at most `6^m`. Let `Z` count those functions
together with arbitrary weighted comparison functions of maximum degree
at most `Delta`. Dividing the permutation-locality count by
`m!(N-m)!` gives

\[
\binom Nm\le
Z\left(6^m+D_\Delta N^2\alpha^m m^{-5/2}\right).
\tag{2}
\]

For `Delta <= 3`, use the degree-three majorant `alpha=4`. At
`m` nearest `N/7`, the second summand is exponentially smaller than
`6^m`. The weighted binomial estimate in (2) therefore gives

\[
Z=\Omega\!\left((7/6)^N/\sqrt N\right).
\]

For fixed `Delta >= 4`, one has `alpha >= 27/4 > 6`. At `m` nearest
`N/(1+alpha)`, the `6^m` term is exponentially smaller than the second
summand. The same cancellation as in the pure-family argument yields

\[
Z=\Omega_\Delta\!\left((1+y_\Delta)^N\right).
\]

These are asymptotic refinements of the elementary weighted-sum proof;
that proof remains available without Lagrange inversion or Stirling.
The mixture includes the specified original rooted-star face dictionary,
not the separately adjoined unrestricted family of arbitrarily oriented
star functions. No Lean verification is claimed here.
