# Relative first variation and the all-chart scalar obstruction

Status: an explicit relative operator and an exact obstruction to its
scalar chart assembly. **It does not descend to the top-dimensional
quotient.** Stop scalar variants of this construction.

## Relative operator on actual CPWL functions

Retain a reference label \(a\), remove four other labels, and use the four
corner charts from overnight_uniform_curvature.md on the removed labels,
relative to \(x_a\). Keep the other coordinates \(z\) as parameters.
Let \(\Phi_R\) use \(0\leq b\leq A\leq R\) and
\(0\leq e\leq D\leq R\), including the normalization by the full affine
hyperplane section in each corner.

Define

\[
 {\cal R}f(z)
 =-\frac13\left.\frac{d}{dt}\right|_{t=0+}
       \Phi_1\bigl(f(\text{corner variables relative to }tz_a,\ tz)\bigr).
\]

This is a linear operation on finite homogeneous CPWL functions whenever
the corner functionals are taken with the fixed wall-normal convention.
The derivative exists and is CPWL in \(z\): section vertices depend
affinely on the external offsets within finitely many polyhedral regions;
section volumes are piecewise polynomial of degree at most three.
The denominator has a strictly positive constant term whenever its crease
weight is nonzero. The first-order ratio coefficient is therefore
piecewise linear. Coincident walls add before or after taking the limit.
These statements give existence and linearity, not a filtration bound.

For the maximum, let \(M=\max_{i\text{ retained}}z_i\), including \(a\).
Only the fourth corner contributes. Its crease \(b=e\) is active when
\(b=e\geq M-z_a\). Its normalized section measure is

\[
 \Phi_R(\max_N)=\left(1-\frac{M-z_a}{R}\right)_+^3.
\]

Indeed its cross-sectional density at \(b=e=r\) is proportional to
\((R-r)^2\). Thus

\[
 {\cal R}\max_N=M-z_a.
\]

The operator sends a maximum to a maximum on the retained labels modulo a
linear term. This fact alone is insufficient.

## Explicit first-variation defect states

After eliminating the crease equation, each section is a three-dimensional
polytope with fixed inequality normals and offsets affine in \(tz\).
For a facet of the limiting polytope, group all inequalities defining that
same supporting plane and orient their interior normals consistently.
Their effective first-order offset is the minimum of their normalized
offsets. The facet's contribution to the volume derivative is that minimum
times its fixed two-dimensional measure, with the usual normal-coordinate
factor.

If a section collapses at \(t=0\) to a two-dimensional face, its first-order
volume is the area of that face times

\[
 \left[\min(\text{upper offsets})
             -\max(\text{lower offsets})\right]_+.
\]

Sections of limiting dimension at most one have zero first-order volume.
For a normalized ratio \(V(t)/D(t)\), the remaining correction is
\((V'(0)D(0)-V(0)D'(0))/D(0)^2\).
Thus the recurrence retains minima, maxima, and positive-part functions
of the external offsets. These are genuine CPWL boundary states.
Cross-block first hidden layer walls and the corner boundaries both occur
among these states; neither can be discarded.

## Mandatory filtration control: failure

Let \(F_a=\max_{i\ne a}x_i\), omitting the reference apex.
On every probed corner, both common coordinates are at least \(x_a\).
Consequently \(F_a=\max_N\) throughout every chart and

\[
 {\cal R}F_a={\cal R}\max_N.
\]

But \(F_a\) belongs to the lower-dimensional span
\(L_{N-2}\), modulo a linear term.
Therefore \({\cal R}\) does **not** supply the required map
from the top quotient to the smaller top quotient.
Its reference-apex boundary defect would have to be cancelled before any
separator claim or scalar iteration.

## No scalar assembly over all apex charts repairs the base case

At five labels, take any chart with reference apex \(a\), first coordinates
\(u,s\), and common coordinates \(v,t\).
Write \(F_j=\max_{i\ne j}x_i\) and \(G_j=\min_{i\ne j}x_i\).
The exact corner formulas give

\[
 \Phi(\max_5)=1,\qquad
 \Phi(F_j)=1_{\{j=a\}},\qquad
 \Phi(G_j)=1_{\{j=v\text{ or }j=t\}}.
\]

Hence every such chart annihilates

\[
 H=\max_5-\frac13\sum_{j=0}^4(F_j+G_j).
\]

Its input-reflected version does too, since
\(\max(-x)=-\min(x)\) and the full minimum has score one.
This covers every apex choice, every pairing, every block ordering, and
both reflection sectors.

Each \(F_j\) and \(G_j\) belongs to \(L_3\).
Therefore **no scalar linear combination of this entire chart family can
annihilate \(L_3\) and detect \(\max_5\)**.
The obstruction applies to arbitrary coefficients, rather than just an
ordinary symmetry average or an alternating matching sum.

The standard-library checker overnight_uniform_relative_curvature.py
proves the scoring table by exact dominance on each simplicial corner cone.
After removing dominated forms, each extremum has at most two remaining
linear forms, so its crease weight is evaluated directly.
No integration, Fourier samples, or matrix rank is used.

A viable Čech or flag construction must retain new overlap/transition
information. Listing or tensoring these same scalar values without new
boundary data cannot repair their loss of the top quotient.
