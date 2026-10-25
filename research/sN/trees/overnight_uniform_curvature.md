# Function-level four-corner curvature: definition and exact star control

This is a failed scalar extension, with a precise remaining structural
requirement. It is not a separator for arbitrary tree units.

## An actual linear functional

Use the two blocks of coordinates \((u,v)\), \((s,t)\), with a common
zeroth coordinate fixed to zero. In each block choose either
\(u\geq v\geq0\) or \(u\leq0\leq v\), and similarly for the second block.
Use coordinates \((A,b,D,e)\) in either corner, so

\[
 u=A\ \text{or}\ b-A,\quad v=b,\qquad
 s=D\ \text{or}\ e-D,\quad t=e,
\]

and in all four charts the cone is
\(A\geq b\geq0,\ D\geq e\geq0\).
Truncate it by \(A,D\leq1\).

For a crease hyperplane with normal \(n=(a,B,d,E)\), retain only the class
\(B+E=0,\ B\ne0\). Give it the weight

\[
 \kappa(n)=\sigma(a+B)-\sigma(a)-\sigma(d)+\sigma(d-B).
\]

This weight is even under \(n\mapsto-n\), homogeneous of degree one,
and vanishes when the linear form has a fixed sign on the corner cone.

For each retained hyperplane, integrate its signed gradient-jump coefficient
over its intersection with the truncated cone, and divide by the measure
of that entire hyperplane section. Choose the first nonzero normal coordinate
positive and use ordinary Lebesgue measure in the other three coordinates.
The choice makes all computations rational for rational walls. Weight this
normalized integral by \(\kappa\), and sum over the finitely many crease
hyperplanes. Finally take the alternating sum over the four corners.
Call the resulting functional \(\Phi\).

This definition is linear on homogeneous CPWL functions: gradient-jump
measures add, the normal and section normalization are fixed for each
hyperplane, and intersections of different hyperplanes have measure zero.
For a single ReLU of a linear form in a corner, it gives exactly the
four-corner wall score from the natural-eight first-hidden-layer proof.
For arbitrary units it also sees partial crease pieces, including the
extra first hidden layer walls joining the two coordinate blocks.

The maximum has \(\Phi(\max_5)=1\). The first three corners have a maximum
crease outside the retained normal class; the last has \(\max(b,e)\),
whose normalized crease has weight one.

## The extra terms are real

The shallow function \(\sigma(u-s)\) has corner scores \((0,0,0,-1)\).
Thus \(\Phi\) itself does not even annihilate the shallow span.
Oddization

\[
 \Phi_{\mathrm{odd}}(f)=\Phi(f(x))-\Phi(f(-x))
\]

annihilates every shallow function, since
\(\sigma(h)-\sigma(-h)=h\), and \(\Phi\) annihilates linear functions.
It gives \(\Phi_{\mathrm{odd}}(\max_5)=2\).
This is still insufficient.

Take the inward star

\[
 U=\sigma(x_1-x_0+\sigma(x_2-x_1)
                     +\sigma(x_3-x_1)+\sigma(x_4-x_1)).
\]

In this labeling it has corner scores \((0,0,0,-1)\).
For its unaveraged sum over all \(5!\) label permutations,
the exact scores are

\[
 \Phi\!\left(\sum_\pi U_\pi\right)=6,\qquad
 \Phi\!\left(\sum_\pi U_\pi(-x)\right)=-39,\qquad
 \Phi_{\mathrm{odd}}\!\left(\sum_\pi U_\pi\right)=45.
\]

The corresponding maximum scores are \(120\) and \(240\).
Therefore ordinary symmetrization and oddization both fail the elementary
star-annihilation test.

## Exact computation

overnight_uniform_curvature.py derives all outer-crease pieces by fixing
the signs of the three first hidden layer expressions.
It also includes each first hidden layer crease on the portion where the
outer preactivation is positive. The head and tree-edge forms are linearly
independent, so no whole first hidden layer wall is simultaneously an outer
wall; codimension-two intersections do not affect these integrals.

Each required three-dimensional section volume is computed over the
rationals. Vertices are obtained by exact Cramer's-rule solves and checked
against every inequality. SciPy proposes a hull triangulation, but every
triangle is checked to lie on an exact supporting plane; every edge occurs
twice, and Euler's formula is checked. Volumes are then exact rational
determinants from an interior point. These are exact finite geometric
controls, not numerical quadrature.

The full symmetry control uses twenty distinct relabelings, each with
multiplicity six. Its receipt is
overnight_uniform_curvature_sym.json. Runtime is below one second.

## What an aggregate still needs

A scalar alternating sum over prescribed matchings transforms by the sign
character and consequently cancels the symmetric maximum, unless another
alternating normal or volume factor is retained. Squaring scalar scores
would destroy linearity. Thus the plausible continuation needs a relative
or tensor-valued output before a second alternating contraction.

Its cross-block first hidden layer jumps must remain explicit defect terms.
The operator above provides a concrete function-level starting point and
an exact star control, but no matching-deficiency cancellation has been
proved. A fixed prescribed-matching condition is also ruled out by the
existing exact noncrossing construction.
