# A nonnegative signed state outside the positive coefficient cone

The cone-saturation conjecture for the 48-function finite Hadamard orbit is
false. The counterexample has only six terms, each with coefficient \(1\)
or \(-1\). It is a nonnegative function, but it does not yet give a shallow
outer-ReLU fold or a network construction.

Put \(S=\sum_i x_i\), and define five orbit functions

\[
 B(x)=\sigma\!\left(\min_i(S/2-x_i)\right),
\]

\[
 D_i(x)=\sigma\!\left(\min\left\{S/2,\ x_i+x_j-S/2:j\ne i\right\}\right),
 \qquad 1\le i\le4.
\]

Their four linear arguments are orthonormal frame coordinates, so all five
belong to the specified orbit. Define

\[
 F=B+D_1+D_2+D_3+D_4-q.
\]

**Claim:** \(F\ge0\) everywhere, but \(F\) has no representation as a
nonnegative linear combination of the 48 orbit functions.

## Direct proof of nonnegativity

Outside the closed positive orthant, \(q=0\), so the assertion is immediate.
Inside that orthant let \(M=\max_i x_i\), \(m=\min_i x_i\), and
\(t=S/2-M\). Only a dominant term indexed by a largest coordinate can be
positive; its value is \(\sigma(m-t)\). The other dominant terms vanish,
and \(B=\sigma(t)\). Therefore

\[
 F=\sigma(t)+\sigma(m-t)-m
   =\sigma(-t)+\sigma(t-m)\ge0.
\]

If the largest coordinate is repeated, the possibly positive dominant
value is zero, so the same formula remains valid.

## Why changing the coefficient representation cannot make it positive

The signed-orbit classification in `overnight_fixed_f4_signed.md` proves
that the coefficient kernel is one-dimensional. In its normalization
\(k_q=1\), it has coefficient \(-1\) at a coordinate orthant function
whose first coordinate has reversed sign. That orthant function has
coefficient zero in the displayed six-term expression.

Every other coefficient vector for \(F\) is consequently \(w+tk\).
Nonnegativity at the base function requires \(-1+t\ge0\), whereas
nonnegativity at the stated zero coefficient requires \(-t\ge0\).
These are incompatible.

## Exact finite fan control

`overnight_fixed_f4_cone_verify.py` independently constructs the three
frames, the six functions, and the 24 possible walls. It enumerates all
240 oriented rays by rational Gaussian elimination on triples of wall
normals. It verifies nonnegativity on every ray and the exact zero relation
on every ray. All functions are linear on each cone of this complete
pointed arrangement, so the ray check proves global nonnegativity.

At each nonzero ray exactly two orbit functions are positive, with equal
values. The 120 occurring pairs form a five-regular bipartite graph. The
five positive terms in this example are exactly the base function's five
neighbors. Pointwise nonnegativity tests only these 120 edge inequalities;
nonnegative coefficient representatives would require all 576 inequalities
between opposite signs of the unique kernel. This graph explains the
failure of cone saturation.

## One-fold probe, with restricted scope

The exploratory producer `overnight_fixed_f4_signed_candidate.py` tested
whether this particular \(F\) equals \(\sigma(g)\) with \(g\) in the
28-dimensional shallow span of the 24 F4 walls and the coordinates.
On the 1152 chambers it identified 117 rays where equality with \(F\)
is forced by a neighboring positive chamber. Those equalities are
inconsistent; the producer checks a rational 21-row contradiction.

This rejects the candidate only in that prescribed shallow span. It has
not been promoted to a rejection for arbitrary first hidden layer walls:
the positive set has several connected components, so a wall avoiding all
of them might contribute different linear restrictions on different
components. The cone counterexample itself is independent of this probe.
