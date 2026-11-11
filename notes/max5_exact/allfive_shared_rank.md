# Shared positive contacts: rank limits and a local rigidity lemma

Status: 31 October 2026. This note studies the remaining two-positive-core
case at Max5 widths (9,4). It does not claim an exclusion of that case.

## Why the five-by-seven rank count is insufficient

Let the seven invariant first normals be a_j and let
`B_ij=ReLU(-a_ji)`. If both shallow cores vanish at all five quadruple
contacts `q_i=-e_i`, their coefficient vectors c and d satisfy
`B*c=B*d=0`. Since B has five rows and seven columns, its kernel already
has dimension at least two. Linear independence of the seven functions
does not imply linear independence of their five-point evaluations.
Consequently this rank inequality alone cannot force proportional cores.

The local singular first rows at q_i are precisely those whose i-th
coordinate is zero. If their counts are m_i, then
`sum_i m_i=sum_j(5-size(support(a_j)))`. With seven rows this is at most
21. This exposes small local dictionaries but does not by itself classify
their positive two-core completions.

## One nonroot line: exact positive-two-core Max3 rigidity

Suppose an identity

```
max(0,x,y)=R+ReLU(g)+ReLU(h)
```

uses shallow R,g,h whose only possible nonlinear first hyperplane is
`H=alpha*x+beta*y=0`, with alpha,beta strictly positive. Arbitrary linear
terms are allowed. Then, after interchanging and independently complementing
the two cores and compensating R, the identity is forced to be

```
g=x-ReLU(H)/(alpha+beta),
h=y-ReLU(H)/(alpha+beta),
R=ReLU(H)/(alpha+beta).
```

Here complementation means replacing g by -g and R by R+g, which
preserves the positive output sign and the represented function.

On H<0, at most one of x,y is positive, and the target has its two
distinct creases along the negative portions of the coordinate axes.
Every core is linear there. No extra positive crease can cancel, so
the two cores must carry these two target creases separately. Their
unit curvature, after complementation, forces g=x and h=y, with R=0
on this half-plane.

On H=0 their restrictions remain x and y. Each restriction changes sign
along that boundary, so each linear extension into H>0 has one crossing
zero ray inside that half-plane. The target has just one such ray,
x=y>0. Positive outer signs prohibit cancellation of another ray.
Both core zero rays therefore coincide with x=y. Continuity across H
fixes the extensions as `x-H/(alpha+beta)` and
`y-H/(alpha+beta)`. The target value fixes R as H/(alpha+beta).
These are precisely the displayed global shallow functions.

Thus the two nonroot ridge coefficients have the same nonzero magnitude,
and, after the indicated orientation choices, g-h is globally linear.
The argument includes zero preactivation on the target rays; it does
not require generic nonzero gates there.

Every line distinct from the three Max3 target lines separates its three
target rays into a two-ray side and a one-ray side. Relabeling the three
target coordinates and reversing H puts it into the stated form. Hence
the coefficient-magnitude conclusion applies to every rootless top triple
with exactly one singular first hyperplane in a positive-two-core Max5
germ. Both cores must vanish at that triple: otherwise only one folded
linear core remains on a strict first cell containing two target rays.

This is a local necessary condition. Independent core complementation can
be chosen separately when proving each local statement, so the invariant
global consequence is equality of the absolute ridge coefficients. A
single global orientation choice across all triples is an additional
compatibility question.

## Why the immediate rank-five shortcut does not finish the search

Suppose B has rank five, so its kernel C has dimension two. If a local
singleton-triple condition gives `c_j^2=d_j^2`, put u=c-d and v=c+d.
Then `u_j*v_j=0`. If three such coordinate functionals restricted to C
are nonzero and pairwise projectively distinct, one of u,v must vanish:
two nonzero vectors in a two-dimensional space can be annihilated by at
most two distinct functional directions between them. This would make
g and h equal up to sign, reducing the positive pair to at most one
outer fold plus a shallow term.

However, the independently audited local three-hyperplane theorem in
[local4_three_hyperplanes.md](local4_three_hyperplanes.md) leaves 209
seven-row support orbits. Their numbers of singleton rootless-triple
rows are:

| Number of such rows | Support orbits |
| --- | ---: |
| 0 | 171 |
| 1 | 31 |
| 2 | 7 |

No survivor has the three rows needed for this immediate argument.
Thus a rank-five proof requires additional coefficient relations from
other local germs; the singleton-triple constraints alone cannot close
the all-five-shared case. Lower-rank B also remains outside that shortcut.
