# Two positive Max4 folds over at most three first hyperplanes

Status: 31 October 2026. **Complete and independently audited.** The
one-root case has an exact finite linear model and a trust-free CPC
refutation checked independently by Ethos. The adjacent-root case has
an independently audited analytic proof. The combined local classification
is established; it is not a full Max5 width theorem.

The model is

```
Max4=R+ReLU(g)+ReLU(h),
```

where R,g,h are homogeneous shallow functions with the declared first
hyperplanes and arbitrary additional linear functions. Both outer output
coefficients are positive and have been absorbed into g,h. First feature
orientations are immaterial here because their reversals differ by a
linear function. This enlarged model includes every corresponding local
germ of a two-positive-core Max5 representation.

## Two adjacent roots and one nonroot triple

Suppose the only nonlinear first hyperplanes are roots 01 and 02 and
a genuine nonroot supported on 123. Set x0=0 and write
`a=x1,b=x2,c=x3`. The third normal is

```
L=alpha*a+beta*b-(alpha+beta)*c,
alpha*beta*(alpha+beta)!=0.
```

At the top triple 123, the two root features are affine and only L can
be singular. The one-nonroot Max3 rigidity lemma from
[the contact note](allfive_shared_rank.md) forces both outer cores to
use L with nonzero curvature.

If alpha and beta have opposite signs, L crosses the interior of the
missing target facet `c=0,a<0,b<0`. Any positive outer core carrying an
open patch of this facet must keep its zero hyperplane equal to c=0
on both sides of L. Otherwise its continued zero hyperplane on the
other side is an extra positive crease in a region where the target
is affine. A first curvature jump proportional to L cannot turn a
nonzero multiple of c into zero or another multiple of c, because L
is not proportional to c. Thus such a carrier must have zero L
curvature. Both cores have nonzero L curvature, a contradiction.

If alpha and beta have the same sign, reverse L so that they are both
positive, and put s=alpha+beta. At the 123 contact, independently
complementing and exchanging the cores gives the unique local form.
Every global extension using the three declared hyperplanes therefore
has the form

```
g=a-c-ReLU(L)/s+A*ReLU(-a)+B*ReLU(-b),
h=b-c-ReLU(L)/s+C*ReLU(-a)+D*ReLU(-b).
```

On the missing facet `a=c>max(0,b)`, L is negative. The first core
already carries that facet for b>0. If B were nonzero, continuation
across b=0 would create its zero plane at `a-c+B*(-b)=0` when b<0,
an extra positive crease. Hence B=0. The corresponding argument on
`b=c>max(0,a)` gives C=0.

On `c=0,a<0,b<0`, L is negative, and the core values are
`(1-A)*a` and `(1-D)*b`. The target crease requires A=1 or D=1.
If A=1, choose `a=-beta,b=alpha,c=-1`. Every first preactivation is
strict, L=s>0, and

```
g=-(alpha*a+beta*b)/s=0.
```

Its transverse derivative is nonzero, producing a positive crease
where b is the unique target maximum. The shallow remainder is affine
there, and another positive folded term cannot cancel the crease.
This is impossible. The case D=1 is symmetric. Thus this entire
arbitrary-real three-hyperplane family is excluded.

## One root and two nonroot triples

Now suppose the three hyperplanes are root 01, a genuine nonroot A
supported on 023, and a genuine nonroot B supported on 123.
Reverse and scale each nonroot normal so that its unique negative
coordinate is -1 and its two positive coordinates sum to one.
Let u and v be their first positive coordinates, each strictly between
zero and one. This covers every genuine zero-sum normal on a triple.

At q0=-e0 only B is singular; at q1=-e1 only A is singular.
The one-nonroot Max3 rigidity lemma forces both cores to vanish at
each contact. After assigning the two positive-coordinate labels of
each normal to the two cores, their local forms are

```
epsilon*(x_major-x_minor-ReLU(normal)), epsilon in {+1,-1}.
```

Their local remainder is the minority coordinate plus ReLU(normal),
plus each canonical core whose orientation was complemented.
These formulas include the full ambient linear gradient: neither core
can depend on the omitted coordinate, since an extra crossing plane
would create uncanceled positive curvature.

Fix the majority assignment for A by exchanging the two cores globally.
There are exactly

```
3 choices of A's minority,
3 choices of B's minority,
2 majority assignments for B,
4 independent core orientations at each contact,
288 cases in total.
```

The producer
`research/sN/frontier5/max5_exact_local4_one_root_germs.py`
imposes these full local gradient equations with arbitrary global linear
coefficients and an arbitrary coefficient of ReLU(x0-x1). It also
imposes the target values at the three points

```
(1,1,0,0), (0,0,-1,0), (0,0,0,-1).
```

The first normal coefficients are affine in u,v, and their multipliers
in g,h,R are fixed integers determined by the local orientations.
Therefore every case is linear real arithmetic, including the ReLU
case distinctions at the three fixed points. No coefficient bound or
sampled approximation is used. The union of all 288 cases is written
to `max5_exact_local4_one_root_germs.smt2`.

The local equations alone allow 16 cases. These are global core
complementations of three geometric forms. The added three evaluations
exclude all of them. The independent mathematical and model audit is
[local4_one_root_audit.md](local4_one_root_audit.md). It also checks the
ambient omitted-coordinate argument, all 288 cases, and all 864 added
point equations. Independent replay is recorded in
`research/sN/frontier5/max5_exact_local4_one_root_germs_audit.ethos.json`.

## Established local classification

The C3/C4 support conditions for Max4 with at most three singular first
hyperplanes leave only the following alternatives:

1. Two disjoint coordinate roots are present.
2. Two adjacent roots and a nonroot on the remaining triple.
3. One root and one nonroot on each of the two triples avoiding that root.

The latter two alternatives are exactly the obstructions above. Thus a
Max5 quadruple-contact germ with at most three singular first hyperplanes
must contain two disjoint coordinate roots. This is a necessary local
condition, not a complete global Max5 width theorem.

Applying it to the existing 431-orbit seven-row support inventory leaves
209 support orbits, including 198 with a nonroot row. The surviving root
row counts are at least three. These are necessary support counts, not
feasible-network or component counts. The local theorem holds whether
the two global core values at the quadruple are both zero or only one
is zero, since a nonzero core may be absorbed into the local shallow
remainder.
