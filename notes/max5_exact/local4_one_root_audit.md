# Independent audit: positive two-fold Max4 with three first hyperplanes

Status: **PASS**, 31 October 2026. Audited
[local4_three_hyperplanes.md](local4_three_hyperplanes.md), including the
one-nonroot Max3 rigidity premise in
[allfive_shared_rank.md](allfive_shared_rank.md), the 288-case finite
model, the adjacent-root argument, and the support-cover reduction.

The exact conclusion is: if

```
Max4 = R + ReLU(g) + ReLU(h)
```

and R,g,h are homogeneous shallow functions using at most three distinct
translation-invariant first hyperplanes, with arbitrary additional linear
functions, then those hyperplanes must include a disjoint pair of
coordinate-comparison hyperplanes. This is a necessary local structural
condition. It does not classify the whole Max5 (9,4) fiber.

## The local Max3 premise

The positive-two-fold rigidity statement is valid. After relabeling and
reorienting the sole nonroot line, write it as H=alpha*x+beta*y with
alpha,beta>0. In H<0, Max3 has two distinct crease rays. Each positive
outer fold is linear before activation on this half-plane, so the two
cores must carry these rays separately, with unit curvature. Independently
complementing the cores makes their restrictions exactly x and y, while
the remainder is zero there.

Continuity fixes their values on H=0. Each linear continuation to H>0
has a zero ray in that half-plane because its boundary restriction changes
sign. Positive outer curvature cannot cancel. Thus both rays must be
the target's only crease x=y>0, forcing the continuations
`x-H/(alpha+beta)` and `y-H/(alpha+beta)`. This gives the claimed global
forms and fixes the remainder.

For a local germ with an extra untied coordinate, neither core can depend
on that coordinate: a nonzero slope would create an extra positive crease
along its free axis, whereas the target and shallow first features are
affine along it. Hence the premise supplies the full ambient gradients,
not merely a restriction to the tied-coordinate slice.

## Exhaustiveness of the one-root model

Fix root01 and nonroot planes A on 023 and B on 123. Every genuine
zero-sum triple normal can be reversed and positively scaled to have a
unique negative coefficient -1 and two positive coefficients u,1-u with
0<u<1. Reorientations are harmless because arbitrary linear functions are
allowed. Repeated or zero coefficient boundaries are roots, outside this
declared one-root/two-genuine-nonroot case.

At q0=-e0, only B is singular. At q1=-e1, only A is singular. The local
Max3 result requires both cores to vanish at both contacts and fixes their
curvatures on A and B. Assigning A's positive-coordinate labels to the
cores can be fixed by one global core interchange; B has two assignments.
Each core's local sign can be complemented independently at either
contact, with the corresponding remainder correction explicitly retained.
This gives 3*3*2*4*4=288 cases and covers every real normal ratio.

I checked the producer's equations directly. Write a global function as
`L+c*ReLU(x0-x1)+ca*ReLU(A)+cb*ReLU(B)`. At q0 its affine local part is
`L+ca*A` exactly when A's negative coordinate is 0, and L otherwise.
At q1 it is `L+c*(x0-x1)+cb*B` exactly when B's negative coordinate is 1,
and `L+c*(x0-x1)` otherwise. These are precisely the two gradient equations
in the source. The coefficients ca and cb equal the signed curvatures
forced by local rigidity; the remainder's coefficients are one minus the
number of complemented local cores. All remaining global linear terms
and the root coefficient c are unrestricted.

The three extra evaluations are necessary consequences of the full identity
at `(1,1,0,0)`, `-e2`, and `-e3`. All equations are linear real arithmetic:
the nonroot ratios multiply only fixed integer curvature coefficients.
The aggregate is the disjunction of all 288 complete case formulas.
Reusing variable names across disjuncts does not identify distinct cases:
existence of a solution to their disjunction is exactly existence for at
least one case.

## Checked exclusion and a non-vacuous control

The aggregate original SMT source has SHA256
`3abd78fbbfcf8daa8d38911257714146d5bf9fcc1e7d95b74629ecd3fbe3fd77`.
Its 2,680,408-byte CPC proof contains one proof root and no trust rule.
The pinned independent Ethos checker proves false against the normalized
original formula and returns `correct`. The source hash agrees with the
current file. The exact receipts are
`max5_exact_local4_one_root_germs_audit.cvc5.json` and
`max5_exact_local4_one_root_germs_audit.ethos.json` under
`research/sN/frontier5/`.

A further independent source-structure checker imports no producer and
confirms 288 distinct Cartesian cases, each with four strict parameter
bounds, 24 local linear equations, and three evaluation conditions. It
rebuilds all 864 evaluation conditions directly and replays Ethos against
the current source. The receipt is
`max5_exact_local4_one_root_independent_replay.json`.

The local gradient constraints alone are satisfiable. An independent
rational control uses

```
A = -x0 + x2/4 + 3*x3/4,
B = -x1 + x2/4 + 3*x3/4,
g = -x0-x1+5*x2/4+3*x3/4-ReLU(A)-ReLU(B),
h = -x0-x1+x2/4+7*x3/4-ReLU(A)-ReLU(B),
R = x0+x1-x2/4-3*x3/4+ReLU(A)+ReLU(B).
```

It has both required local Max3 germs, but gives 2 at `(1,1,0,0)` instead
of 1. Thus the added evaluations exclude genuinely compatible local
data rather than merely restating an inconsistent normalization.

## Adjacent-root obstruction

The analytic exclusion for roots01,02 and a nonroot plane on123 also
passes. In the opposite-sign coefficient case, that plane crosses the
interior of the missing target facet. A positive core carrying the facet
on one side cannot continue across the nonroot plane with nonzero curvature:
its continued zero plane would differ from the target plane and would
create a positive crease inside a target linearity region. It cannot
become identically zero there, because the target normal and the nonroot
normal are independent. Local Max3 rigidity, however, forces both cores'
nonroot curvatures to be nonzero.

In the same-sign case, the source's explicit extension formulas are
exhaustive because their differences from the required local forms vanish
on the open quadrant a,b>0 and use only the two remaining root planes.
Continuing the missing facets across b=0 and a=0 forces B=C=0 in the
source notation. The facet c=0 with a,b<0 then forces A=1 or D=1.
At the supplied witness, the corresponding core has a nonzero transverse
gradient and vanishes strictly inside a target winner region and a first
activation cell. Its positive kink cannot be canceled. Both sign cases
therefore give exact contradictions.

## Support-cover bridge

Every top triple must contain a supported first normal; otherwise its
local Max3 germ would be shallow. Every coordinate must occur in some
first normal. For the latter assertion, if x_i is absent, write each core
as a constant multiple of x_i plus a shallow function of the other inputs.
Subtracting the x_i-to-positive-infinity and x_i-to-negative-infinity
identities cancels all zero-slope folded terms and expresses the remaining
three-input maximum as a shallow function, which is impossible.

For at most three distinct nonzero first hyperplanes, these two necessary
conditions leave only: a matching pair of roots; two adjacent roots plus
the triple avoiding their common vertex; or one root plus the two triples
avoiding its endpoints. I independently enumerated support multisets,
including repetitions and four-coordinate supports, and obtained 36, 12,
and 6 labeled support cases respectively, with no other cases. The final
two families are exactly the audited exclusions above.

The standard-library checker
`research/sN/frontier5/max5_exact_local4_audit_check.py` verifies this
support cover and the rational local-germ control with exact fractions.
Its adjacent JSON records the full finite inventory. No bounded numerical
search or generic-position assumption is used. No Lean implementation
or verification is claimed.
