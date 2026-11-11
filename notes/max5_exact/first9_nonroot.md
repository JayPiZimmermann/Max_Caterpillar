# Max5 first width nine: one shared contact reduction

Status: 31 October 2026. **The exactly-one-shared-contact positive case
is excluded**, with independent mathematical audit and four independently
checked CPC/Ethos refutations. Target is the remaining singleton-carrier
branch of a hypothetical exact two-hidden-layer Max5 network of widths
(9,4). This note does not claim the unrestricted exclusion.

The signed-carrier cost reduction gives two residual ReLUs over seven
invariant physical first features. Earlier work excludes two negative
outputs. For two positive outputs, each core uniquely carries at most
two of the five four-way top-tie rays q_i=-e_i. Hence at least one ray
is shared. The present calculation excludes exactly one shared ray.
Consequently any remaining two-positive-core candidate shares at least two.
The subsequent independently audited [two-shared-contact exclusion](two_shared_reduction.md)
now strengthens this to **at least three shared quadruple contacts**.

## Complete root reduction for exactly one shared ray

Relabel the unique contact pairs as 01 for g and 23 for h, and the
shared contact as 4. Complement either core, replacing g by -g and
absorbing g into the shallow remainder, when needed. The local comparator
signs can then be chosen positive. For c in {2,3,4}, set {a,b} to be its
complement among those three labels. The forced root part of g is

```
Qg = max(x_a,x_b)-max(x_0,x_c)-max(x_1,x_c)+x_c.
```

The analogous expression Qh uses the unique pair 23, a common label d
in {0,1,4}, and the other pair. The forced root triples are
`{0c,1c,ab}` and `{2d,3d,ef}`. Apart from these, g can use only root01,
and h can use only root23. A used nonroot normal must contain both labels
of its core's unique contact pair. These follow from the local one-core
Max4 classification, with no restriction to coordinate comparisons.

The nine choices of (c,d) give six distinct mandatory roots when c=d=4;
that case is already excluded in `max5_oct31_seven_nonroot.md`.
The other eight choices have five mandatory roots. Under swaps within
the unique pairs and interchange of the cores, they have two types:

* C5: c=2,d=0, roots 02,12,34,03,14.
* Triangle and attached path: c=2,d=4, roots 02,12,34,24,01.

The notation ij here describes a hyperplane, not a chosen feature
orientation. Each physical root feature may have either orientation.

## Local root curvature fixes the branch activities

Write r_ij for the consolidated root curvature of the remainder. At a
unique contact of g, the other core h has a strict nonzero value, so
locally the remainder plus either h or zero is the pair maximum that
complements the positive comparator g. Match root curvature at all four
unique contacts.

For the C5 type, the resulting identities force

```
h(q0)<0, h(q1)>0, g(q2)<0, g(q3)>0,
r02=2, r12=r03=1, r34=r14=0.
```

For example the local baseline at q0 is max(x1,x2), so r12=1 and
r34=0. The local baseline at q2 is max(x0,x3), so r03=1 and r14=0.
At q1, root03 then forces h active; at q0, root14 forces h inactive.
The corresponding comparison gives the two g activities, and root02
fixes its coefficient to two.

For the triangle type, allow an optional coefficient lambda on root01
in g. The same equations force

```
h(q0)>0, h(q1)>0, g(q2)<0, g(q3)>0,
lambda=0,
r02=r12=r34=r24=1, r01=0.
```

In detail r02=r12=1 follows from q1,q0. At q3 these force g active,
and the baseline root24 forces r24=1. The equations at q0,q1 then force
h active and r34=1. At q2 the root34 equation forces g inactive.
Comparing root01 at q2 and q3 yields r01=lambda=0.

For an additional distinct root outside the five mandatory roots, its
curvature in g and h is zero except for the optional contact edges;
the same equations force those optional coefficients zero. This does
not remove an additional physical root in the reverse orientation:
such a pair can supply a linear function. That case must be retained.

## Exact necessary models

Two model families are implemented under
`research/sN/frontier5/`:

1. `max5_exact_one_shared_local.py`: five mandatory root rows and two
   distinct, nonproportional nonroot rows. It retains every root
   orientation and arbitrary real nonroot normals and coefficients.
2. `max5_exact_one_shared_one_nonroot.py`: the five mandatory roots,
   one arbitrary additional physical root, and one nonroot row.
   The extra root can repeat any mandatory root in either orientation.
   All actual root coefficients are free, and the local equations
   consolidate their curvatures. The other core's activity at each
   unique contact is also a free Boolean variable in this model.

Both impose the exact local comparator germ for g at q0,q1 and for h
at q2,q3; the complementary pair-maximum germ for the remainder plus
the active other core; strict nonzero values of that other core; and
g(q4)=h(q4)=0. They also impose the necessary four-face first-support
cover. They are relaxations: full global equality is not imposed.
UNSAT therefore gives an exclusion, while SAT would only give local
candidate data.

Positive row scaling normalizes the first nonzero coefficient among
g,h,remainder to magnitude one. In particular, a nonroot used only by
the remainder is included. Completely unused physical features can be
excluded using the already established global first-width minimum nine.

All four models have CVC5 UNSAT proofs checked independently by pinned
Ethos, without proof holes. The receipts are
`max5_exact_one_shared_cycle_audit.ethos.json`,
`max5_exact_one_shared_triangle_audit.ethos.json`,
`max5_exact_one_shared_one_nonroot_cycle_audit.ethos.json`, and
`max5_exact_one_shared_one_nonroot_triangle_audit.ethos.json`.
The separate Z3 run also returns UNSAT for the two-nonroot models and
times out for the one-nonroot models; those timeouts play no role in
the conclusion. An independent rational checker,
`max5_exact_one_shared_reduction_check.py`, verifies the eight-to-two
orbit cover and the hardcoded curvature/activity deductions.

## Proportional nonroot rows

Same-orientation proportional rows are functionally duplicate and reduce
the global first width below nine. Two opposite rows are handled
separately. For the C5 type, the existing cycle-contrast theorem forces
their common normal to be a root, contradicting nonroot status.

For the triangle type, the four-face cover on {0,1,2,3} must cover label3.
None of the five mandatory roots does so within that four-set. Thus
the common nonroot normal l has l4=0. The two opposite features provide
only one linear direction l in addition to their absolute ridge.
The local comparator conditions at q2,q3 then give h=Qh plus a
combination of l and its ReLU that vanishes near both contacts.
Both additions vanish at q4 because l4=0, whereas Qh(q4)=-1. This
contradicts the shared-contact condition h(q4)=0. The independent audit
also checks this deduction. With no nonroot features, the existing
complete-comparison exclusion applies. These cases exhaust all seven
physical first-row budgets after the five mandatory roots.

## Remaining unrestricted obligation

The two positive cores may still share three or more quadruple rays.
The [mixed-sign residual case](first9_mixed.md) is now independently
excluded in full, and the [exactly-two-shared positive case](two_shared_reduction.md)
is independently excluded as well. Neither contact elimination proves
that (9,4) is empty until the remaining positive configurations have also
been excluded.
