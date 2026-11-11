# Exactly four shared positive contacts at Max5 first width nine

Status: 31 October 2026. The branch is not yet completely excluded.
There is an exhaustive finite support cover and an independently audited
necessary model. Proof-producing solver batches are running. Solver
counts below concern support cases, not network fibers or components.

## Problem and normalization

The remaining physical (9,4) singleton-carrier case has the residual
identity

```
Max5 = ell + R + ReLU(g) + ReLU(h),
```

where R,g,h belong to the actual span of seven invariant physical first
features, and ell has coefficient sum one. No additional linear terms
are freely supplied to the three shallow functions.

In this branch g vanishes at all five q_i=-e_i, while h vanishes exactly
at q_1,...,q_4. Relabeling inputs and complementing the cores permits

```
germ_q0(g) = max(x_1,x_2)-max(x_3,x_4),
h(q_0) < 0,
germ_q0(ell+R) = max(x_3,x_4).
```

The first dictionary therefore contains the comparison hyperplanes 12
and 34. Its physical orientations remain free: fixing a support-orbit
representative does not permit further input swaps as orientation gauges.

## A useful normal form at the unique contact

Consolidate first hyperplanes, and write

```
A=max(x_1,x_2), B=max(x_3,x_4), Q=A-B.
```

Every first hyperplane not containing q_0 can be oriented by a defining
normal b_j with b_j0=1. Then the local identities imply global identities

```
g = Q + sum_j c_j*ReLU(b_j.x),
ell+R = B + sum_j d_j*ReLU(b_j.x).
```

Only those first hyperplanes with nonzero coordinate 0 occur in these
sums. This statement introduces no freely available feature: it is an
identity between shallow functions obtained from the actual dictionary.

To prove it, the prescribed germ fixes the curvature of every first
hyperplane containing q_0: the two matching planes have the displayed
coefficients, and every other such plane has zero consolidated curvature.
For a remaining feature subtract its affine germ at q_0. If its original
normal has positive coordinate 0, the feature is already zero near q_0.
If that coordinate is negative, use ReLU(t)-t=ReLU(-t). The remaining
linear part vanishes because the full germ has been matched.

Let N_ij=max(-b_ji,0), with i=1,...,4. Since Q and B vanish at all the
q_i, the contact equations give

```
N*c=0, N*d=0.
```

Moreover c is nonzero. Otherwise g=Q globally and

```
Max5-Max(x_1,x_2,x_3,x_4)
  = shallow + ReLU(h).
```

At e_0 the directional target is u_0-Max(u_1,u_2,u_3,u_4). A strict
h(e_0) would make this shallow, which it is not. If h(e_0)=0, rearranging
its directional identity would represent Max4 as shallow minus one
ReLU, contradicting the audited tetrahedron theorem in
[the polytope note](polytope.md). Thus c cannot vanish.

Consequently N has nontrivial kernel, at least two correction hyperplanes
are needed, and at least one nonroot hyperplane containing coordinate 0
must be used by g. Indeed each column of N is nonzero, and for distinct
comparison planes 0i the columns are distinct coordinate vectors.
This immediately rules out 69 of the 587 decorated support cases; these
are already among the initial local-solver exclusions. This normal-form
argument itself has not yet received a separate independent audit.

## Finite support cover and necessary equations

Starting from the independently audited 193 surviving C3/C4 support
orbits, decorate each support multiset with its unique contact and chosen
matching. Normalize that decoration to q_0 and 12|34, and quotient by
the eight permutations preserving it. This gives exactly **587 cases**.
The independent decorated-orbit enumeration agrees with the producer.

The producer is `research/sN/frontier5/max5_four_shared_support_cover.py`.
The inventory is `max5_four_shared_supports.json`; the independent
receipt is `max5_four_shared_cover_audit.json` in the same directory.

The necessary model `max5_exact_four_shared.py` retains:

* every physical root orientation;
* arbitrary real nonroot normals, normalized only by positive scaling;
* opposite features and coincident nonroot hyperplanes, with their
  curvature coefficients consolidated exactly;
* all seven physical feature coefficients in R,g,h, with no extra linear
  terms in their span;
* the complete unique-contact comparator and baseline germs;
* the four shared-zero conditions and exact values of the target there;
* the audited rigid-contact comparator allocation, including the budget
  of at most two canonical contacts per core;
* the full-support nonroot-wall criterion when both cores use that wall;
* optional exact finite sample equations and the fifteen-branch
  odd-normal-plane constraint.

Minimal first width also excludes unused features and duplicate
same-orientation features. Opposite orientations remain allowed. An
unused or mergeable feature would leave at most six invariant features;
adjoining the signed ell pair and using
ReLU(ell+R)-ReLU(-ell-R)+ReLU(g)+ReLU(h) would contradict first width nine.

See [the full model audit](four_shared_model_audit.md) and
[the odd-normal-plane audit](four_shared_structure_audit.md).

## Exact shared-contact tangent probes

For a first normal a, its directional feature at q_i is

```
a_i<0:  a.u,
a_i>0:  0,
a_i=0:  ReLU(a.u).
```

Both outer cores vanish at a shared contact, so their output derivatives
are the ReLU of these shallow directional functions. The target derivative
is max(u_j : j!=i). The model optionally checks all fourteen nonconstant
Boolean assignments to these four coordinates at each of the four
shared contacts: **56 exact directional equations**. These are not finite
differences and use no small numerical epsilon. Their translation has
also been independently audited.

## Current computation and precise remaining obligation

An exploratory one-second Z3 sweep of all 587 local necessary models
reported 473 UNSAT, 52 SAT, and 62 timeouts. The SAT results were local
data, not global representations. Adding Boolean input values to the
114 unresolved cases gave five further UNSAT results and 109 timeouts
at five seconds per case.

CVC5 is substantially stronger on the tangent equations: the first
formerly SAT case, case 2, is UNSAT with a trust-free CPC proof. Separate
batches now attempt independent CVC5/Ethos certificates for the 473
initial cases and the 114 remaining cases, using frozen formulas and
hashed receipts. Until those batches finish and every case is covered,
these figures do not establish the full four-shared exclusion.

The related new general tool is the odd-normal-plane theorem in
[four_shared_structure.md](four_shared_structure.md): two residual cores
force a centrally symmetric parallelogram projection and an explicit
fifteen-branch family of odd-normal planes. It applies beyond this branch.
