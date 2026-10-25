# Source-oriented tree faces: component charges and capacity transfer

Status: complete mathematical proof, independently reviewed by the root and
both tree reviewers. This is not a new Lean theorem. It covers every
omitted/linear/hinge state of a canonical source-oriented tree unit, with
unit inner coefficients. It does not cover arbitrary original orientations
or independently signed inner coefficients.

## Conventions and the charge identity

Let T be a tree on n=N−1 nonapex labels, orient its edges away from s, and
start with head x_r−x_a. Thus a directed edge p→q carries sigma(x_p−x_q).
Assign each edge one of the three states 0, x_p−x_q, sigma(x_p−x_q).
Let F be the forest of retained hinges on the nonapex labels, and let h'
be the original head plus the linear edge terms. For a nonapex vertex v put

    kappa'_v = h'_v + outdegree_F(v),
    e_v = kappa'_v − degree_F(v) + 1.

Then

    e_v = 1_{v=r}+1_{v=s}
          + #(linear outgoing original edges at v)
          + #(omitted incoming original edges at v).                 (1)

In particular all e_v are nonnegative integers. To check the signs, write
kappa'−degree_F+1=h'−indegree_F+1 and use original indegree
1−1_{v=s}. A linear deletion charges its parent; an omitted deletion
charges its child.

For every component D of F, internal edge terms cancel on summation, giving

    h'(1_D) = sum_(v in D) e_v − 1.                                (2)

The total charge is

    sum_v e_v = #(components of F)+1.                              (3)

These formulas include isolated vertices. The apex is not a component of F;
its coefficient remains −1 and it has no comparison edge.

## Which localities can contribute

Use the common generic tied-maximum test, with a tie B of size at least3.
All such detecting localities satisfy:

1. every frozen coefficient outside B is zero;
2. an isolated tied vertex has nonzero normalized coefficient;
3. the retained comparison graph induced on B has at most two components,
   counting isolates.

For this note, call a locality **passing** only when all three necessary
conditions hold. This strengthens the earlier balance/activity passing
condition. Adding the third condition never invalidates an existing
capacity upper bound. It is essential for the transfer below: the earlier
passing condition alone can hold at the full tie even when F has several
components and the top class is zero.

The apex must be in B, since its outside frozen coefficient would be−1.
It is isolated. Condition3 consequently forces B minus {a} to be a connected
induced subtree lying in one retained component C. Every other component D
is wholly untied. Summing its zero frozen coefficients gives h'(1_D)=0,
since its hinge contributions cancel. Equations (2) and (3) then imply

    sum_D e = 1 for D≠C,          sum_C e = 2.                       (4)

Thus a fixed face can pass only if its components have exactly one charge2
component and every other component has charge1. This distinguished C is
fixed by the face, independently of B and its outside order. A different
charge pattern has zero capacity. If C is a singleton, B⊂C union {a}
would have size at most2, so it also has zero capacity in our |B|≥3 sum.
Condition (4) is necessary, not sufficient for a nonzero test.

## Exact source reduction on the active component

Because e is nonnegative integral, on C it has the form delta_u+delta_v,
allowing u=v. Reorient C away from u and give it head x_v−x_a. The resulting
canonical source unit is

    U_C = sigma(x_v−x_a + sum_(p→q away from u in C) sigma(x_p−x_q)).

This reorientation gives exactly the same preactivation on C and a. Indeed,
normalization writes a preactivation as

    sum_w kappa'_w x_w − sum_(ij in F) min(x_i,x_j) − x_a,

with the apex term shown separately. In C, (1) gives
kappa'_w=degree_C(w)−1+1_{w=u}+1_{w=v}. This is precisely the normalized
coefficient of the displayed source-u, head-v unit, since away from u the
outdegree is degree−1+delta_u. Reversing an individual hinge and adding its
linear correction gives the same identity.

For completeness, a charge1 component D has e=delta_w and reorients to
head zero with all edges directed away from w. Its preactivation is the
nonnegative shallow sum of those comparisons. Thus when (4) holds the
original preactivation decomposes globally into the active canonical
preactivation plus one such nonnegative shallow sum for each other
component. At a passing locality those other components have zero frozen
coefficients, so they contribute neither a value nor a tied-coordinate
germ. This confirms the local reduction directly, though the capacity
proof needs only its necessary passing conditions.

## Order fractions and generating-function bounds

Fix a tie B⊂C union {a}. Restrict a uniformly random outside order of all
N labels to the outside labels of C union {a}; that relative order is
uniform. If the original face passes, the smaller source unit passes in
this restricted order: its normalized coefficients and hinge adjacencies
are identical on C, the apex remains−1, and the graph condition is unchanged.
No sufficiency claim and no independent choice of generic points is needed.

Let a_U(B) denote the fraction of outside orders satisfying the strengthened
passing conditions, and define

    F_U(y) = sum_(|B|≥3) y^|B| a_U(B).

The preceding injection of allowed ties and restriction of orders give

    F_U(y) ≤ F_(U_C)(y)                                           (5)

for every y≥0. If the charge condition fails or |C|=1, the left side is zero.
This comparison loses no factorial or interleaving factor.

Apply the already reviewed full-source bounds to U_C, on |C|+1 labels.
With y_0=sqrt(3/2)−1 and tau=sqrt(7)/2,

    F_U(y_0) ≤ 1,
    F_U(1/2) ≤ tau^(|C|+1) ≤ tau^N.                               (6)

The last inequality has the stated direction because tau>1. Thus every
source-oriented face has the same capacities needed by the pure exponential
bound and the p=1/3 matching-mixture bound. In probability normalization,
(2/3)^N F_U(1/2)≤(7/9)^(N/2), with the original N throughout.

## Reduced-degree families are also closed under all face states

For a forest with arbitrary real head and unit hinge coefficients, form its
reduced forest by deleting its degree-one vertices with kappa=0. Give its
edges arbitrary omitted/linear/hinge states and adjust the head as above.
The new reduced edge set is a subset of the old reduced edge set.

Indeed, a surviving edge that met an old zero-kappa pendant still meets the
same degree-one vertex. Because that vertex had no other incident edge,
retaining its edge leaves its head and kappa unchanged; it is still a
zero-kappa pendant, so this edge is absent from the new reduced forest.
Every other new reduced edge was already an old reduced edge. Therefore
the reduced maximum degree cannot increase under face selection, for real
heads just as for integer heads.

This argument concerns genuine three-state faces of unit-coefficient
forest functions. The arbitrary-weight degree/matching theorems already
allow face selection by absorbing linear states into their arbitrary head
and keeping omitted edges in the original comparison graph with coefficient
zero. These are separate valid reasons the corresponding hypotheses remain
available for face functions; no unrestricted all-oriented-tree exponential
statement follows.

## Exact closure formula for weighted edge states

Let L contain at most one orientation of each unordered comparison, let h
be an arbitrary real linear head, and let c_ell be arbitrary real numbers.
For tau(ell) in {0,ell,sigma composed with ell}, set

    U^tau_(h,L,c) = sigma(h + sum_(ell in L) c_ell tau(ell)),
    M = {ell in L : tau(ell)=sigma composed with ell},
    h' = h + sum_(tau(ell)=ell) c_ell ell.

Then the exact function identity is

    U^tau_(h,L,c) = U_(h',M,c restricted to M)
                 = U_(h',L,c^tau),

where c^tau_ell=c_ell for retained hinge states and c^tau_ell=0 otherwise.
Both representations keep precisely the original linear-state coefficient;
in particular one must not forget c_ell when adjusting the head. The head
h' remains an arbitrary real linear form.

In the second representation the comparison graph is the original G_L,
including its zero-coefficient edges. Therefore hypotheses on its maximum
degree, matching number, pseudoforest property, or excess are unchanged.
The graph-rank test remains necessary because the actual comparison forms
span a subspace of the span of all listed graph edges. Including zero
coefficients only enlarges that upper bound; it does not assert that the
corresponding germs actually contribute. If one instead uses G_M, its
matching number may decrease, so the original matching hypothesis must not
silently be reassigned to that retained graph.

For signed inner weights these are edge-state functions as defined above;
the statement does not identify them with geometric faces of a convex
pyramid. The geometric face interpretation is used for the canonical
unit-coefficient functions. After removing biases by recession, these
identities and graph hypotheses are unchanged.

The revised paper's weighted edge-state definition, original-graph
matching convention, general reduced-degree theorem with source faces,
and component-charge proof have been checked against this note. In
particular its strengthened passing condition includes the induced graph
cap, its generating function starts at tied size3, and the charge2
singleton case is excluded before applying the smaller-arity bound.

## Reproducible checks

The independent review is `source_face_closure_independent_review.md`.
The standard-library checker `source_face_closure_check.py` tests all 7,167
source/root/edge-state cases through four nonapex vertices and all 3,899
passing ordered ties. Both its producer receipt and a fresh root replay
passed: `source_face_closure_check.json` and
`source_face_closure_root_replay.json`. These finite controls check
conventions; the arguments above prove the uniform statements.
