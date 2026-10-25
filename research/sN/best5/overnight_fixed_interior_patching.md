# Interior cancellation: what patches, and what does not

The unrestricted K2 target remains open. The earlier fixed-winner-sign
obstruction proves that a hypothetical two-free-term representation must
have an outer preactivation taking both signs inside at least one winner
cone. This note audits that remaining mechanism without restricting the
first hidden layer directions.

Remove biases by recession and absorb each nonzero output magnitude into
its preactivation. Refine the finite first-layer hyperplane arrangement by
all coordinate-equality walls; this is an analytical refinement and does
not assume those extra rows existed in the network. The target is linear
on every full chamber of the refinement. The shallow remainder and both
preactivations are linear on each such chamber.

## Exact chamberwise cancellation

If a preactivation has a strict sign change inside a chamber, its zero
hyperplane has an open facet there. The target and shallow remainder have
no crease there. Thus the other folded unit must have the same hyperplane,
opposite output sign, and equal absolute normal derivative. With output
signs normalized to+1,-1, the two chamber-linear forms are exactly equal
or opposite. This assertion excludes an identically zero preactivation,
which has no strict sign change or crease to cancel.

For two adjacent chambers that both contain a strict crossing, the sign
in `g1=epsilon*g2` cannot change. Continuity across their common facet
would otherwise force both functions to vanish on an open subset of that
facet. Their linear forms on the first chamber would then be multiples
of the facet normal, hence have fixed sign throughout the chamber, a
contradiction.

Moreover, if an interior zero wall reaches the relative interior of a
common facet, the neighboring chamber must also contain a strict crossing.
The restriction to the facet cannot vanish identically by the preceding
argument. Near an intersection point it takes both signs along the facet,
and continuity carries both signs into the neighboring chamber.

Consequently epsilon is constant on every connected component of mixed
chambers, and the shallow function `g1-epsilon*g2` has zero jump across
every facet traversed by that component. The independent proof agent
checked the strict-crossing, continuity, and zero-boundary qualifications.
This does not prove that the components connect every winner region or
that their boundaries along arrangement intersections can be removed.

## A precise obstruction to naive global continuation

Let the coordinates be a,b,c,d,e and define

```
g = max(a,b)-c,
h = sigma((a+b+c+d)/4-e),
k = g+h.
```

All three functions are homogeneous shallow. On the whole winner cone
`C_e={e>max(a,b,c,d)}`, h=0, so g=k and
`sigma(g)-sigma(k)=0`. The common preactivation nevertheless takes both
signs there: compare(1,0,0,0,2) with(0,0,1,0,2).

Neither folded function is shallow. Along a=b=0 with d=0,e=2, its normal
jump is nonzero when c=-1 and zero when c=1. Both points lie in C_e, where
h vanishes in a neighborhood, so this varying jump applies to both folds.
A shallow function would have one constant consolidated jump on a=b.
Outside C_e, at(1,1,1,1,0), the two folded values are0 and1. Thus all the
mixed chambers inside one entire winner cone can agree without giving a
global proportionality of the preactivations or folds.

This example is not a representation of max5. It refutes only the proposed
inference from one-cone cancellation to global equality. A valid max-specific
patching theorem must additionally use compatibility across winner cones
and the convex target; it cannot discard those hypotheses.

## Complete comparison first layer: the remaining exact domain

For the complete span of linear functions and all `sigma(x_i-x_j)`, the
first-layer arrangement is the braid arrangement. The target has no
interior wall in any of its120 chambers. The existing complete K2
certificate excludes all two-free-term identities in this span. A
three-free-term construction would therefore match the fixed16-feature
second-width lower bound five via the established two-carrier bridge.
This would not establish unrestricted second-width minimality.

The complete K3 vanishing-flat domain contains10,703,779,537 unordered
covering triples, at least89,198,163 orbits under label permutations before
output signs. The exact count uses the previously proved15-circuit and an
integer subset transform; a second avoidance-transform implementation
checks the ordered count. This domain is not being exhaustively searched.

The all-neurons-conforming branch is closed by the literature theorem
recorded in `overnight_fixed_complete_braid_closed.md`. The live constructive
restriction instead allows a positive and negative core neuron to cancel
an interior wall with equal or opposite preactivations on that entire
chamber. The remaining neuron must have a weak fixed sign. This is a
closed finite disjunction of linear equations and inequalities, with no
bounds on real coefficients. Matching the Boolean rays then proves exact
global equality because the entire output is linear on every braid cone.
The independent global verifier remains the final gate.

Genuine three-way proportional cancellation is excluded from that
constructive model and remains part of the full K3 residual. In particular,
a timeout or even a solver-UNSAT answer to the pair-only model cannot be
reported as a lower bound for the complete comparison layer.
