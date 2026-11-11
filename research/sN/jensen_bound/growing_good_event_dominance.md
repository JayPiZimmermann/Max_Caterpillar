# Actual good-event dominance at arbitrary selected arity

The new `GrowingMatching.GoodEventDominance` package proves the deterministic
semantic implication for every natural selected arity k and tail size m, on
the original label space `Fin (m+k)`. No k=5 or positivity premise is imposed.

The full permutation is the actual label-to-position permutation. All k
selected weights are aggregated at the anchor; every original tail weight is
retained in position order, and the original row support remains unchanged.
The sum decomposition and position bijection come from
`GrowingMatching.ConfigurationsSums` and `ConfigurationsGeometry`.

The selected-independent prefix-cut/run proofs are reused unchanged. An
isolated dominant low-rank gap produces an opposite nonzero pair. Another
nonzero tail has a run partner, producing actual case A or B. Otherwise, original
support size at least three and selected zero sum produce two distinct selected
support labels, giving case C. These are the new actual k-arity placement and
bad-event definitions, not the old selected-five events. For k=0 or k=1, the
impossible selected-role branches are discharged by the same finite arguments;
no exceptional coefficient certificate is needed.

The placement/count package independently retains the exact selected-role
factors: one for A, k for B, and k(k-1) for C. The semantic proof assumes none of
their probability estimates. Its headline also contains no H(k,q), proper-model,
cleanliness, or run-zero-sum premise.

Primary APIs in namespace
`MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance`
have explicit k as their first argument:

- `dominant_isolated_support_bad`;
- `good_event_excludes_nonbraid_dominant`;
- `dominant_isolated_support_bad_of_tail_order`;
- `good_event_excludes_nonbraid_dominant_of_tail_order`;
- `support_three_no_isolated_dominant_of_tail_order`.

The raw-order version requires literal original tail-coordinate agreement.
The separate `GoodEventDominance.Family` leaf gives the corresponding implication
from the complement of the actual finite family `feedingBadConfigurations`;
the family may be the actual feeding-row subtype of a network.

An independent nonvacuity theorem constructs a true support-four zero-sum row
for every k. Selected coefficients are zero, tail coefficients are
`[1,-1,1,-1]`, ranks are `[2,1,3,0]`, K=2 and the isolated dominant gap is 1.
It explicitly checks k=0 and k=1 and evaluates no enormous permutation universe.

Main receipt: `growing_good_event_dominance_receipt.json` (14 exact contracts,
13 standard-axiom audits). Nonvacuity receipt:
`growing_good_event_nonvacuity_receipt.json`. Every receipt hashes its complete
project import closure and checks that it stayed unchanged during verification.
All prior selected-five, Count65, tied-point and small-matching source files
remain unchanged.
