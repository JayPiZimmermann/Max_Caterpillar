# A complete twelve-case cover for each K3 output-sign count

For every omitted label i, quadruple locality requires at least one of
the three preactivations to vanish at 1_[5]\{i}. Choose one such neuron
for each i. This gives a map from five labels to three neurons. Permuting
labels makes each fiber a consecutive block. Exchanging the two neurons
with the same output sign orders their fiber sizes. Thus only twelve
nonnegative triples of sizes summing to five are needed for each output
sign count. All zero overlaps are retained because the cases require only
the chosen zeros, with no nonzero conditions elsewhere.

The producer loads the frozen complete 42-variable formula, removes its
last same-sign weighted-score ordering constraint, and adds the five
canonical zero equations. Per-neuron sign flips used to make its first
comparison coefficient nonnegative remain compatible with zero assignments.
The stronger maximal-comparison-coefficient label normalization is not
used, since the label permutation is already used for the zero blocks.

An independent finite checker enumerates all 243 assignments for each sign
count and recovers exactly these twelve representatives. As a positive
control, the known four-core construction lies in every canonical cover:
all its quadruple values vanish. It passes all 24 augmented formulas
and the independent exact physical-network verifier.

The bounded campaign uses 15 seconds per case. Every completed case is
recorded immediately with its count triple and verdict. Solver unknown
or timeout is not an infeasibility result. Any SAT candidate is compiled
to a physical network and sent directly to the exact global verifier.
Even if every case returned UNSAT, independently checked proofs would
still be required before claiming K3 infeasibility.

All 24 cases timed out at their 15-second caps; none produced a candidate
or an infeasibility certificate. No larger campaign was run. The live mathematical
residual remains the full three-unit problem described in
`overnight_fixed_complete_status.md`. The sparse complement coordinates
in `overnight_fixed_complete_complement.md` are an exact possible future
formulation, rather than a new width result.
