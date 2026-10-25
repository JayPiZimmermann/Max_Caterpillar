# Boundaries of direct regrouping and fixed-carrier completion

The live target is a five-free-term P4 identity, compiling to `(9,7)` and
matching the certified fixed-first-layer lower bound. None of the tests
below produced a smaller construction. The general five-term question
remains open. These records prevent repeating restricted construction
routes; they are not additional network-width theorems.

## Regrouping the existing twelve free terms

We tested replacing any proper subset of two through eleven fixed weighted
terms of `overnight_fixed_cross_net9_14_simple.json` by one arbitrary signed
outer ReLU in W7, plus an arbitrary W7 remainder. The prospective replacement
coefficients were unrestricted real numbers.

A braid-cone-only curvature test was too weak: all 4,082 subsets passed.
Only the first three existing terms create hyperplanes inside braid cones;
those hyperplanes cancel in the full identity. We therefore used the 54
full first-layer activation cells, where every W7 preactivation is linear.
A single signed ReLU can have at most one crossing hyperplane on each cell,
and its nonzero curvature has the same sign on every cell.

This necessary test rejects 3,526 subsets for multiple hyperplanes and 518
for inconsistent curvature signs. Of the 38 remaining subsets, exact
linear gradient compatibility rejects 23. Eleven others force finitely
many possible replacement preactivations (34 in total); all fail the
linear-remainder equations on the Boolean rays. Four two-unit subsets
retain eight affine families of dimensions one through three. Closed
sign tests for those families terminate in 36 nodes with rational Farkas
contradictions. There is no coefficient box or positive margin.

The calculations and rational witnesses are preserved in the three
`overnight_fixed_p4_regroup*` stages and
`overnight_fixed_p4_regroup_remaining.json`. They have not received the
separate full independent replay used for the main K4 theorem. Treat this
as an exact-arithmetic producer exclusion of a restricted regrouping route,
not as an independently certified general lower bound. Reopening requires
changing several old terms together, changing their coefficients, or using
a replacement involving more than one new outer ReLU.

## Natural positive carriers with two arbitrary negative corrections

The smaller continuous completion tests fix three positive carriers and
allow both negative preactivations and the linear remainder to vary freely.
The correction has a particularly transparent geometric description:

```
R+σ(h1)+σ(h2) = max(R,R+h1,R+h2,R+h1+h2).
```

Its four planes form a translated parallelogram in the feature coefficient
space. Each full-dimensional linear region of the correction must be served
by one plane. This is stronger than counting crossing hyperplanes separately
on each first-layer cell.

The simple carriers `(a-c,a-d,q-r)` fail exact continuous gradient
compatibility. Thirty-two nearby carrier choices were a bounded diagnostic,
not an exhaustive coefficient domain; no further enlargement of that list
is planned. Some left affine families for the correction and one exhausted
a declared 5,000-node direct DFS budget. Eight remaining choices were then
resolved by the independently checked five-patch certificate described in
`overnight_fixed_p4_fivepatch.md`. That certificate is the stable, smaller
proof route for those eight choices; the earlier larger diagnostics remain
as provenance.

## Current constructive branch

All five preactivations are now variable in an unbounded-real incidence
model. On each first-layer cell, the target is a linear function plus at
most one known ReLU wall. Target-wall groups may contain several neurons;
their signed amplitudes sum to the target amplitude. Other walls cancel in
positive/negative pairs, or in the later extension by a 2:1 three-unit
merge. Unmatched neurons have fixed sign on the complete cell cone.
Every incidence choice imposes only linear real equations and inequalities.

This is a constructive restriction. General multiway spurious groups with
arbitrary ratios are not covered. The pair-only model for three positive
and two negative units returned SMT UNSAT in 36.6 seconds; that is a
restricted solver diagnostic, not a certified five-term impossibility.
The known `(10,6)` network is reproduced as an exact SAT positive control
and passes the independent global checker. In the known `(9,14)` network,
all multiway groups remaining after pair cancellation consist of one positive
full-sized gradient and two negative half-sized gradients. This motivates
the 2:1 extension.

All possible positive-output counts from one through five are construction
regimes, not assumed conclusions. A completely negative core is impossible
on a first-layer cell with the target's positive curvature. A successful
SMT proposal is accepted only after its rational network passes the existing
full-domain checker. A timeout is neither a refutation nor a construction.
Z3 is installed only under `/tmp/overnight_fixed_z3`; the version and exact
SMT input hashes are recorded in the receipts.
