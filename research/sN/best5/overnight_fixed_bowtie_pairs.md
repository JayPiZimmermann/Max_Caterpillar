# Fixed10 optimality from locality and singleton/pair rays

The matched result is unchanged: the first hidden layer in
`netB_10_6.json` has optimal second hidden layer width six, over arbitrary
real weights and signed outputs, with arbitrary biases handled by the
recession argument. The mathematical model bridge, exact locality
equations, exhaustive flat coverage, and six-neuron construction remain
those of `overnight_fixed_bowtie.md`.

This new independently checked route reduces the extra conditions used
in the lower bound. The original proof eliminated the eight-dimensional
first-layer remainder from all thirty nontrivial Boolean rays, leaving
22 equations. It is enough to use the fifteen singleton and pair rays.
Their feature-evaluation matrix has rank eight, leaving only seven
equations. Together with the 26 locality equations, this gives 33
conditions rather than 48. The original checked artifacts are unchanged.

Write `a_S=abs(g(1_S))` for one outer preactivation. The seven expressions
used, in order, are

    -a_0-a_1-a_2+a_01+a_02,
    -a_0-a_3+a_03,
    -a_0-a_4+a_04,
    -a_1+a_12+a_14,
    -a_2-a_3+a_23,
    -a_2-a_4+a_24,
    -a_1-a_3-a_4+a_13+a_34.

Their signed sums over the outer neurons must respectively equal
`(-2,-2,-2,0,-2,-2,-2)`. The reference coordinate is label one, as in
the original fixed10 certificate. Each displayed combination annihilates
the remainder and every linear contribution from the preactivations.

All 30,041 unordered nonzero flat triples, including repeated flats,
and all eight output-sign assignments are checked again on this smaller
system. The resulting complete proof has 239,996 rational cone witnesses
and 332 closed-sign trees, totaling 126,869 splits. No signs are assumed
strict, and coefficient magnitudes are unrestricted. As before, candidates
with fewer nonzero outer terms are covered by splitting a nonzero term
into identical scaled copies. The zero-term case fails the fifth mixed
difference.

The independent checker passed all 240,328 cases in 118.64 seconds. It
reuses only the standard-library exact arithmetic checker. Before checking
any proof, it replaces the fifteen discarded ray equations by `0=0`.
Cone witnesses must explicitly use only retained indices. Every compressed
tree system must have exactly the same rational row space as the 33
retained direct equations, after which every closed-sign branch and leaf
is checked. Thus omitted conditions cannot enter through row reduction.

This is a complete finite certificate on the same original real-parameter
domain, not a Lean theorem. To reproduce the independent check:

    python3 overnight_fixed_bowtie_coverage.py
    python3 overnight_fixed_bowtie_pairs_verify.py

The new producer first reuses old cone proofs already involving only
retained rows, then produces 967 replacement cone proofs and 332 sign
trees. The producer's numerical LP choices carry no trust: the new checker
validates every displayed rational relation independently. The matching
upper construction is unchanged and retains its independent global
network verification and short algebraic proof.
