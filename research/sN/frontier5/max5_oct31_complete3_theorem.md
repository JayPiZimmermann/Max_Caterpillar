# Exact residual minimum four in the complete comparison space

Status: 31 October 2026. **Proved by audited mathematical reductions and
independently checked finite proof certificates.** This is not a new
Lean formalization and not an unrestricted first-direction theorem.

## The theorem

Let V be the fourteen-dimensional space spanned by the ten functions
ReLU(x_i-x_j), i<j, and the four differences x_i-x4, i<4. For any anchor
a, the minimum K in an identity

```
Max5(x)-x_a = R(x) + sum_{k=1,...,K} d_k ReLU(g_k(x)),
R,g_k in V,
```

is **exactly four**. All real coefficients are permitted. Allowing affine
constants does not lower the minimum: homogeneous radial recession
removes them without increasing the number of folded terms.

The known bowtie construction supplies four terms and a remainder in V;
see `construction_frontier.md` and `../best5/netB_10_6.json`. Its anchor
change to a different a only adds a linear difference to R.

For the lower bound, absorb the magnitude of every nonzero d_k into
g_k and allow zero cores to pad a formula with fewer terms. Three cores
have either a common output sign or one of the two mixed sign counts.
Same-sign cores are individually braid conforming: on each braid
chamber their common-signed curvature cannot cancel, since R and the
target are linear there. The published braid-conforming Max5 obstruction
excludes such a formula, regardless of the number of conforming terms.
Its use and the conversion of a shallow remainder are explained in
`../best5/overnight_fixed_complete_mixed_lemma.md`.

Both mixed sign counts are now completely excluded:

| Output signs | Exhaustive independently checked package |
| --- | --- |
| (+,+,-) | `max5_oct31_complete3_p2_manifest.json`: 35 CPC/Ethos cases |
| (+,-,-) | `max5_oct30_complete3_zero_p1_manifest.json`: 35 CPC/Ethos cases |

Each manifest reports `ALL_35_INDEPENDENT_ETHOS_PASS`, with no missing
case. Source-level model audits prove necessity of the encoded formulas;
the proof objects establish their unsatisfiability. The manifests pin
the original exact formulas, proofs, independent checker receipts,
checker binary, and mathematical dependencies. The proof covers
arbitrary real coefficients, zero degeneracies, ties, and every input.
No finite coefficient alphabet, approximate equality, or training set
is used in this lower bound.

## Why the finite cover is exhaustive

The common-translation-invariant functions in V are linear on the 120
braid chambers and determined by the thirty nonempty proper Boolean
rays. At most three cores cannot all cross the interior of one chamber:
local triple and quadruple tie constraints, followed by a third Boolean
difference, give a contradiction. Thus any interior crossing is an
opposite-output pair with equal or opposite chamber-linear forms.
The corresponding closed disjunction and Boolean-ray identities form
an exact finite real linear-arithmetic model. This completeness step
is crucial; pair cancellation is not assumed for arbitrary networks.

Local Max4 comparator rigidity supplies a normal form whenever exactly
one core vanishes at a four-way top tie. The normalized branch is
independently refuted for each mixed sign count. Therefore at every one
of the five four-way ties at least two cores vanish.

For (+,+,-), the exact zero masks at those five ties form 34 symmetry
orbits: one all-zero case and 33 remaining cases. The unique-carrier
normalization plus these 34 cases gives the 35-case proof package.

For (+,-,-), the same 34 shared-zero orbits occur, with output signs
distinguishing their interpretation. Whenever the positive core is
nonzero at a four-way tie, the two negative cores must supply a Max4
germ. A separate exact local classification shows that their four
triple-tie zero-count patterns, up to exchange, are only
(shared, first-only, second-only) = (0,0,4), (0,2,2), or (1,1,2).
These necessary constraints make the 34 remaining cases tractable.
Six excluded local patterns have independent CPC/Ethos proofs and the
three admitted patterns have exact rational all-input witnesses.

Independent assembly audits:

* `max5_oct31_complete3_p2_assembly_audit.md`;
* `max5_oct30_complete3_zero_p1_package_audit.md`;
* `max5_oct30_complete3_zero_local4_audit.md`.

This is a use of fiber analysis to prove a lower bound: the hypothetical
solution fiber is projected to exact zero-pattern strata; the cover is
proved complete; every stratum is refuted. Connectivity of a collection
of already known solutions would not suffice.

## Physical hidden-width consequences

Suppose the first hidden layer consists of invariant coordinate-comparison
features and an independent signed carrier pair ReLU(ell),ReLU(-ell),
where ell(ones)=1. The signed-coordinate cost theorem identifies physical
second hidden width with two plus the residual cost in the actual
invariant first-feature span. That span is contained in V, and
ell-x_a is an invariant linear form. Therefore:

**Every exact Max5 realization over such a first dictionary needs at
least six second hidden neurons, regardless of the number of comparison
features or their orientations.**

The bowtie dictionary attains six at first width ten. Adding arbitrary
coordinate comparisons while retaining the signed carrier can never
reduce that minimum. In particular the full sixteen-neuron dictionary
realizing V plus a signed anchor has minimum second width exactly six.
The theorem gives a lower bound for every other such fixed dictionary;
it does not claim every fixed dictionary admits a six-neuron completion.

There is also a weaker consequence without a signed-pair hypothesis.
If every nonzero invariant first row is a coordinate difference, a
common-translation tail has its remainder and all free cores in the
complete comparison-plus-linear space. It needs at least four free
second neurons, and the target translation slope requires a separate
passing neuron. Hence **second width is at least five for this entire
root-invariant class, at every first width**, even with arbitrary
noninvariant carrier directions.

Multiple independent carriers may leave different free intercepts in
the two tails, so the last argument does not add two passing costs to
one tail. Arbitrary nonroot invariant directions are not in V. These
are the two remaining ways in which an unrestricted smaller network
could evade this theorem. The unrestricted minimum second width remains
between four and six; at first widths 10, 11, and 12, the same interval
remains in force unless another theorem separately applies.

The residual exclusion extends to every Max_n with n>=5 in the analogous
comparison-plus-linear space. Retain five coordinates and send the
others jointly to negative infinity. Each inner function becomes
eventually a*t+b(x): positive-slope folded terms enter the remainder,
negative-slope terms disappear, and zero-slope terms remain. No new
comparison between retained coordinates appears and the number of
remaining folds cannot increase. Common-translation normalization and
radial recession produce the excluded Max5 three-core identity.
The general restriction proof is
`max5_first12_missing_general_corollary.md`; here the completed stronger
Max5 theorem removes its missing-edge hypothesis.

## Software and replay

The finite existence model is implemented, not merely asserted decidable.
The producers use unbounded real variables and all braid chambers;
the case audits check the finite symmetry cover and each frozen source.
They decide this declared first-function-space problem, not arbitrary
first-layer directions at a given architecture.

To verify the completed package artifacts and prior independent receipts:

```
python3 research/sN/frontier5/max5_oct31_complete3_p2_manifest.py
python3 research/sN/frontier5/max5_oct30_complete3_zero_p1_manifest.py
```

To independently replay an individual CPC proof against its original
formula, use the pinned checker driver:

```
python3 research/sN/frontier5/max5_first10_ethos.py --case CASE_STEM
```

The two manifest checks do not themselves constitute a new Ethos replay;
they verify that the archived proofs, formulas, and successful replay
receipts agree. The independent proof replays have all already passed.
Historical full-model timeouts and coarse-cover timeouts remain recorded
as failed search routes and are not used as exclusions.
