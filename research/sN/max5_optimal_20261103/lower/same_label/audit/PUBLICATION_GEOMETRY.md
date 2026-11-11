# Geometry needed for the six certified same-label cases

The clean paper statement is: **in the same-label, one-unique-contact-per-core
sector, an exact seven-feature positive two-core MAX5 identity cannot have
only three physical root rows.** Its short support cover is
`MINIMAL_COVER.md`. The selected six CPC refutations and independent Ethos
replays finish the arithmetic exclusions. They do not settle the full
MAX5 width problem or constitute a Lean proof.

Here is a minimal dependency list, separating the physical-network bridge
from the reduced identity theorem.

| Lemma | Role | Existing detailed source |
| --- | --- | --- |
| Homogeneous recession and signed singleton-carrier reduction | Removes arbitrary biases at unchanged widths; in the `(1,1,7)` branch with second width four gives `MAX5=ell+R+ReLU(g)+ReLU(h)`, with `ell(ones)=1` and R,g,h in the actual seven-feature span. | `research/sN/frontier5/max5_first_width_audit.md`; `notes/max5_exact/three_shared_model_audit.md` |
| First width at least nine | Justifies pruning a zero or wholly unused first feature, so the coefficient gauge loses no physical candidate. | `research/sN/frontier5/max5_first_width_audit.md` and its cited lower-bound classification and rectangle certificates |
| One-positive-core MAX4 classification | At a uniquely vanishing core, the core germ is a unit complementary-pair comparator, and the shallow remainder is the complementary pair maximum. | `research/sN/frontier5/max5_width4_results.md`, section 1; `research/sN/frontier5/max5_width4_quad_local_audit.md`; `notes/max5_exact/three_shared_model_audit.md`, sections 2–4 |
| Positive-two-core MAX4 rigidity with at most three first hyperplanes | A shared contact with at most three singular physical rows has at least one effective canonical comparator. Compatibility with its unique-contact matching requires an absent root, hence every shared contact has at least four singular physical rows. | `notes/max5_exact/local4_three_hyperplanes.md`; `notes/max5_exact/local4_one_root_audit.md`; `notes/max5_exact/local4_matching_extremality_audit.md`; matching compatibility in `notes/max5_exact/three_shared_one_each_cover_audit.md` |
| Direct omission cover | The three shared contacts require at least 3,2,2 omissions among four nonroot supports; seven omissions out of eight leave exactly the selected six support orbits. | `MINIMAL_COVER.md`, independently replayed by `minimal_cover.py` |
| Exact shallow-germ coordinates | Consolidated curvature uses positive L1 normal lengths; midpoint gradients retain the linear contribution from opposite rows. This proves the unique-contact equations. Boolean values and directional germs are necessary consequences of the all-input identity. | `notes/max5_exact/three_shared_model_audit.md`, sections 3–5; `AUDIT.md` |
| Positive two-core MAX3 with one nonroot first line | In case 277, each singleton rootless triple forces both corresponding core coefficients nonzero and equal in absolute value, including independent local complements. | `SINGLETON_AUDIT.md`; earlier `notes/max5_exact/allfive_shared_rank.md` and `shared_rank_audit.md` |

For a theorem stated directly about the residual identity, the physical
carrier reduction need only appear in the application. The unused-row
argument can still use first-width-nine minimality: if an invariant
feature were unused, the identity would use at most six such features.
Add first features `ReLU(ell),ReLU(-ell)` and form four second gates with
preactivations `ell+R`, `-ell-R`, g, h, and output signs `+,-,+,+`.
This is an ordinary no-skip width-at-most-eight realization, a contradiction.
Thus no uncounted free linear head is needed in this pruning argument.

The direct cover removes the old 431/193/387-orbit inventory and the
eight-row three-comparator-contact budget from the selected result's
logical dependency chain. C3/C4 support conditions hold automatically in
all twelve labelled survivors. The wall and rigid-contact blocks in the
selected coefficient models are likewise tautological, as checked in
`AUDIT.md`. The optional quantitative unit-normal consequences and the
broader singleton face-curvature helper are not used by the selected proof.
The local MAX4 rigidity theorem retains an upstream 288-case CPC/Ethos
certificate for one root and two nonroot first hyperplanes, so this shorter
cover does not turn the whole result into a proof without computation.

No geometric gap was found in this stated six-case sector. The existing
formula/proof manifest freezes the arithmetic package; publication must
also cite or preserve the mathematical dependencies above, especially the
first-width-nine theorem and the local MAX4 rigidity certificate. A fully
Lean-verified result would additionally need formal statements and proofs
connecting those reductions and the arithmetic certificates to the intended
network theorem; this package does not supply that bridge.

The remaining same-label support families have at least four physical root
rows (381 classes in the older cover). The other three-shared contact
distribution, four-shared and five-shared cases, and the unrestricted
width frontier are separate. Six refutations cannot be reported as an
unconditional exclusion of physical widths `(9,4)`.
