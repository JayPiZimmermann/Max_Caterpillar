# Exactly three shared positive-core contacts for Max5

Status: 31 October 2026. **Open.** This note concerns the remaining
first-width-nine, second-width-four candidate, reduced to

```
Max5 = ell + R + ReLU(g) + ReLU(h).
```

Here ell has coordinate sum one, and R,g,h belong to the actual span
of seven oriented invariant first-layer ReLU features. All seven normals
have coordinate sum zero. No independent linear functions are adjoined
to that feature span. The contacts are q_i=-e_i. At exactly three contacts
both cores vanish; at the other two exactly one core vanishes.

## Complete discrete contact cover

Relabel the shared contacts as 2,3,4. There are three cases:

| Unique contacts | Mandatory root hyperplanes |
| --- | --- |
| g unique at 0, h unique at 1; same distinguished shared label | 02,12,34 |
| g unique at 0, h unique at 1; different distinguished shared labels | 03,12,24,34 |
| g unique at 0 and 1; h has no unique contact | 02,12,34 |

The first two cases exhaust the nine pairs of local perfect matchings,
with orbit sizes three and six. The third follows from compatibility of
two comparator germs of one shallow core. Core complementation adjusts
the shallow remainder and is permitted; reversal of a first feature is
not silently quotiented out.

The independently checked [one-each cover](three_shared_one_each_cover.md)
and [audit](three_shared_one_each_cover_audit.md) retain arbitrary additional
root rows, opposite rows, linearly dependent distinct normals, coefficient
zeros, and rows used only by the remainder. Their support reduction gives
387 and 269 contact-preserving support classes. With no additional root
rows, these reduce to six and twenty classes respectively. These are
necessary support classes, not network fibers or components.

## General necessary arithmetic model

`research/sN/frontier5/max5_exact_three_shared_local.py` imposes exact
comparator germs at unique contacts and the zero values at shared contacts.
Additional options impose equality on the Boolean or ternary inputs,
Boolean directional derivatives at shared contacts, and local comparator
rigidity at contacts with at most three singular physical rows or only
root singular rows.

The general model allows arbitrary remaining physical rows, including
extra roots and opposite or proportional rows. For a hyperplane represented
by a row a, its consolidated curvature is the sum, over parallel physical
rows b, of coefficient(b) times the L1 norm of b. Proportional row normals
have proportional L1 norms, so this preserves the correct magnitude while
forgetting only the irrelevant orientation of curvature. The separate
midpoint-gradient equations retain the linear contribution of oppositely
oriented rows. Thus cancellation does not manufacture free linear terms.

For the ordinary row gauge, the first nonzero normal coordinate is plus
or minus one. An optional coefficient gauge instead normalizes the first
nonzero member of the core/core/remainder coefficient triple to plus or
minus one. Known root rows retain the row gauge. A completely unused row
would contradict the established first-width-nine lower bound.

The [model bridge audit](three_shared_model_audit.md) checks the actual-span
equations, all three discrete cases, proportional boundaries, local rigidity,
and exact arithmetic. An initial implementation used integer division in
the mandatory-root midpoint expression; this was caught before any
refutation claim, replaced with multiplication by the rational one-half,
and the initial artifacts were replaced. The independent checker now
inspects the actual Z3 expressions and rejects integer-division nodes.

## Two additional hyperplane obstructions

The [hyperplane classification](polytope.md) supplies the first-wall test:
if both positive cores have nonzero consolidated curvature on a full-support
first normal with signs two versus three, the largest absolute coefficient
on the three-element side must be at least the largest on the two-element
side. The model guards this by net curvature, not individual row coefficients.

A separate odd-vector version applies to each actual core odd vector,
the sum of its first normals weighted by its feature coefficients. On its
kernel that core and its outer ReLU are even. The odd part of the remaining
identity has only one folded shallow core, so the same strict two-versus-three
obstruction applies. The helper
`research/sN/frontier5/max5_three_shared_odd_criterion.py` imports this test
without a both-used guard. This is a different consequence from the
first-wall test, and uses the strengthened linear-odd-remainder proof.

## Current arithmetic work and limits

**All 269 surviving path support classes have independent arithmetic
refutations.** Their
exact necessary models come from `max5_three_shared_path_support_probe.py`.
For the twenty minimal-root classes, an initial coefficient-gauge Z3 pass
refuted eight and timed out on twelve; CVC5 then produced trust-free CPC
refutations for all twenty, and pinned
Ethos independently checked every proof. The
[certificate note](three_shared_path_certificates.md) records source hashes,
receipts, and coverage. The simpler Boolean-plus-rigidity models suffice;
the newer odd-vector and shared-derivative constraints are not needed for
these twenty exclusions. A timeout from a different solver was never
treated as an exclusion.

The remaining 143 support classes with five physical root rows and 106
with six physical root rows also all passed CPC production and independent
Ethos replay. Their root multiplicities include opposite orientations and
are not assumed to represent distinct planes. The complete coverage and
model bridge have independent audits; the final assembly audit is checking
the pairing of all 269 support cases, frozen sources, and proof receipts.

The six minimal-root same-label families are handled by a separate lane.
The two-unique-one-core lane analyzes the all-five-zero core directly.
Its new [theorem](three_shared_two_unique.md), independently
[audited](three_shared_two_unique_audit.md), forces at least two distinct
nonroot planes with nonzero consolidated curvature in that core; opposite
rows supplying pure linear terms are retained. This excludes 354 of its
553 support classes analytically. Sixty further necessary linear models
are undergoing certificate checks, leaving 139 full two-core support
models in that lane.
Neither the three-shared case nor unrestricted Max5(9,4) is excluded by
the present note. No Lean theorem or matching second-width optimum is claimed.
