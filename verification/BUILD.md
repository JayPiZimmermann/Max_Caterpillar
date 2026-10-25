# Verification record

Status: **historical verification receipt; the current cleanup needs a new gate**.

The 122-statement receipt below predates the consolidation into
`MaxCaterpillar/Count/`, `MaxCaterpillar/Dimension.lean`, and
`MaxCaterpillar/Retained.lean`. Its source hashes do not certify the current
sources. The cleanup and research checkpoint preserves this receipt as
historical evidence; its public manifest and exact-statement gate still need
to be reconciled with the surviving declarations. See
`research/sN/cleanup/PROGRESS.md` for the current build status.

## Scoped proof-refactor check, 25 October 2026

The lower-bound simplification and finite face-elimination proof were rebuilt
through `All`. Exact checks preserve the nine public lower-bound statements,
dictionary sufficiency, and the class identity, and verify the new relative
face-elimination lemma and the historical compatibility statement. The checked
axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
See the [scoped receipt](../research/sN/simplify/lower_public_refactor/receipt.json)
and [exact statements](../research/sN/simplify/LowerBoundStatements.lean).
This scoped audit does not replace the historical full-manifest certificate.
The initial broad build was interrupted under memory pressure; the successful
retry compiled the generated cell modules two at a time before rebuilding `All`.

The public interface and dependency closure contain the caterpillar
construction of $\operatorname{MAX}_N$, the Version 2–4 proofs,
the restored Wang–Sun formalization under `MaxNN/CPWL`,
and the Koutschan–Moser–Ponomarchuk–Schicho representation. Superseded
declarations are kept in the sources and commented as Version 1 (or 2);
their replacements are identified by their version and proof route.

On 2026-10-24 the following command completed successfully on a local
workstation (Lean 4.4.0, mathlib cache from `lake exe cache get`):

```sh
ulimit -s unlimited && python3 scripts/verify.py
```

The verifier built `All` and `Verification.Statements`, re-elaborated all 122
exact theorem statements in `verification/main.json`, rejected `sorry`,
`admit`, project `axiom` declarations, and `native_decide`, and audited every
theorem with `#print axioms`. It found 303 Lean source files. Every theorem
uses only the permitted foundational axioms `propext`, `Classical.choice`, and
`Quot.sound`.

The latest gate includes the simplified rational projection and third mixed
difference proofs, the reduced-degree forest bound, its caterpillar/rooted-star
corollary, and the existence and tree-model bridges. The unrestricted
all-tree cubic certificate and the exploratory upper-bound searches are
separate research results, not claims covered by this Lean receipt.

Statements added on 2026-10-22 (historical list, in addition to the 27 original ones):

- `maximum_width_rational`, `maximum_width_one_basis`, `coefficient_rational`,
  `network_rational`, `rational_coefficients`, `compilation`;
- `quotientDim_eq`, `quotient_compression`,
  `quotientDim_add_two_le_secondWidth`;
- `max_three_network`, `max_four_network`, `max_four_identity`;
- `caterpillar_sum_affine`, `caterpillar_shared_pieces`,
  `caterpillar_shared_pieces_min`, `card_imageSets_le_sum_choose`;
- `wang_sun`, `cpwl_two_hidden_layers`, `cpwl_two_hidden_layers_shared`;
- public interface (`Theorems.lean`): `caterpillar_net`, `caterpillar_expansion_choose_le`,
  `caterpillar_expansion_exponential`, `caterpillar_expansion_quadratic`,
  `caterpillarDim_ge`, `caterpillarDim_eq`; `caterpillar_count_lower`,
  `caterpillar_choose_three_le`, `caterpillar_count_exponential`,
  `caterpillar_count_exponential_pow`, `factorial_le_quotientDim`;
- `kmps_of_continuous_selection`, `kmps_pieces`,
  `cpwl_two_hidden_layers_pieces`;
- `exists_rat_caterpillarExpansion`, `caterpillar_sum_affine_rational_pieces`,
  `caterpillar_shared_pieces_rational_pieces`,
  `cpwl_two_hidden_layers_shared_rational`,
  `cpwl_two_hidden_layers_pieces_rational`.

The machine-readable receipt is `verification/certificate.json`, with
aggregate source digest
`98964bb97528391ed2b499ac7f971b21651e55f91a0cc9a7f699ec2b649fac33`
and the SHA-256 of every checked source and manifest. Its `source_commit` is
`null` because the gate certified the working tree by content. This receipt
does not assert that the checked sources have been committed or pushed.
