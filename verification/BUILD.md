# Verification record

Status: **the repository passes the complete verification gate**.

The public interface and dependency closure contain the caterpillar
construction of $\operatorname{MAX}_N$, the Version 2 and Version 3 results
added on 2026-10-22, the restored Wang–Sun formalization under `MaxNN/CPWL`,
and the Koutschan–Moser–Ponomarchuk–Schicho representation. Superseded
declarations are kept in the sources and commented as Version 1 (or 2);
their replacements are commented as Version 2 (or 3).

On 2026-10-22 the following command completed successfully on a local
workstation (Lean 4.4.0, mathlib cache from `lake exe cache get`):

```sh
ulimit -s unlimited && python3 scripts/verify.py
```

The verifier built `All` and `Verification.Statements`, re-elaborated all 65
exact theorem statements in `verification/main.json`, rejected `sorry`,
`admit`, project `axiom` declarations, and `native_decide`, and audited every
theorem with `#print axioms`. It found 239 Lean source files. Every theorem
uses only the permitted foundational axioms `propext`, `Classical.choice`, and
`Quot.sound`.

Statements added on 2026-10-22 (in addition to the 27 original ones):

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
`1e4bae2059e93e22671285562e6ab84281639860b8af32d64367be9d08b78f87`
and the SHA-256 of every checked source and manifest. Its `source_commit` is
`null` because the gate certified the working tree by content; the checked
Lean sources are identical to those of commit
`8b4d74ab66f429fc454c8349ade514bc3775f557`.
