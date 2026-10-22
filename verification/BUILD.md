# Verification record

Status: **the repository passes the complete verification gate**.

The public interface and dependency closure contain the caterpillar
construction of $\operatorname{MAX}_N$, the Version 2 results added on
2026-10-22, and the restored Wang–Sun formalization under `MaxNN/CPWL`
needed for the CPWL network theorems. Superseded declarations are kept in the
sources and commented as Version 1; their replacements are commented as
Version 2.

On 2026-10-22 the following command completed successfully on a local
workstation (Lean 4.4.0, mathlib cache from `lake exe cache get`):

```sh
ulimit -s unlimited && python3 scripts/verify.py
```

The verifier built `All` and `Verification.Statements`, re-elaborated all 44
exact theorem statements in `verification/main.json`, rejected `sorry`,
`admit`, project `axiom` declarations, and `native_decide`, and audited every
theorem with `#print axioms`. It found 201 Lean source files. Every theorem
uses only the permitted foundational axioms `propext`, `Classical.choice`, and
`Quot.sound`.

New checked statements (in addition to the 27 Version 1 statements):

- `maximum_width_rational`, `coefficient_rational`, `network_rational`,
  `rational_coefficients`, `compilation`;
- `quotientDim_eq`, `quotient_compression`, `factorial_le_quotientDim`;
- `max_three_network`, `max_four_network`, `max_four_identity`;
- `caterpillar_sum_affine`, `caterpillar_shared_pieces`,
  `caterpillar_shared_pieces_min`;
- `wang_sun`, `cpwl_two_hidden_layers`, `cpwl_two_hidden_layers_shared`.

The machine-readable receipt is `verification/certificate.json`, with
aggregate source digest
`b734333e8acfcab2be515c22e27af95226c7228560b156d7fe544e5411adc1ae`
and the SHA-256 of every checked source and manifest. Its `source_commit` is
`null` because the gate certified the working tree by content; the checked
Lean sources are identical to those of commit
`9eff36af7b8d9898bcfb1e2ee70b753c5efbaca6`.

The exact small-arity searches of `scripts/vocabulary_search.py`
($q_3=1$, $q_4=65$, $q_5=1136$, $s_3=1$, $s_4=3$) are computational
certificates in Python and are not part of this Lean certificate.
