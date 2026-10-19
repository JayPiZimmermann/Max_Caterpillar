# Verification record

Status: **the reduced MAX-only repository passes the complete verification gate**.

The public interface and dependency closure contain the caterpillar
construction of $\operatorname{MAX}_N$ and the results used in the paper. The
general CPWL development and archived alternative constructions are absent.

On 2026-10-19, the following command completed successfully on the reserved
compute allocation:

```sh
srun --jobid=753647 --overlap --ntasks=1 --nodes=1 --cpu-bind=none --cpus-per-task=1 bash -lc 'cd /home/fe/jzimmermann/code/MaxCaterpillar && ulimit -s unlimited && python3 scripts/verify.py'
```

The verifier built `All` and `Verification.Statements`, re-elaborated all 27
exact theorem statements in `verification/main.json`, rejected `sorry`,
`admit`, project `axiom` declarations, and `native_decide`, and audited every
theorem with `#print axioms`. It found 166 Lean source files. Every theorem uses
only the permitted foundational axioms `propext`, `Classical.choice`, and
`Quot.sound`.

The machine-readable receipt is `verification/certificate.json`. Its SHA-256
is

```text
7402f2fbc3139ee58ebb7a10e3b6173a7fe73abd7d6293d1a4dcccd2c16b74f4
```

The receipt records aggregate source digest
`16eae06d5f72bd2b0b0353597a5b3c164b2cf77e1b4993d4398f8d0d0679f8e9`
and the SHA-256 of every checked source. Its `source_commit` is `null` because
verification was run on the completed working tree before creating the single
fresh root commit. The per-file hashes and aggregate digest bind the receipt to
that exact tree without referring to the repository history that is being
removed.

The paper also rebuilt and passed its link and layout checks: 13 pages, 98 Lean
links, 85 equation links (83 Lean links and two literature links), 102 distinct
declaration mappings, three proof anchors, five proof-step links, and no
overfull boxes. The corresponding source hashes are recorded in
`verification/paper.json`.
