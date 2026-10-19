# Verification record

Status: **the reduced MAX-only repository passes the complete verification gate**.

The public interface and dependency closure contain the caterpillar
construction of $\operatorname{MAX}_N$ and the results used in the paper. The
general CPWL development and archived alternative constructions are absent.

On 2026-10-19, the following command completed successfully on the reserved
compute allocation after the final Lean comment edit:

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
7ad1e4d547633aca3e08023e32bff3399a8536ca394f7a548f773cdd2f213639
```

The receipt records aggregate source digest
`5309e0d5ace2238c88342f271dff6092ab51c265977ae6d741ae91cae0e349ad`
and the SHA-256 of every checked source and manifest. Its `source_commit` is
`null` because the gate certified the working tree by content rather than a Git
revision. All 169 recorded files were rehashed after this fresh full gate;
every current hash matches the receipt and no file is missing. The certificate
therefore applies directly to the current source tree.

The paper also rebuilt and passed its link and layout checks: 17 pages, 120 Lean
links, 107 equation links (105 Lean links and two literature links), 124 distinct
declaration mappings, three proof anchors, five proof-step links, and no
overfull boxes. The corresponding source hashes are recorded in
`verification/paper.json`.
