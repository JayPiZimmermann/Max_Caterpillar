# k(N) for all N: results (live)

`k(N)` = fewest general second-layer neurons over the paper's first layer (second width `k(N)+2`).
Known before: `k(3) = k(4) = 1`, `2 ≤ k(5) ≤ 4`, `k(N) ≥ 2` (N ≥ 5), upper bound `2^{O(N log N)}`
(caterpillar). Proofs: PROOFS.md.

| claim | status |
|---|---|
| **`k(N) ≥ ⌈C(N,3)/B(N)⌉ ≥ √N/2` for all N** (Theorem L): first lower bound on the second width that grows with N | proof on paper; finite steps exact-checked (`locf.py`, `check_lemmas.py`); not Lean |
| one neuron sees at most `B(N)(N−3)! ≤ (N−1)(N−2)√N/3 · (N−3)!` of the 3-locality cells | same |
| conjecture: one neuron sees `O(N²)(N−3)!` cells, giving `k(N) = Ω(N)` (ceiling of the method) | measured (max f = 6, 8, 9.75, 12 for N = 5..8); open step isolated in PROOFS.md |
| Lemma U1: exact identities ⟺ Boolean identity + per-chain cancellation (linear in d) | proof on paper |
| chain-separated neurons alone cannot give max_5 (top Möbius coefficient) | measured |
| pipeline chainlp.py → cert_exact.py: dictionary LP, exact rational solve, independent cell certificate, smalln JSON | working: N = 5, 7 neurons certified (`max5_chain7.json`) |
| upper bound for all N better than caterpillar | open; no family found yet |

Evidence levels follow .claude/skills/formalization-research. Upper-bound search status below.

## Log
- N = 6 dictionary LP (chainlp.py / chainlp2.py, measured):
  - terms(≤3 OR-basis terms, coef ±1,±2) + stars: infeasible (`lp6a.log`).
  - terms(≤2) + stars + 5% sample of "c(OR_P−OR_Q)+star": lsqr residual 7e-2, infeasible (`lp6d.log`).
  - all degree-2 atoms `σ(m_p+m_q−m_r−m_s)` (35 910 neurons, coef ±1): feasible (lsqr 2e-11);
    weighted L1 support 284 neurons, reweighting does not move it (`lp6e.log`, `lp6f.log`,
    `sup6f.json`; not certified exactly: 284 neurons too many for the cell certifier).
  - unrestricted runs over ~1M neurons exceed the 3 GB budget (HiGHS); not pursued.
