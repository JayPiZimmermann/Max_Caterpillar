# Refutation attempt: independent recomputation + counterexample search

Producer: `search.py` (own numpy Adam + scipy LM fitter, independent of `../fit.py`),
`evalnet.py`. Python: `research/sN/dfs/h4-general-neurons/venv/bin/python`, seed 7, 450 s/run.
Log: `search.log`. Validation: max relative error on 20000 fresh points.

| N | (h1,h2) | bias | best val maxrel |
|---|---|---|---|
| 3 | (4,3) control | 0 | 3.3e-09 |
| 4 | (6,3) control | 0 | 2.8e-07 |
| 3 | (3,3), (3,6) | 0 | 0.57 |
| 3 | (6,2) | 0 | 0.21 |
| 3 | (10,2) | 1 | 2.6e-03 (radii 0.2-3 only) |
| 4 | (5,3), (5,6), (8,2) | 0 | 0.29, 0.18, 0.32 |
| 4 | (5,4) | 1 | 4.8e-15 on radii [0.2,3]; 0.71 at radius 10, ~1.0 at radius 100+ |

The biased (5,4) N=4 fit is exact on a bounded ball only (biases emulate a linear term
locally); it is not a counterexample on R^N, consistent with the recession-function argument
(Hertrich et al. Prop 2.3). Scope caveat: the frontier claims are for all of R^N; on bounded
domains with biases they do not hold.
Both JSON networks: algebra rechecked by hand, max rel err ~5e-16 on 1e6 points incl. ties,
`../cert.py` re-run PASS.
