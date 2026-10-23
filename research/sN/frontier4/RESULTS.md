# Width frontier for max_4 (and max_3) with two hidden layers — results

Model: `F(x) = Σ_k d_k σ(Σ_j W_kj σ(a_j·x))`, zero biases, no linear/skip term, every neuron
counts. Proofs: `PROOFS.md` (this directory). Evidence levels follow
`.claude/skills/formalization-research`.

## Live claim (N = 4) — PROVED (paper) + CERTIFIED (construction)

**`(h1, h2)` computes `max_4` iff `h1 ≥ 6` and `h2 ≥ 3`.** The Pareto frontier is the single
point `(6, 3)`; `h2*(h1) = ∞` (infeasible) for `h1 ≤ 5`, `h2*(h1) = 3` for `h1 ≥ 6`. One pair is
minimal in both widths; there is no trade-off.

| h1 | h2*(h1) | lower bound | upper bound | status |
|---|---|---|---|---|
| ≤ 3 | infeasible | Lemma S + C3 (`|J0| ≥ 2`, `|J±| ≥ 1`) give `h1 ≥ 4` | — | proved |
| 4 | infeasible | Lemma S: `|J0| = 2` forces `|J±| ≥ 2` | — | proved; fit `(4,4)` stalls at 0.65 (measured) |
| 5 | infeasible | Lemma S + Lemma M (monomial lemma) + C3 | — | proved; fits `(5,3)`, `(5,4)`, `(5,5)` stall at 0.31, 0.24, 0.20 (measured) |
| 6 | 3 | Theorem 1 (`h2 ≥ 3`, any h1) | `net_N4_6_3.json` | **certified** (exact, 84 leaf cones, 0 failures) |
| ≥ 7 | 3 | Theorem 1 | padding of `(6,3)` | proved |

Answers to the posed questions:
- `h2 = 1` and `h2 = 2` are impossible for **every** `h1` (Theorem 1; valid for all `N ≥ 3`).
  Measured control: fits `(6,2)`, `(8,2)` stall at 0.31, 0.35.
- Minimal `h1 = 6` (adapting best5 H1 alone gives only `h1 ≥ 4`; the extra ingredients are
  Lemma S, a spanning condition from the translation asymptotics, and Lemma M).
- The best5 caterpillar-free nesting `max(max(x0,x1), max(x2,x3))` with first layer
  `x0-x1, x2-x3, ±x1, ±x3` is optimal in both widths; the paper's caterpillar net `(11,5)` is not.

## N = 3 (sanity check) — PROVED + CERTIFIED

Feasible iff `h1 ≥ 4`, `h2 ≥ 3`; frontier `{(4, 3)}`. Lower bounds: Theorem 1 and Lemma S.
Construction `net_N3_4_3.json` (first layer `x0-x2, x1-x2, ±x2`;
`F = σ(σ(x2)+σ(x0-x2)) - σ(σ(-x2)) + σ(σ(x1-x2)-σ(x0-x2))`), certified exactly (12 leaf cones).

## What transfers to N = 5

| statement | N = 5 consequence | status |
|---|---|---|
| Theorem 1 (`h2 ≥ 3`, all N ≥ 3) | `h2 ≥ 3` (was `≥ 2`), total `h1 + h2 ≥ 10` (was 9) | proved |
| Lemma S (`|J0| + |J±| ≥ N`) | nothing beyond best5's `h1 ≥ 7` | proved |
| Cell condition (Lemma M generalized) | `h1 = 7` forces `(1,1,5)`; then no `J0` made only of root rows `±(e_i-e_j)` works: all 2304 oriented C3+C4 root families fail | exact check per family (`cellcond.py`, `logs/cellcond_N5_m5.log`) |
| same, `J0` with 3-support rows (families `{01,02,034,13,24}`, `{01,02,123,124,34}`) | all 288 + 2592 instances with integer coefficients in [-3,3] fail (`logs/cellcond_gen_B3.log`) | measured (coefficient grid only) |
| structure of passing root families (C3/C4 dropped) | m = 4: exactly the 5 stars `x_k - x_i` pass; m = 5: exactly the 60 families star + one extra root pass (`logs/cellcond_N5_noC3.log`) | exact per family |
| `h1 ≥ 8` for N = 5 | **conjecture**. Route: prove 'cell condition ⇒ `J0` contains a full star `{x_k - x_i : k ≠ i}`' for arbitrary real rows (true for N = 4, m = 3 by Lemma M; matches every exact N = 5 root check). With a star, C3 on the four 3-sets avoiding `i` needs ≥ 2 more rows, so `|J+| = 1` forces `|J0| ≥ 6`, and `h1 ≥ min(1+1+6, 2+2+5) = 8` | open |

## Files

- `PROOFS.md` — complete proofs (Lemmas 0′, T, S, C3, M; Theorems 1–3; N = 3; N = 5 notes).
- `net_N4_6_3.json`, `net_N3_4_3.json` — exact networks; `cert.py` (copy of `best5/cert.py`,
  exact rational cone decomposition) prints PASS for both.
- `fit.py` (copy of `best5/fit_B.py`), `queue1.sh`, `logs/fit_h*_s1.log` — measured scan
  (2000 sphere points, 400 restarts or 300 s per width pair, seed 1). Reached `9.8e-10` at
  `(6,3)` (limited by the `1e-6` ridge), and ≥ 0.2 at every pair the proofs exclude.
- `cellcond.py`, `cellcond_gen.py` — exact cell-condition checks (N = 4 controls, N = 5 probes).

## Reproduce

```
PY=research/sN/dfs/h4-general-neurons/venv/bin/python
cd research/sN/frontier4
$PY cert.py net_N4_6_3.json; $PY cert.py net_N3_4_3.json      # PASS, PASS
$PY cellcond.py 4 3 2000                                         # 0 of 96 pass (Lemma M control)
$PY cellcond.py 5 5 3000                                         # 0 of 2304 pass
$PY cellcond_gen.py 3 3000
```
