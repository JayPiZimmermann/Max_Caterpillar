# Best exact two-hidden-layer ReLU networks for max_5 — results (live file)

Live claim / status (update after every step):
- Model A (paper first layer Φ, 16 features): best CERTIFIED h2 = 6. Theorem A (PROOFS.md):
  the optimum is exactly k(5) + 2, k(5) = least number of free neurons in
  max_5 = R + Σ d_k σ(G_k) over pair features. Known 2 ≤ k(5) ≤ 4, so 4 ≤ h2_A ≤ 6.
- Running: exact exhaustive search for k(5) ≥ 3 (`k2_exact.py`, 3-locality germ equations,
  certified LP pruning). Status: in progress (see bottom).
- Any first layer (model B): certified (10, 6); proved h1 ≥ 7 (Theorem H1), h2 ≥ 3
  (frontier4 Theorem 1, valid for all N ≥ 3), h1 + h2 ≥ 10.

## Frontier table

| model | h1 | h2 | status | file |
|---|---|---|---|---|
| A (paper Φ, all neurons counted) | 16 | 6 | CERTIFIED (exact, all cells) | `netA_h2_6.json`, `certA_h2_6.log` |
| A lower bound | 16 | ≥ 4 | PROVED (Theorem A + k(5) ≥ 2) | PROOFS.md, `logs/k1_vanish.log` |
| A, h2 = 5 | 16 | 5 | OPEN (equivalent to k(5) = 3) | — |
| B (any first layer) | 10 | 6 | CERTIFIED | `netB_10_6.json`, `certB_10_6.log` |
| B lower bound h1 | ≥ 7 | any | PROVED (Theorem H1) | PROOFS.md, `logs/supports.log` |
| B lower bound h2 | any | ≥ 3 | PROVED (frontier4/PROOFS.md Theorem 1) | ../frontier4/PROOFS.md |
| C (total h1+h2) | | 16 | CERTIFIED (10,6); lower bound 10 PROVED | |

## Negative / instrument results (do not repeat)
- "h2 = 5 exact fit" `logs/fitA_h5_s21_SPURIOUS_noval.log` (train rel 7.5e-10, no validation):
  REFUTED — fresh max abs error 0.81; uses no σ(±x0) feature, fails on the diagonal.
- Validated gradient search (`fit_B.py`, LM + variable projection) finds only closure-type
  near-solutions with huge weights (error concentrated on a set of measure ~1e-4, fails on
  t·1, t<0); e.g. `logs/fitA_h6_s11_weakval_closure_artifact.log` (4 effective neurons!).
  With ridge 1e-6 and 120k validation points, 260 restarts (50 min) found no exact h2 = 6
  network even though one exists (`logs/fitA_h6_s12_reg.log`). Conclusion: random-restart
  fitting is NOT a reliable instrument here; its failure at h2 = 5 is no evidence.
- MILP (HiGHS, ray/set-function formulation `milp_k.py`) did not find the known K = 4
  identity within 20 min: abandoned.
- Plain cell-by-cell LP branch-and-bound (`bnb_k.py`) has no early pruning (6^depth nodes).

## Step log
1. Certified (16,6) model A and (10,6) model B networks (`cert.py`, exact Fourier–Motzkin cells;
   negative control with a perturbed output weight FAILS as expected).
2. Proved Theorems A, H1, H2 (PROOFS.md); imported Theorem 1 (h2 ≥ 3) from frontier4.
3. Exact reformulation of k(5) via set functions v(S) = g(1_S) and locality germs
   (PROOFS.md §k-search); flats of vanishing patterns: 32753 (`flats_loc.py`), complete
   coverage pairs: 97961 flat pairs (`cover_pairs.py`), 1193 up to S5 and swap.
   Soundness test on pairs of neurons of the known identity: PASS (`test_k2_sound.py`,
   `logs/test_k2_sound.log`).

## Literature (details and page references: `lit/LITERATURE.md`, compiled by a sub-agent from the
## arXiv texts in `lit/`; "derived" = widths counted from the construction, not stated by authors)
- Bakaev–Brunck–Hertrich–Stade–Yehudayoff, "Better neural network expressivity: subdividing the
  simplex", STOC 2026, arXiv:2505.14338v3, Sec. 2.1 Eq. (2): exact max_5, two hidden layers; widths
  not stated; derived (11, 9) with skip connections, about (≤21, ≤11) without.
- Rueß et al., arXiv:2607.21651v2, Thm 1.1 / App. C: exact; generic bound (20, 1080) (not optimized).
- Wang–Basu, arXiv:2608.25221v1, Thms 2.1/2.3: exact; derived first width 10 (with skips), second
  width 180 (Thm 2.3).
- Brunck–Hertrich–Rueß–Stade–Yehudayoff, "Two ReLU layers is all you need", arXiv:2610.28587v1:
  no explicit widths.
- Lu, Zenodo 10.5281/zenodo.22728502, App. C.1: widths (6, 4) for d = 5 but only as an L^p
  APPROXIMATION (closure); Thm 2.13 exact lower bound r_ex(5) ≥ 10 − 6 = 4 (counts first-layer
  cores only); Prop. 2.1: h1 ≥ 5.
- Safran, COLT 2026, Thm 2.1: max(h1, h2) ≥ 1.375 at d = 5 (vacuous).
- Our certified (10, 6) without any skip/linear term beats every exact construction above in both
  widths; our h1 ≥ 7 beats Lu's 4/5.
4. K = 2 exact search, stage 1 (3-locality equations only, `k2b.py`, log `logs/k2b.log`,
   per-pair verdicts `k2b_done.txt`): 1193 flat pairs, 961519 LPs, 314567 exactly certified
   infeasibility certificates, 0 FM fallbacks, 1096 s, 98 MB. 1183 pairs EXCLUDED, 10 survive
   (`k2b_survivors.txt`; flat dims 3–6). Soundness control: `logs/test_k2b_sound.log` (true sign
   patterns of identity neuron pairs are found).

## STOPPED 2026-10-23 (user: general n only)
Stage 2 (k2c.py) excluded pairs 87, 88, 125, 126 of the 10 survivors; 191-193, 230, 231, 392 not run. sub_triples.py killed before output.
