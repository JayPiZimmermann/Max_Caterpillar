# frontierN progress (general N widths for exact two-hidden-layer max_N)

Model: F(x) = Σ_k d_k σ(Σ_j W_kj σ(a_j·x)) (biases dropped, proved), widths (h1, h2), exact on R^N.

## Step 1 (2026-10-23): combinatorial optimum of the support condition — COMPUTED
`cover_ilp.py`, `cover_ilp.log`: minimum number of supports S ⊆ [N] (|S| = 2..4) with
(C4) "every 4-set I and every a ∈ I: some S with a ∈ S ⊆ I":
N = 4..9: 1, 4, 7, 12, 18, 24 = C(N,2) − ⌊4N/3⌋ (exact ILP optima, HiGHS).
Adding (C3) changes it only for N ≤ 7 (+1). So the C4 counting cannot give more than C(N,2) − ⌊4N/3⌋.

## Step 2: Theorem Q (quadratic first width) — paper proof written (PROOFS.md), Lean in progress
Claim: every network computing max_N has 6 h1 ≥ 3N² − 11N + 12, i.e.
h1 ≥ C(N,2) − ⌊4N/3⌋ + 2 (for N ≥ 4). Status: proved on paper; adversarial check pending.

## Step 3 (2026-10-24): Theorem H — h2 ≥ ⌈N/2⌉ for every network — paper proof written (PROOFS.md)
Odd-part argument + Lemma 3 (dim of subspaces where max+min is linear ≤ ⌊N/2⌋+1, tight).
Lean: MaxCaterpillar/Frontier/MaxMinSubspace.lean (Lemma 3), SecondWidthN.lean (Theorem H). In progress.
Lean for Theorem Q: CoverCount.lean (Lemma K), Claw.lean (Lemma C4), FirstWidthN.lean. In progress.

## Step 4 (2026-10-24): LEAN VERIFIED (axioms propext, Classical.choice, Quot.sound)
- Theorem Q: `MaxCaterpillar.Frontier.first_width_quadratic` (Network with biases):
  `3N² + 12 ≤ 6h₁ + 11N`, i.e. h1 ≥ C(N,2) − ⌊4N/3⌋ + 2. Files: Frontier/CoverCount.lean (Lemma K,
  `cover_count`), Frontier/Claw.lean (Lemma C4, `ZNet.claw`), Frontier/FirstWidthN.lean
  (`exists_generic_point`, `ZNet.cover4`, `ZNet.first_width_quadratic`).
- `first_width_bounds`: with `caterpillar_net`, C(N,2) − ⌊4N/3⌋ + 2 ≤ h1* ≤ C(N,2) + N + 1.
- Theorem H: `MaxCaterpillar.Frontier.second_width_half`: `N ≤ 2h₂` for every N.
  Files: Frontier/MaxMinSubspace.lean (Lemma 3, `finrank_le_of_maxmin(_univ)`),
  Frontier/SecondWidthN.lean (`ZNet.second_width_half`), Frontier/GeneralN.lean (public wrappers,
  `second_width_bounds`). Aggregator MaxCaterpillar/Frontier.lean imports GeneralN.
- verification/main.json: two entries added; verify.py run log: logs/verify.log.
## Open
- (1) trade-off for general N: open. Known: no trade-off for N = 3, 4; bounds
  h1 ≥ C(N,2) − ⌊4N/3⌋ + 2, h2 ≥ max(3, ⌈N/2⌉) are independent of the other width.
- Improving Theorem H to ⌈N/2⌉ + 1 (both ±∞ sides, would recover Theorem 1 at N = 4): not done.
- verify.py: PASS, 76 exact statements, only permitted axioms (logs/verify.log).
- nc_search.py / nc_search.log: sampled search for the one-free-neuron odd-part condition; NOT exact
  (finite samples admit degenerate huge-λ "solutions"); superseded by Lemma 3. No evidence value.
