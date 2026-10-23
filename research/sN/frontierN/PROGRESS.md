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

## Step 5 (2026-10-24, after commit b4e7787): LEAN VERIFIED, verify.py pending at time of writing
- `free_neurons` (Theorem K): any exact `max_N = 1HL + K·σ(1HL)` (skips allowed) needs K ≥ ⌈N/2⌉−1.
- `second_width_half_succ` (Theorem H⁺): |J+| = |J−| = 1 ⇒ h2 ≥ ⌈N/2⌉ + 1.
- `second_width_joint`: 6h1 + 11N < 3N² + 18 ⇒ h2 ≥ ⌈N/2⌉ + 1 (first joint h1/h2 bound).
  Files: Frontier/SecondWidthPlus.lean, Frontier/GeneralN2.lean; 3 entries in verification/main.json.
- General ⌈N/2⌉+1 (any J±): reduced to the configuration rank δ_R ≥ 1, |J+|+|J−| ≥ 3; open.
- (a) trade-off: open. (b) superlinear h2: open; analysis in REPORT of this step. (c) gap: open;
  data point: certified nets give h1* ≤ C(N,2) for N = 4 (6) and N = 5 (10), below C(N,2)+N+1.

## Step 6 (2026-10-24, after commit 089ec6a)
- (1) h2 ≥ ⌈N/2⌉+1 for every first layer: NOT closed. The remaining configuration (P+={n},
  P−={m}, R ⊆ Z+∩Z−, |R| = ⌈N/2⌉−2, rank δ_R ≥ 1, |J+|+|J−| ≥ 3) contains, for N = 5, 6, the
  statement "h2 = 3 is impossible", which the N = 5 work (best5) also left open. Tried on paper:
  cancellation on ker δ_R (gives only rank δ_R ≥ 1), the odd part of the subtraction identity on
  ker{o±_R} (not linear), averaging the two identities (no gain). No Lean.
- (2) Test of a "sum over S" germ count (germ_usage.py; logs/germ_usage_N4.log, _N5.log): at every
  1_S, |S| ≥ 3, list the neurons vanishing there and the rank of their odd germ functionals on the
  S-directions. In the certified nets ONE neuron serves every S (N = 4: neuron 2 serves all 5 sets;
  N = 5: neuron 2 serves 14 of 16 sets) and the Lemma-3 rank requirement is met by 1-3 neurons
  everywhere. So vanishing + odd-germ rank at the points 1_S cannot give more than the ⌈N/2⌉
  bound; a superlinear argument needs a different invariant (measured, negative).
- (3) Trade-off: no candidate; no search run.
