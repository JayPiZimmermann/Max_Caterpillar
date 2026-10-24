# Exact two-hidden-layer ReLU networks for the maximum of 5 numbers: widths in the literature

Read-only extraction from the text files in this directory and in
`research/sN/dfs/h4-any-network/lit/` (2026-10-23). Notation: `h1`, `h2` = widths of
the first and second hidden layer. "MAX5" = max(x1,...,x5) on R^5 (5 inputs);
"F4" = max{0,x1,...,x4} on R^4 (4 inputs). A MAX5 network gives an F4 network of the
same widths by fixing x5 = 0; the converse direction (F4 applied to x_i - x5, plus x5)
needs an affine skip of x5 to the output or extra pass-through neurons.

Tags: **[text]** = number stated verbatim in the paper; **[derived]** = I counted it from the
displayed construction (not stated by the authors); **[bound]** = authors' own generic upper
bound, not an optimized count.

## Table

| Source | Exact citation | Input model | Biases / skip / affine output | h1 | h2 | Exact or approx. | Notes |
|---|---|---|---|---|---|---|---|
| Bakaev–Brunck–Hertrich–Stade–Yehudayoff, "Better NN expressivity: subdividing the simplex" | arXiv:2505.14338**v3**, Sec. 2.1, Eq. (2), Claim 4, Proposition 3 (p. 4) | MAX5, 5 inputs (x5 plays a distinguished role) | No widths or network written out; identity M = 0.5(P1+P2+P3+P4+Q−R13−R14−R23−R24) of nine terms max(A,B), bias-free, weights in {±1/2, ±1, 2} | **11** [derived]: distinct first-layer hinges 2x5 vs x1+x2, 2x5 vs x3+x4, x1 vs x3, x1 vs x4, x2 vs x3, x2 vs x4, x1+x2 vs x3+x4, 2x5 vs x1+x3, 2x5 vs x1+x4, 2x5 vs x2+x3, 2x5 vs x2+x4 | **9** [derived]: one neuron ReLU(B−A) per term | Exact on R^5 | The counts (11, 9) assume input→second-layer and first-layer→output skips (max(A,B) = A + ReLU(B−A)). For a standard bias-free net without skips: h1 ≤ 21 (adds ReLU(±x_i)), h2 ≤ 11 (adds ReLU(±S), where S = 0.5·Σ±A) [derived upper bound]. Paper: "only linearly many neurons to compute MAX_n" (Sec. 1.2) [text], no numbers |
| Rueß, Averkov, Brunck, Grillo, Hertrich, Loho, Stade, Stargalla, Sun, Winter, "Shallower ReLU network representations via exact linear algebra" | arXiv:2607.21651**v2**, Thm 1.1 (Sec. 3.4), Table 3 (n=5: k=2, support size 3), App. C "Width of the construction" (p. 16), Lemma 1.5 | max_n of n inputs, n=5 | Rank-2 maxout ansatz Φ_{A,B} = max(Σ_A m_ij, Σ_B m_ij), m_ij = max(x_i,x_j); ReLU conversion via Eq. (2) max{x1,x2} = ReLU(x1) − ReLU(−x1) + ReLU(x2−x1). App. C quotes widths for the "standard ReLU network without skip connections" | maxout: ≤ C(n+1,2) = 15; ReLU, no skip: ≤ C(n,2) + 2n = **20** [bound, text formula, evaluated at n=5] | maxout: Q ≤ s·n! = 3·120 = 360; ReLU: ≤ 3Q = **1080** [bound, text formula, evaluated] | Exact on R^n, rational | The n=5 certificate itself (s=3) is only in the online material, not in the paper, so no sharper count is possible from the text. Authors: "width is not optimized" [text] |
| Wang–Basu, "Representing MAX functions using two-hidden-layer ReLU networks" | arXiv:2608.25221**v1**, Thm 2.1 (Eq. 6, 7 orbits) and Thm 2.3 (Eq. 7, 5 orbits), Sec. 2, pp. 7–8 | MAX5, 5 inputs | No network or width given: an identity in atoms max(Σ m_ab, Σ m_cd) of degree k=2, bias-free | **10** pairwise maxima m_ij [derived], i.e. 10 ReLU(x_i−x_j) plus linear channels; no skip: ≤ 20 | Thm 2.3: orbit sizes P3:30, P69:30, P95:60, P97:60 (P0 = 2x_i is linear) → **180** nonlinear atoms [derived]; no skip: ≤ 182. Thm 2.1: 30+15+60+60+60+60 = **285** [derived] | Exact on R^5, rational | Orbit sizes = 120/|stabilizer| (Σ5 action), computed by hand. Second-layer counts assume first-layer→output skips for the linear part of each atom |
| Brunck–Hertrich–Rueß–Stade–Yehudayoff, "Two ReLU layers is all you need" | arXiv:2610.28587**v1**, Thm 1; Thm 25 (Sec. 9); overview Sec. 1.1–1.3 | MAX_n of n inputs, all n | Bias-free WLOG ("we can assume that all biases ... are zero", Sec. 1.1); works with MAX2 (maxout) gates; paramid support functions MAX2(⟨γ,x⟩, Σ MAX2(⟨a_i,x⟩,⟨b_i,x⟩)) | not stated | not stated | Exact, rational (division by n!) | Widths not stated and not derived here: h_Δ ≡ ((−1)^n/n!) Σ_v Σ_π Σ_M (−1)^{|M|} h_pyr(B_{v,π,M}) modulo a lower-dimensional remainder handled recursively. The number of paramids is factorial in n, so this is no competitor at n=5 |
| Lu, "Sharp closure thresholds for two-hidden-layer ReLU networks" | Zenodo 10.5281/zenodo.22728502, App. C.1 (p. 37), Eq. (C.1); Sec. 6 end; Thm 2.12 | MAX5 on [0,1]^5, 5 inputs | Standard network (Eq. 2.1): biases allowed, **no** affine input skips, affine output c0 | **6** [text]: u3=x3, u5=x5, ρ(x1−x2), ρ(x1−x3), ρ(x2−x3), ρ(x4−x5) | **4** [text] | **Approximation only** (L² / L^p closure limit Λ→∞; gated terms "vanish in the limit"). Not exact | Gives w_cl(5) ≤ 6, r_cl(5) ∈ [5, 6]. The cube domain is used (u3 = x3 is a valid ReLU output only because x ≥ 0) |
| Lu (same) | Prop. 2.1 (p. 4–5) | MAX4 on [0,1]^4 (4 numbers, not our target) | standard, cube | 4 [text] | 2 [text] | Exact on cube | Shown only for orientation: exact (4,2) for MAX4 and (3,2) for MAX3 |
| Lu (same) | App. C.2, Eq. (C.2) | MAX6 on [0,1]^6 | standard | 8 [text] | 10 [text] | Approximation only | for comparison |
| Grillo–Hertrich–Loho, "Depth-bounds for NNs via the braid arrangement" | arXiv:2502.09324**v2**, Thm 6.2 and Remark 6.3, Sec. 6 | F6 = max{0,x1..x6} | rank-(3,2) maxout, B_d-conforming | — | — | Exact | No MAX5 width. Thm 5.2: F4 (= MAX5) is **not** computable by a B_d⁰-conforming 2-hidden-layer ReLU net (depth obstruction for that class; consistent with BBHSY because those constructions are not braid-conforming) |
| Hertrich–Basu–Di Summa–Skutella | arXiv:2105.14835**v5**, Thm 1.7 (Sec. 1.4, Sec. 2) | F4 | H-conforming, bias-free WLOG (Prop. 2.3) | — | — | — | Depth obstruction only: no H-conforming 3-layer (= 2 hidden layers) network computes F4. No widths |
| Haase–Hertrich–Loho | arXiv:2302.12553**v1**, Thm 3, Cor. 4 | F_n | integer weights | — | — | — | F4 is not in ReLU^Z(2): with integer weights no 2-hidden-layer network exists. BBHSY uses weight 1/2 |
| Averkov–Hojny–Merkert, "On the expressiveness of rational ReLU NNs with bounded depth" (ICLR 2025) = **2502.06283** | arXiv:2502.06283**v2**, Thm 2, Cor. 3 | F_n | N-ary-fraction weights | — | — | — | For F4, ⌈log3 5⌉ = 2 and ⌈log_p 5⌉ = 2 for every prime p ≥ 3, so no obstruction at 2 hidden layers for decimal weights. With N = 2^t (p = 3 does not divide N) the bound is also 2, which allows BBHSY's dyadic weights. No widths |
| Safran, "A depth hierarchy for computing the maximum in ReLU networks via extremal graph theory" (COLT 2026, PMLR 336) | arXiv:2601.01417**v1**, Thm 2.1 (Sec. 2.1, pp. 5–6), Thm 1.1 | MAX_d on [0,1]^d | standard; biases allowed (removed by homogenization) | — | — | lower bound | See the lower-bound section below |

## Lower bounds on widths (exact representation of MAX5)

- **Lu, Thm 2.13** (p. 10, Eq. 2.34, proved in App. D, end of D.2): for d ≥ 4,
  r_ex(d) ≥ C(d,2) − ⌊4d/3⌋. Here r_ex(d) (Eq. 2.4) is the infimum of the **first hidden
  width m1** over standard networks N(x) = cᵀρ(Bρ(Ax+a)+b)+c0 (biases allowed, no affine
  input skips into the second layer or output, any finite m2) that equal MAX_d exactly on
  [0,1]^d. The proof bounds the number m of first-layer **cores**. Prop. 7.1 replaces the
  network by a homogeneous "paired-core" network, in which a "paired channel" ρ(r), ρ(−r)
  with opposite coefficients only transmits a linear form and is not counted. Then m ≥
  C(d,2) − 4d/3, and m ≤ m1 (Prop. D.2). For d = 5 this gives **10 − 6 = 4**, weaker than
  Prop. 2.1 (input dimension, r_ex(d) ≥ r_cl(d) ≥ d), which gives **m1 ≥ 5**. Remark D.9 notes
  that the Rueß and Wang–Basu constructions use at most C(d,2) cores plus at most 2d linear
  rows, a gap of ⌊4d/3⌋ to the bound. Lu proves no lower bound on h2. Inferred, not stated:
  because cores exclude linear channels, the count probably also applies to the nonlinear
  first-layer units of networks with skips. The theorem itself is stated only for standard
  networks.
- **Lu, App. C.1**: the (6,4) network for d = 5 is a **closure/approximation** result
  (Λ → ∞, convergence in every finite L^p). It is not exact, so it gives no exact width
  upper bound.
- **Safran, Thm 2.1**: a depth-3 network (2 hidden layers) that equals MAX_d on [0,1]^d
  has width (the **maximum** over hidden layers, Sec. 1.2) at least (1/8 − 1/(4d) − 1/(2d²))d².
  For d = 5: (0.125 − 0.05 − 0.02)·25 = 1.375, so **max(h1,h2) ≥ 2**, which says nothing
  useful at d = 5. Safran also cites a depth-independent width ≥ d lower bound from Safran et
  al. [26] (Sec. 1.1, "Lower bounds for Max_d"). That bound is not restated as a theorem here.
- Depth-only obstructions (no width content): H-conforming networks (Hertrich et al.
  Thm 1.7), B_d⁰-conforming networks (Grillo et al. Thm 5.2), integer weights (Haase et al.
  Thm 3). Averkov et al. Thm 2 gives no obstruction at depth 2 for F4.

**Net for MAX5:** the best exact widths readable from the literature are **(11, 9)**
[derived, from BBHSY Eq. (2), bias-free, assuming skip connections], or about (≤21, ≤11)
for a standard network without skips. The best exact lower bound is **h1 ≥ 5** (Lu
Prop. 2.1). Lu Thm 2.13 gives only h1 ≥ 4 at d = 5. No paper gives a lower bound on h2
beyond max(h1, h2) ≥ 2 (Safran).
