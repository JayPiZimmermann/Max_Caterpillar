# Adversarial check of Theorem CVX (h4-any-network r3)

Verdict: NOT refuted. Every step re-derived independently:
- Lemma L / cell conditions (a),(c),(Λ): re-derived from the normal form
  g = Σγx + Σ c_e max(x_i,x_j); Λ = Σ_T[σ(Γ_t) − σ(d_t − Γ_t)] = Σ clamp(Γ_t,0,d_t) − c(E(T)) under (c).
- P1 peeling bijection (bottom vertex of O), P2 (T⊆R impossible; Γ_u forced ≤ 0; Λ = c_ab;
  covering edges pairwise intersect -> star ≤ n−2 or triangle), P3 induction arithmetic,
  P4 case list from (|A1|−1)δ1 + (|A2|−1)δ2 ≤ 0 and Γ_{u2} ≤ 0 when A2 = ∅. In every case the
  bound f ≤ (3−e) + e/2 follows from: pair R∖{r_i} adjacent ⇔ {r_i,u1} can be seen.
- Counting: Σ_k W_k ≥ C(N,3)(N−3)!, so |K| ≥ C(N,3)/F(N) = N(N−1)/6 when F(N) ≤ N−2.

Computations (measured, integer exact):
- hill.py: raw-neuron brute force (cell-vanishing by evaluation, 8-corner sum); reproduces
  the convex star f = 3 at N=5 (star_seed.py); local search found nothing above 3.
- ex5.cpp (own closed form): exhaustive N=5, weights {0,1}, Γ ∈ [−5,5]^5: max f = 3
  (ex5_N5_01_R5.log). Random: N=5 W≤3 2e7 samples max 3; N=6 W≤2 3e6 max 4; N=7 max 1.5
  (random.log). All ≤ N−2.
