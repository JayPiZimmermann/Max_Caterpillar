import MaxCaterpillar.Count.Classes
import Mathlib.Data.Nat.Choose.Cast

/-!
# The exponential count

`unified_choose_le`: if `max_N = Σ_{k ∈ K₁} d_k U_k + Σ_{F ∈ K₂} e_F U_F + (auxiliary)` with
caterpillar functions `U_k` and tree face functions `U_F` with `ω ≤ Δ` (`Δ ≥ 2`), then
`C(N, m) ≤ (2Δ+2)^m (|K₁| + |K₂|)` for `3 ≤ m ≤ N`; `unified_exponential`:
`(2Δ+3)^N ≤ (N+1) (2Δ+2)^N (|K₁| + |K₂|)` for `N ≥ 3`.  Corollaries for caterpillars and the
building blocks of Brunck et al. (base 6), bounded hinge degree, and few out-leaves.
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Count

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections CountLower Trees Audit

/-! ## From the per-unit count to the binomial count -/

open Classical in
/-- If every unit passes at most `c^k k! (N-k)!` localities of order `k`, then
`C(N, k) ≤ c^k |K|`. -/
theorem choose_le_of_unit_bound (r : ℕ) {ι : Type*} (K : Finset ι) (D : ι → Descr (r + 1 + 1))
    (hlt : ∀ i ∈ K, ∀ m ∈ (D i).M, m.1 < m.2) (c : ℝ) {k : ℕ} (hk : 3 ≤ k)
    (hkN : k ≤ r + 1 + 1)
    (hunit : ∀ i ∈ K, (((univ : Finset (Equiv.Perm (Fin (r + 1 + 1)))).filter
      (DPasses (D i) k)).card : ℝ) ≤ c ^ k * (k ! * (r + 1 + 1 - k)! : ℕ))
    (d : ι → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ i in K, d i * (D i).unit x + auxiliary a x) :
    ((r + 1 + 1).choose k : ℝ) ≤ c ^ k * K.card := by
  classical
  have hcover : (univ : Finset (Equiv.Perm (Fin (r + 1 + 1)))) ⊆
      K.biUnion fun i => univ.filter (DPasses (D i) k) := by
    intro π _
    obtain ⟨i, hi, hp⟩ := exists_dpasses r K D hlt d a h hk hkN π
    exact mem_biUnion.mpr ⟨i, hi, mem_filter.mpr ⟨mem_univ _, hp⟩⟩
  have h1 := card_le_of_subset hcover
  rw [card_univ, Fintype.card_perm, Fintype.card_fin] at h1
  have h2 : ((r + 1 + 1)! : ℝ) ≤
      ∑ i in K, ((univ.filter (DPasses (D i) k)).card : ℝ) := by
    have := h1.trans card_biUnion_le
    exact_mod_cast this
  have h3 : ∑ i in K, ((univ.filter (DPasses (D i) k)).card : ℝ) ≤
      K.card * (c ^ k * (k ! * (r + 1 + 1 - k)! : ℕ)) := by
    calc ∑ i in K, ((univ.filter (DPasses (D i) k)).card : ℝ)
        ≤ ∑ _i in K, (c ^ k * (k ! * (r + 1 + 1 - k)! : ℕ) : ℝ) := sum_le_sum hunit
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hfac : ((r + 1 + 1)! : ℝ) =
      ((r + 1 + 1).choose k : ℝ) * (k ! * (r + 1 + 1 - k)! : ℕ) := by
    rw [← Nat.choose_mul_factorial_mul_factorial hkN]
    push_cast
    ring
  have hpos : (0 : ℝ) < (k ! * (r + 1 + 1 - k)! : ℕ) := by
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have h4 := h2.trans h3
  rw [hfac] at h4
  have h5 : ((r + 1 + 1).choose k : ℝ) * (k ! * (r + 1 + 1 - k)! : ℕ) ≤
      (c ^ k * K.card) * (k ! * (r + 1 + 1 - k)! : ℕ) := by
    linarith
  exact le_of_mul_le_mul_right h5 hpos

/-! ## From the binomial count to the exponential count -/

/-- `C(N, m) ≤ c^m Z` for `3 ≤ m ≤ N` and `N (N-1) ≤ 6 Z` give `(c + 1)^N ≤ (N + 1) c^N Z`
for `N ≥ 3` and `c ≥ 3`. -/
theorem pow_le_of_choose_le {N : ℕ} (hN : 3 ≤ N) {c Z : ℝ} (hc : 3 ≤ c)
    (hquad : (N : ℝ) * ((N : ℝ) - 1) ≤ 6 * Z)
    (hchoose : ∀ m, 3 ≤ m → m ≤ N → (N.choose m : ℝ) ≤ c ^ m * Z) :
    (c + 1) ^ N ≤ (N + 1) * c ^ N * Z := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hcpos : (0 : ℝ) < c := by linarith
  have hZ1 : 1 ≤ Z := by nlinarith
  have hterm : ∀ m ≤ N, (N.choose m : ℝ) * c ^ (N - m) ≤ c ^ N * Z := by
    intro m hm
    have hcm : c ^ (N - m) * c ^ m = c ^ N := by rw [← pow_add, Nat.sub_add_cancel hm]
    have hp := pow_pos hcpos (N - m)
    have key : (N.choose m : ℝ) ≤ c ^ m * Z := by
      rcases Nat.lt_or_ge m 3 with hm3 | hm3
      · interval_cases m
        · simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul]
          exact hZ1
        · rw [Nat.choose_one_right, pow_one]
          nlinarith
        · rw [Nat.cast_choose_two]
          have hc2 : (9 : ℝ) ≤ c ^ 2 := by nlinarith
          have h9 : 9 * Z ≤ c ^ 2 * Z := mul_le_mul_of_nonneg_right hc2 (by linarith)
          linarith
      · exact hchoose m hm3 hm
    calc (N.choose m : ℝ) * c ^ (N - m) ≤ (c ^ m * Z) * c ^ (N - m) :=
          mul_le_mul_of_nonneg_right key hp.le
      _ = (c ^ (N - m) * c ^ m) * Z := by ring
      _ = c ^ N * Z := by rw [hcm]
  have hbin : (c + 1) ^ N = ∑ m in range (N + 1), (N.choose m : ℝ) * c ^ (N - m) := by
    rw [add_comm, add_pow]
    refine sum_congr rfl fun m _ => ?_
    rw [one_pow, one_mul, mul_comm]
  rw [hbin]
  calc ∑ m in range (N + 1), (N.choose m : ℝ) * c ^ (N - m)
      ≤ ∑ _m in range (N + 1), c ^ N * Z :=
        sum_le_sum fun m hm => hterm m (Nat.lt_succ_iff.mp (mem_range.mp hm))
    _ = (N + 1) * c ^ N * Z := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring

/-! ## The quadratic count -/

/-- The quadratic count for an expansion by caterpillar and tree face functions. -/
theorem mixed_quadratic (r : ℕ) (hr : 1 ≤ r) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (TreeFace (r + 1 + 1))} (hK : IsMixedExpansion r K₁ K₂) :
    (r + 1 + 1) * (r + 1) ≤ 6 * (K₁.card + K₂.card) := by
  obtain ⟨hsub, d₁, d₂, a, h⟩ := hK
  have := count_lower_of_good r hr (K₁.disjSum K₂)
    (Sum.elim (fun key => caterpillarFunction key) fun F => F.unit)
    (by
      rintro (key | F) hi
      · obtain ⟨D, apex, hD, hU⟩ := exists_descr (hsub (inl_mem_disjSum.mp hi))
        exact ⟨D, apex, hD, hU⟩
      · exact ⟨F.descr, F.apex, F.descr_good (by omega), fun y => (F.descr_unit y).symm⟩)
    (Sum.elim d₁ d₂) a
    (by
      intro x
      rw [sum_disj_sum]
      exact h x)
  rwa [card_disjSum] at this

/-! ## Tree units -/

open Classical in
/-- **Per-unit count for tree units.** -/
theorem treeFace_card_passes_le {N : ℕ} (F : TreeFace N) {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hω : OmegaLe F.descr Δ) {k : ℕ} (hk : k ≤ N) :
    ((univ.filter (DPasses F.descr k)).card : ℝ) ≤ (2 * Δ + 2 : ℝ) ^ k * (k ! * (N - k)! : ℕ) := by
  rw [mul_comm]
  exact card_passes_le_unified F.descr F.descr_lt F.descr_leaf F.child F.descr_child_spec
    F.descr_child_inj hΔ hω hk

/-! ## Public statements -/

variable {r : ℕ}

/-- **Binomial count, unified.** If `max_N = Σ_{k ∈ K₁} d_k U_k + Σ_{F ∈ K₂} e_F U_F +
(auxiliary)` with caterpillar functions `U_k` and tree units `U_F` with `ω ≤ Δ` (`Δ ≥ 2`),
then `C(N, m) ≤ (2Δ+2)^m (|K₁| + |K₂|)` for `3 ≤ m ≤ N`. -/
theorem unified_choose_le {K₁ : Finset (FaceKey r)} {K₂ : Finset (TreeFace (r + 1 + 1))}
    (hK : IsMixedExpansion r K₁ K₂) {Δ : ℕ} (hΔ : 2 ≤ Δ) (hω : ∀ F ∈ K₂, OmegaLe F.descr Δ)
    {m : ℕ} (hm : 3 ≤ m) (hmN : m ≤ r + 1 + 1) :
    (r + 1 + 1).choose m ≤ (2 * Δ + 2) ^ m * (K₁.card + K₂.card) := by
  classical
  obtain ⟨hsub, d₁, d₂, a, h⟩ := hK
  have hex : ∀ k : FaceKey r, ∃ F : TreeFace (r + 1 + 1),
      (k ∈ caterpillarDescriptions r →
        TreeFace.IsUpCaterpillar F ∧ caterpillarFunction k = F.unit) := by
    intro k
    by_cases hk : k ∈ caterpillarDescriptions r
    · obtain ⟨F, hF, he⟩ := caterpillarFunction_eq_upTree hk
      exact ⟨F, fun _ => ⟨hF, he⟩⟩
    · exact ⟨Trees.starFace 0 1 (by simp), fun h => absurd h hk⟩
  choose f hf using hex
  set K : Finset (FaceKey r ⊕ TreeFace (r + 1 + 1)) := K₁.disjSum K₂
  set G : FaceKey r ⊕ TreeFace (r + 1 + 1) → TreeFace (r + 1 + 1) := Sum.elim f id
  have hωK : ∀ i ∈ K, OmegaLe (G i).descr Δ := by
    intro i hi
    cases i with
    | inl k =>
      have hk : k ∈ K₁ := by simpa [K] using hi
      exact omegaLe_of_redDeg (by omega)
        (fun v => ((TreeFace.redDeg_of_isUpCaterpillar _ (hf k (hsub hk)).1) v).trans hΔ)
    | inr F => exact hω F (by simpa [K] using hi)
  have hexp : ∀ x, Maximum (r + 1 + 1) x =
      ∑ i in K, Sum.elim d₁ d₂ i * (G i).descr.unit x + auxiliary a x := by
    intro x
    rw [h x, sum_disj_sum]
    simp only [G, Sum.elim_inl, Sum.elim_inr, TreeFace.descr_unit, id]
    congr 2
    refine sum_congr rfl fun k hk => ?_
    rw [(hf k (hsub hk)).2]
  have hc := choose_le_of_unit_bound r K (fun i => (G i).descr) (fun i _ => (G i).descr_lt)
    (2 * Δ + 2) hm hmN (fun i hi => treeFace_card_passes_le (G i) hΔ (hωK i hi) hmN)
    (Sum.elim d₁ d₂) a hexp
  rw [card_disjSum] at hc
  exact_mod_cast hc

/-- **Exponential count, unified.** Under the hypotheses of `unified_choose_le`, for every
`N = r + 2 ≥ 3`: `(2Δ+3)^N ≤ (N+1) (2Δ+2)^N (|K₁| + |K₂|)`, i.e.
`|K₁| + |K₂| ≥ (1 + 1/(2Δ+2))^N / (N+1)`. -/
theorem unified_exponential (hr : 1 ≤ r) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (TreeFace (r + 1 + 1))} (hK : IsMixedExpansion r K₁ K₂) {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hω : ∀ F ∈ K₂, OmegaLe F.descr Δ) :
    (2 * Δ + 3) ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * (2 * Δ + 2) ^ (r + 1 + 1) * (K₁.card + K₂.card) := by
  have hquad := mixed_quadratic r hr hK
  have hΔr : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have key := pow_le_of_choose_le (N := r + 1 + 1) (by omega) (c := 2 * Δ + 2)
    (Z := (K₁.card : ℝ) + K₂.card) (by linarith)
    (by
      have : (((r + 1 + 1) * (r + 1) : ℕ) : ℝ) ≤ ((6 * (K₁.card + K₂.card) : ℕ) : ℝ) := by
        exact_mod_cast hquad
      push_cast at this ⊢
      linarith)
    (fun m hm3 hmN => by exact_mod_cast unified_choose_le hK hΔ hω hm3 hmN)
  have e : (2 * (Δ : ℝ) + 2 + 1) = 2 * Δ + 3 := by ring
  rw [e] at key
  exact_mod_cast key

/-- **The building blocks of Brunck et al., all counted** (caterpillar functions and every
face of the rooted stars): `7^N ≤ (N+1) 6^N (|K₁| + |K₂|)` for `N ≥ 3`. -/
theorem brunck_unified_exponential (hr : 1 ≤ r) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (TreeFace (r + 1 + 1))} (hK : IsBrunckExpansion r K₁ K₂) :
    7 ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * 6 ^ (r + 1 + 1) * (K₁.card + K₂.card) := by
  obtain ⟨hsub, hstar, d₁, d₂, a, h⟩ := hK
  exact unified_exponential hr ⟨hsub, d₁, d₂, a, h⟩ (le_refl 2)
    (fun F hF => omegaLe_of_redDeg (by norm_num) (TreeFace.redDeg_of_isStar F (hstar F hF) 2))

/-- **Bounded hinge degree** (`Δ ≥ 2`), together with caterpillars:
`(2Δ+3)^N ≤ (N+1) (2Δ+2)^N (|K₁| + |K₂|)` for `N ≥ 3`. -/
theorem hingeDeg_unified_exponential (hr : 1 ≤ r) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (TreeFace (r + 1 + 1))} (hK : IsMixedExpansion r K₁ K₂) {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hdeg : ∀ F ∈ K₂, ∀ u, F.hingeDeg u ≤ Δ) :
    (2 * Δ + 3) ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * (2 * Δ + 2) ^ (r + 1 + 1) * (K₁.card + K₂.card) :=
  unified_exponential hr hK hΔ fun F hF =>
    omegaLe_of_redDeg (by omega) (TreeFace.redDeg_of_hingeDeg_le F (hdeg F hF))

/-- **Few out-leaves** (at most `s ≥ 1` out-leaves at every vertex), together with
caterpillars: `(2s+5)^N ≤ (N+1) (2s+4)^N (|K₁| + |K₂|)` for `N ≥ 3`. -/
theorem outLeaf_unified_exponential (hr : 1 ≤ r) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (TreeFace (r + 1 + 1))} (hK : IsMixedExpansion r K₁ K₂) {s : ℕ} (hs : 1 ≤ s)
    (hout : ∀ F ∈ K₂, OutLeafBound F.descr s) :
    (2 * s + 5) ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * (2 * s + 4) ^ (r + 1 + 1) * (K₁.card + K₂.card) := by
  have := unified_exponential hr hK (Δ := s + 1) (by omega)
    (fun F hF => omegaLe_of_outLeafBound F.descr_lt (hout F hF))
  have e1 : 2 * (s + 1) + 3 = 2 * s + 5 := by ring
  have e2 : 2 * (s + 1) + 2 = 2 * s + 4 := by ring
  rwa [e1, e2] at this

end MaxCaterpillar.Count
