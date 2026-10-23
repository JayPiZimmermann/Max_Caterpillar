import MaxCaterpillar.Trees.HubsMain

/-!
# One vocabulary: caterpillars, rooted stars, and trees of bounded hinge degree

Expansions of `max_N` whose units are caterpillar face functions (`K₁`) together with tree
face functions of the hub class (`K₂`: rooted stars, trees of hinge degree `≤ Δ`, and any
other tree with `HubOK`).  Every locality is passed by a unit of `K₁` (at most `6^k k!(N-k)!`
localities each, `CountExp.card_passSet_le`) or of `K₂` (`card_passes_le_hub`).  Hence
`C(N,k) ≤ 6^k |K₁| + 2(k+1)(6A)^k S |K₂|` and, for `Δ ≥ 3`, `2^k ≤ 2(k+1)^2 (|K₁| + |K₂|)`
whenever `3 ≤ k` and `(144 A² + 1) k ≤ N`, `A = 2Δ - 1`.
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Trees

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections CountLower CountExp CountCubic

/-- The exponential step: from `C(N,k) ≤ 2(k+1)(6A)^k (Σ_{i ≤ q} C(N,i)) Z` with `2q ≤ k`,
`3 ≤ k` and `(144 A² + 1) k ≤ N` follows `2^k ≤ 2 (k+1)^2 Z`. -/
theorem exp_of_choose_bound {N k q A : ℕ} (hA1 : 1 ≤ A) (hk : 3 ≤ k) (hq2 : 2 * q ≤ k)
    (hkN : (144 * A ^ 2 + 1) * k ≤ N) {Z : ℝ} (hZ : 0 ≤ Z)
    (hmain : (N.choose k : ℝ) ≤ 2 * (k + 1) * (6 * A : ℝ) ^ k *
      (∑ i in range (q + 1), (N.choose i : ℝ)) * Z) :
    (2 : ℝ) ^ k ≤ 2 * (k + 1) ^ 2 * Z := by
  obtain ⟨m, hm⟩ : ∃ m, m = 144 * A ^ 2 + 1 := ⟨_, rfl⟩
  rw [← hm] at hkN
  have hm1 : 1 ≤ m := by omega
  have hkN' : k ≤ N := le_trans (Nat.le_mul_of_pos_left (by omega)) hkN
  -- each term `C(N, i) (12A)^k ≤ C(N, k)` for `i ≤ q`
  have hterm : ∀ i ∈ range (q + 1), ((N.choose i : ℝ)) * (12 * A : ℝ) ^ k ≤ N.choose k := by
    intro i hi
    have hi' : i ≤ q := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hik : i ≤ k := by omega
    have hp := choose_pow_le (N := N) (k := k) hkN hm1 (k - i) i (by omega)
    rw [Nat.add_sub_cancel' hik] at hp
    have hpr : ((m - 1 : ℕ) : ℝ) ^ (k - i) * (N.choose i : ℝ) ≤ N.choose k := by exact_mod_cast hp
    have hm' : ((m - 1 : ℕ) : ℝ) = (12 * A : ℝ) ^ 2 := by
      rw [hm, Nat.add_sub_cancel]; push_cast; ring
    rw [hm', ← pow_mul] at hpr
    have h12 : (1 : ℝ) ≤ 12 * A := by
      have : (1 : ℝ) ≤ A := by exact_mod_cast hA1
      linarith
    have hle : (12 * A : ℝ) ^ k ≤ (12 * A : ℝ) ^ (2 * (k - i)) :=
      pow_le_pow_right h12 (by omega)
    calc (N.choose i : ℝ) * (12 * A : ℝ) ^ k ≤ (N.choose i : ℝ) * (12 * A : ℝ) ^ (2 * (k - i)) :=
          mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
      _ = (12 * A : ℝ) ^ (2 * (k - i)) * (N.choose i : ℝ) := by ring
      _ ≤ N.choose k := hpr
  have hS : (∑ i in range (q + 1), (N.choose i : ℝ)) * (12 * A : ℝ) ^ k ≤ (k + 1) * N.choose k := by
    rw [sum_mul]
    calc ∑ i in range (q + 1), (N.choose i : ℝ) * (12 * A : ℝ) ^ k
        ≤ ∑ _i in range (q + 1), (N.choose k : ℝ) := sum_le_sum hterm
      _ = (q + 1) * N.choose k := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ (k + 1) * N.choose k := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          have : (q : ℝ) ≤ k := by exact_mod_cast (show q ≤ k by omega)
          linarith
  have hCpos : (0 : ℝ) < N.choose k := by exact_mod_cast Nat.choose_pos hkN'
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA1
  -- combine
  have key : (N.choose k : ℝ) * (12 * A : ℝ) ^ k ≤
      (N.choose k : ℝ) * ((6 * A : ℝ) ^ k * (2 * (k + 1) ^ 2 * Z)) := by
    have hmain' := hmain
    have hK0 := hZ
    calc (N.choose k : ℝ) * (12 * A : ℝ) ^ k
        ≤ (2 * (k + 1) * (6 * A : ℝ) ^ k *
            (∑ i in range (q + 1), (N.choose i : ℝ)) * Z) * (12 * A : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right hmain' (by positivity)
      _ = 2 * (k + 1) * (6 * A : ℝ) ^ k * Z *
            ((∑ i in range (q + 1), (N.choose i : ℝ)) * (12 * A : ℝ) ^ k) := by ring
      _ ≤ 2 * (k + 1) * (6 * A : ℝ) ^ k * Z * ((k + 1) * N.choose k) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = (N.choose k : ℝ) * ((6 * A : ℝ) ^ k * (2 * (k + 1) ^ 2 * Z)) := by ring
  have key2 := le_of_mul_le_mul_left key hCpos
  have h12 : (12 * A : ℝ) ^ k = 2 ^ k * (6 * A : ℝ) ^ k := by rw [← mul_pow]; ring
  rw [h12] at key2
  have h6 : (0 : ℝ) < (6 * A : ℝ) ^ k := by positivity
  nlinarith

/-- Every locality is passed by a caterpillar unit or by a tree unit of the expansion. -/
theorem exists_passes_mixed (r : ℕ) (K₁ : Finset (RealKey (r + 1))) (hK₁ : K₁ ⊆ normalizedKeys r)
    (K₂ : Finset (TreeFace (r + 1 + 1))) (d₁ : RealKey (r + 1) → ℝ)
    (d₂ : TreeFace (r + 1 + 1) → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ k in K₁, d₁ k * realUnitY k x +
      ∑ F in K₂, d₂ F * F.unit x + auxiliary a x)
    {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) (π : Equiv.Perm (Fin (r + 1 + 1))) :
    (∃ key ∈ K₁, Passes key k π) ∨ ∃ F ∈ K₂, DPasses F.descr k π := by
  classical
  set c₁ : RealKey (r + 1) → ℝ :=
    fun key => ∑ o, |keyHead key o| + 2 * ((pairSet key).card : ℝ) with hc₁
  set c₂ : TreeFace (r + 1 + 1) → ℝ :=
    fun F => ∑ o, |(F.descr.h o : ℝ)| + 2 * (F.descr.M.card : ℝ) with hc₂
  have hc₁0 : ∀ key, 0 ≤ c₁ key := fun key =>
    add_nonneg (Finset.sum_nonneg fun o _ => abs_nonneg _)
      (mul_nonneg zero_le_two (Nat.cast_nonneg _))
  have hc₂0 : ∀ F, 0 ≤ c₂ F := fun F =>
    add_nonneg (Finset.sum_nonneg fun o _ => abs_nonneg _)
      (mul_nonneg zero_le_two (Nat.cast_nonneg _))
  set C : ℝ := ∑ key in K₁, c₁ key + ∑ F in K₂, c₂ F
  have hS1 : 0 ≤ ∑ key in K₁, c₁ key := Finset.sum_nonneg fun key _ => hc₁0 key
  have hS2 : 0 ≤ ∑ F in K₂, c₂ F := Finset.sum_nonneg fun F _ => hc₂0 F
  have hc₁C : ∀ key ∈ K₁, c₁ key ≤ C := fun key hkey => by
    have := Finset.single_le_sum (fun key _ => hc₁0 key) hkey
    show c₁ key ≤ ∑ key in K₁, c₁ key + ∑ F in K₂, c₂ F
    linarith
  have hc₂C : ∀ F ∈ K₂, c₂ F ≤ C := fun F hF => by
    have := Finset.single_le_sum (fun F _ => hc₂0 F) hF
    show c₂ F ≤ ∑ key in K₁, c₁ key + ∑ F in K₂, c₂ F
    linarith
  have hC0 : 0 ≤ C := by show 0 ≤ ∑ key in K₁, c₁ key + ∑ F in K₂, c₂ F; linarith
  set δ : ℝ := 1 / (C + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  set B : ℕ := ⌈C⌉₊ + 1 with hB
  have hB1 : 1 ≤ B := Nat.le_add_left 1 _
  have hCB : C < B := by
    rw [hB]
    push_cast
    exact lt_of_le_of_lt (Nat.le_ceil C) (lt_add_one _)
  have hδC : ∀ c, c ≤ C → δ * c < 1 := by
    intro c hc
    calc δ * c ≤ δ * C := mul_le_mul_of_nonneg_left hc hδ0.le
      _ < δ * (C + 1) := mul_lt_mul_of_pos_left (lt_add_one C) hδ0
      _ = 1 := by rw [hδ, one_div, inv_mul_cancel (by linarith)]
  have hfun : Maximum (r + 1 + 1) = (∑ key in K₁, d₁ key • realUnitY key) +
      (∑ F in K₂, d₂ F • F.descr.unit) + auxiliary a := by
    funext x
    rw [h x, Pi.add_apply, Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun F _ => by
      show d₂ F * F.unit x = d₂ F * F.descr.unit x
      rw [TreeFace.descr_unit]
  have hval := congrArg (mixedDiff k B δ π) hfun
  rw [mixedDiff_maximum (le_trans (by norm_num) hk) hkN hB1 hδ0.le, map_add, map_add,
    mixedDiff_auxiliary hk hkN B δ π a, add_zero, map_sum, map_sum] at hval
  have hne : ∑ key in K₁, mixedDiff k B δ π (d₁ key • realUnitY key) +
      ∑ F in K₂, mixedDiff k B δ π (d₂ F • F.descr.unit) ≠ 0 := by
    rw [← hval]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num))) hδ0.ne'
  by_cases h1 : ∑ key in K₁, mixedDiff k B δ π (d₁ key • realUnitY key) = 0
  · rw [h1, zero_add] at hne
    right
    obtain ⟨F, hF, hF0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    rw [map_smul, smul_eq_mul] at hF0
    have hU : mixedDiff k B δ π F.descr.unit ≠ 0 := right_ne_zero_of_mul hF0
    obtain ⟨h0, hact⟩ := descr_pass_of_mixedDiff_ne F.descr hk hkN hB1 hδ0
      (hδC _ (hc₂C F hF)) π hU
    have hBk : ∑ o, |(F.descr.h o : ℝ)| + (F.descr.M.card : ℝ) < B := by
      have : ∑ o, |(F.descr.h o : ℝ)| + (F.descr.M.card : ℝ) ≤ c₂ F := by
        simp only [hc₂]
        have : (0 : ℝ) ≤ (F.descr.M.card : ℝ) := Nat.cast_nonneg _
        linarith
      linarith [hc₂C F hF]
    exact ⟨F, hF, descr_balanced_of_arg_eq_zero F.descr F.descr_lt hBk π h0, hact⟩
  · left
    obtain ⟨key, hkey, hkey0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    rw [map_smul, smul_eq_mul] at hkey0
    have hU : mixedDiff k B δ π (realUnitY key) ≠ 0 := right_ne_zero_of_mul hkey0
    obtain ⟨h0, hact⟩ := pass_of_mixedDiff_unit_ne (hK₁ hkey) hk hkN hB1 hδ0
      (hδC _ (hc₁C key hkey)) π hU
    have hBk : ∑ o, |keyHead key o| + ((pairSet key).card : ℝ) < B := by
      have : ∑ o, |keyHead key o| + ((pairSet key).card : ℝ) ≤ c₁ key := by
        simp only [hc₁]
        have : (0 : ℝ) ≤ ((pairSet key).card : ℝ) := Nat.cast_nonneg _
        linarith
      linarith [hc₁C key hkey]
    exact ⟨key, hkey, balanced_of_realUnitArg_eq_zero (hK₁ hkey) hBk π h0, hact⟩

/-- **Binomial count for caterpillars plus hub-class trees.** -/
theorem choose_le_mixed (r : ℕ) (K₁ : Finset (RealKey (r + 1))) (hK₁ : K₁ ⊆ normalizedKeys r)
    (K₂ : Finset (TreeFace (r + 1 + 1))) {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hH : ∀ F ∈ K₂, HubOK F.descr Δ) (d₁ : RealKey (r + 1) → ℝ)
    (d₂ : TreeFace (r + 1 + 1) → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ k in K₁, d₁ k * realUnitY k x +
      ∑ F in K₂, d₂ F * F.unit x + auxiliary a x)
    {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) :
    ((r + 1 + 1).choose k : ℝ) ≤ 6 ^ k * K₁.card + 2 * (k + 1) * (6 * (2 * Δ - 1 : ℕ)) ^ k *
      (∑ i in range (2 * k / (Δ + 1) + 1), ((r + 1 + 1).choose i : ℝ)) * K₂.card := by
  classical
  set X := 2 * (k + 1) * (6 * (2 * Δ - 1 : ℕ)) ^ k *
      (∑ i in range (2 * k / (Δ + 1) + 1), ((r + 1 + 1).choose i : ℝ)) with hX
  set F := k ! * (r + 1 + 1 - k)!
  have hcover : (univ : Finset (Equiv.Perm (Fin (r + 1 + 1)))) ⊆
      (K₁.biUnion fun key => passSet key k) ∪
        K₂.biUnion fun G => univ.filter (DPasses G.descr k) := by
    intro π _
    rcases exists_passes_mixed r K₁ hK₁ K₂ d₁ d₂ a h hk hkN π with ⟨key, hkey, hp⟩ | ⟨G, hG, hp⟩
    · refine mem_union_left _ (mem_biUnion.mpr ⟨key, hkey, ?_⟩)
      unfold passSet
      convert Finset.mem_filter.mpr ⟨Finset.mem_univ π, hp⟩
    · exact mem_union_right _ (mem_biUnion.mpr ⟨G, hG, mem_filter.mpr ⟨mem_univ _, hp⟩⟩)
  have h1 := card_le_of_subset hcover
  rw [card_univ, Fintype.card_perm, Fintype.card_fin] at h1
  have h1' := h1.trans ((card_union_le _ _).trans (add_le_add card_biUnion_le card_biUnion_le))
  have h2 : ((r + 1 + 1)! : ℝ) ≤ ∑ key in K₁, ((passSet key k).card : ℝ) +
      ∑ G in K₂, ((univ.filter (DPasses G.descr k)).card : ℝ) := by
    exact_mod_cast h1'
  have h3 : ∑ key in K₁, ((passSet key k).card : ℝ) ≤ K₁.card * ((6 : ℝ) ^ k * F) := by
    calc ∑ key in K₁, ((passSet key k).card : ℝ) ≤ ∑ _key in K₁, ((6 : ℝ) ^ k * F) :=
          sum_le_sum fun key hkey => by
            have := card_passSet_le (hK₁ hkey) hkN
            have : ((passSet key k).card : ℝ) ≤ ((k ! * (r + 1 + 1 - k)! * 6 ^ k : ℕ) : ℝ) := by
              exact_mod_cast this
            push_cast at this ⊢
            linarith
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have h4 : ∑ G in K₂, ((univ.filter (DPasses G.descr k)).card : ℝ) ≤ K₂.card * (X * F) := by
    calc ∑ G in K₂, ((univ.filter (DPasses G.descr k)).card : ℝ) ≤ ∑ _G in K₂, (X * F : ℝ) :=
          sum_le_sum fun G hG =>
            card_passes_le_hub G.descr G.descr_lt G.descr_leaf hΔ (hH G hG) G.child
              G.descr_child_spec G.descr_child_inj hkN
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hfac : ((r + 1 + 1)! : ℝ) = ((r + 1 + 1).choose k : ℝ) * F := by
    rw [← Nat.choose_mul_factorial_mul_factorial hkN]
    push_cast
    ring
  have hpos : (0 : ℝ) < F := by
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have h5 : ((r + 1 + 1).choose k : ℝ) * F ≤ (6 ^ k * K₁.card + X * K₂.card) * F := by
    rw [← hfac]
    nlinarith
  exact le_of_mul_le_mul_right h5 hpos

/-! ## Public statements -/

/-- `K₁` (caterpillar face descriptions) and `K₂` (tree face descriptions) form an
expansion of `max_N`: `max_N = Σ_{K₁} d₁ U + Σ_{K₂} d₂ U + (auxiliary)`. -/
def IsMixedExpansion (r : ℕ) (K₁ : Finset (FaceKey r)) (K₂ : Finset (TreeFace (r + 1 + 1))) :
    Prop :=
  K₁ ⊆ caterpillarDescriptions r ∧
    ∃ (d₁ : FaceKey r → ℝ) (d₂ : TreeFace (r + 1 + 1) → ℝ)
      (a : Fin (MaxNN.Width.W (r + 1 + 1)) → ℝ),
      ∀ x, Maximum (r + 1 + 1) x =
        ∑ k in K₁, d₁ k * caterpillarFunction k x + ∑ F in K₂, d₂ F * F.unit x +
          ∑ j, a j * auxiliaryFunction (r + 1 + 1) j x

/-- **Exponential count for caterpillars, rooted stars and trees of bounded hinge degree.**
If every tree unit of `K₂` is a rooted star or has hinge degree `≤ Δ` (`Δ ≥ 3`), or more
generally satisfies `HubOK`, then `2^k ≤ 2 (k+1)^2 (|K₁| + |K₂|)` for `3 ≤ k` with
`(144 (2Δ-1)^2 + 1) k ≤ N`. -/
theorem mixed_expansion_exponential (r : ℕ) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (TreeFace (r + 1 + 1))} (hK : IsMixedExpansion r K₁ K₂) {Δ : ℕ} (hΔ : 3 ≤ Δ)
    (hH : ∀ F ∈ K₂, HubOK F.descr Δ) {k : ℕ} (hk : 3 ≤ k)
    (hkN : (144 * (2 * Δ - 1) ^ 2 + 1) * k ≤ r + 1 + 1) :
    (2 : ℝ) ^ k ≤ 2 * (k + 1) ^ 2 * (K₁.card + K₂.card) := by
  obtain ⟨hsub, d₁, d₂, a, h⟩ := hK
  obtain ⟨A, hA⟩ : ∃ A, A = 2 * Δ - 1 := ⟨_, rfl⟩
  rw [← hA] at hkN
  have hA1 : 1 ≤ A := by omega
  have hkN' : k ≤ r + 1 + 1 := le_trans (Nat.le_mul_of_pos_left (by omega)) hkN
  have hmain := choose_le_mixed r K₁ hsub K₂ (by omega : 1 ≤ Δ) hH d₁ d₂ a h hk hkN'
  rw [← hA] at hmain
  obtain ⟨q, hq⟩ : ∃ q, q = 2 * k / (Δ + 1) := ⟨_, rfl⟩
  rw [← hq] at hmain
  have hq2 : 2 * q ≤ k := by
    have h1 : q * (Δ + 1) ≤ 2 * k := by rw [hq]; exact Nat.div_mul_le_self _ _
    have h4 : 4 * q ≤ q * (Δ + 1) := by nlinarith
    linarith
  set S := ∑ i in range (q + 1), ((r + 1 + 1).choose i : ℝ)
  have hS1 : (1 : ℝ) ≤ S := by
    have := single_le_sum (f := fun i => ((r + 1 + 1).choose i : ℝ))
      (fun i _ => Nat.cast_nonneg _) (mem_range.mpr (Nat.succ_pos q))
    simpa using this
  have h6 : (6 : ℝ) ^ k ≤ (6 * A : ℝ) ^ k :=
    pow_le_pow_left (by norm_num) (by
      have : (1 : ℝ) ≤ A := by exact_mod_cast hA1
      linarith) _
  have hbig : (6 : ℝ) ^ k ≤ 2 * (k + 1) * (6 * A : ℝ) ^ k * S := by
    have hk0 : (1 : ℝ) ≤ 2 * (k + 1) := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      linarith
    have hp : (0 : ℝ) ≤ (6 * A : ℝ) ^ k := by positivity
    have e1 : (6 * A : ℝ) ^ k ≤ 2 * (k + 1) * (6 * A : ℝ) ^ k := le_mul_of_one_le_left hp hk0
    have e2 : 2 * (k + 1) * (6 * A : ℝ) ^ k ≤ 2 * (k + 1) * (6 * A : ℝ) ^ k * S :=
      le_mul_of_one_le_right (by positivity) hS1
    linarith
  have hmain' : ((r + 1 + 1).choose k : ℝ) ≤ 2 * (k + 1) * (6 * A : ℝ) ^ k * S *
      ((K₁.card : ℝ) + K₂.card) := by
    have hK1 : (0 : ℝ) ≤ K₁.card := Nat.cast_nonneg _
    have := hmain
    push_cast at this
    nlinarith
  exact exp_of_choose_bound hA1 hk hq2 hkN (by positivity) hmain'

end MaxCaterpillar.Trees
