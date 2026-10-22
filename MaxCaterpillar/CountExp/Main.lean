import MaxCaterpillar.CountExp.W1Functional
import MaxCaterpillar.CountExp.W2Digits
import MaxCaterpillar.CountExp.W3Structure
import MaxCaterpillar.CountExp.W4Orders
import MaxCaterpillar.CountExp.W5Generating
import MaxCaterpillar.CountLower

/-!
# Assembly of the exponential count

`research/sN/NOTE.md`, "MAIN ROUTE".  For `3 ≤ k ≤ N` every `k`-locality (a
permutation `π`) is passed by some face function of any expansion of the maximum
(`exists_passes`, steps 1–2), and every normalized key passes at most
`k! (N - k)! 6^k` permutations (`card_passSet_le`, steps 3–6).  Counting all `N!`
permutations gives `C(N, k) ≤ 6^k |K|` (`choose_le_six_pow_mul_card`), and the
binomial theorem gives `7^N ≤ (N + 1) 6^N |K|` (`seven_pow_le`).
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.CountExp

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections MaxNN.ParamidGeom
  MaxNN.ParamidChain CountCubic

/-- Every normalized key passes at most `k! (N - k)! 6^k` localities (steps 3–6). -/
theorem card_passSet_le {r : ℕ} {key : RealKey (r + 1)} (hkey : key ∈ normalizedKeys r)
    {k : ℕ} (hk : k ≤ r + 1 + 1) :
    (passSet key k).card ≤ k ! * (r + 1 + 1 - k)! * 6 ^ k := by
  classical
  obtain ⟨H, hH, hiff, hleaf⟩ := exists_hingeCat hkey
  have hadj : HingeNbr key = H.Adj := funext fun u => funext fun v => propext (hiff u v)
  set κ := kappa key
  set M := k ! * (r + 1 + 1 - k)!
  -- the admissible `k`-sets and the balanced orders over each of them
  set S : Finset (Finset (Fin (r + 1 + 1))) := univ.filter (H.Admissible κ)
  set g : Finset ℕ → ℚ := fun A => (1 / 2 : ℚ) ^ matchCount H.q H.links H.leafy A with hg
  have hcover : passSet key k ⊆
      (S.filter fun T => T.card = k).biUnion fun T => (fiber k T).filter (Balanced H.Adj κ k) := by
    intro π hπ
    have hp : Passes key k π := by
      unfold passSet at hπ
      convert (Finset.mem_filter.mp hπ).2
    obtain ⟨hbal, hact⟩ := hp
    rw [hadj] at hbal hact
    refine Finset.mem_biUnion.mpr ⟨tieSet k π, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · exact H.admissible_tieSet hH κ hleaf hbal hact
      · exact card_tieSet hk π
    · refine Finset.mem_filter.mpr ⟨?_, hbal⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  -- the per-tie-set bound
  have hper : ∀ T ∈ S.filter (fun T => T.card = k),
      (((fiber k T).filter (Balanced H.Adj κ k)).card : ℚ) ≤ (M : ℚ) * g (H.spineIdx T) := by
    intro T hT
    have hTa : H.Admissible κ T := (Finset.mem_filter.mp (Finset.mem_filter.mp hT).1).2
    have h4 := H.card_balanced_fiber_mul_le hH hk T hTa.1 κ
    have h4' : (((fiber k T).filter (Balanced H.Adj κ k)).card : ℚ) *
        (2 : ℚ) ^ matchCount H.q H.links H.leafy (H.spineIdx T) ≤ (M : ℚ) := by
      exact_mod_cast h4
    have hpos : (0 : ℚ) < (2 : ℚ) ^ matchCount H.q H.links H.leafy (H.spineIdx T) :=
      pow_pos two_pos _
    simp only [hg, one_div, inv_pow]
    rw [← div_eq_mul_inv, le_div_iff hpos]
    exact h4'
  -- coefficient extraction and the generating function
  have hinj : Set.InjOn H.spineIdx S := by
    intro T₁ h₁ T₂ h₂ he
    exact H.eq_of_spineIdx_eq hH (Finset.mem_filter.mp h₁).2 (Finset.mem_filter.mp h₂).2 he
  have hext := sum_card_eq_le_extract S H.spineIdx hinj
    (fun T _ => H.card_spineIdx_le hH T) g (fun A => by simp only [hg]; positivity) k
  have himg : S.image H.spineIdx ⊆ admissibleIdx H.q H.links H.leafy (H.forcedIdx κ) := by
    intro A hA
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hA
    exact H.spineIdx_mem_admissibleIdx hH (Finset.mem_filter.mp hT).2
  have hpw : ∑ A in S.image H.spineIdx, g A * (1 / 6 : ℚ) ^ A.card ≤ 1 := by
    calc ∑ A in S.image H.spineIdx, g A * (1 / 6 : ℚ) ^ A.card
        ≤ ∑ A in admissibleIdx H.q H.links H.leafy (H.forcedIdx κ),
            g A * (1 / 6 : ℚ) ^ A.card :=
          Finset.sum_le_sum_of_subset_of_nonneg himg fun A _ _ => by
            simp only [hg]; positivity
      _ = pathWeight H.q H.links H.leafy (H.forcedIdx κ) (1 / 6) := rfl
      _ ≤ 1 := pathWeight_le_one _ _ _ _ hH.links_sub
  have hcard : ((passSet key k).card : ℚ) ≤ (M : ℚ) * 6 ^ k := by
    calc ((passSet key k).card : ℚ)
        ≤ (((S.filter fun T => T.card = k).biUnion
            fun T => (fiber k T).filter (Balanced H.Adj κ k)).card : ℚ) := by
          exact_mod_cast Finset.card_le_of_subset hcover
      _ ≤ ∑ T in S.filter (fun T => T.card = k),
            (((fiber k T).filter (Balanced H.Adj κ k)).card : ℚ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ T in S.filter (fun T => T.card = k), (M : ℚ) * g (H.spineIdx T) :=
          Finset.sum_le_sum hper
      _ = (M : ℚ) * ∑ T in S.filter (fun T => T.card = k), g (H.spineIdx T) := by
          rw [Finset.mul_sum]
      _ ≤ (M : ℚ) * (6 ^ k * ∑ A in S.image H.spineIdx, g A * (1 / 6 : ℚ) ^ A.card) :=
          mul_le_mul_of_nonneg_left hext (Nat.cast_nonneg _)
      _ ≤ (M : ℚ) * (6 ^ k * 1) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left hpw (by positivity)
      _ = (M : ℚ) * 6 ^ k := by ring
  exact_mod_cast hcard

/-- Every locality is passed by some face function of any expansion (steps 1–2). -/
theorem exists_passes (r : ℕ) (K : Finset (RealKey (r + 1))) (hK : K ⊆ normalizedKeys r)
    (d : RealKey (r + 1) → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ k in K, d k * realUnitY k x + auxiliary a x)
    {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) (π : Equiv.Perm (Fin (r + 1 + 1))) :
    ∃ key ∈ K, Passes key k π := by
  classical
  -- uniform constants for the finitely many keys of `K`
  set c : RealKey (r + 1) → ℝ :=
    fun key => ∑ o, |keyHead key o| + 2 * ((pairSet key).card : ℝ) with hc
  have hc0 : ∀ key, 0 ≤ c key := fun key =>
    add_nonneg (Finset.sum_nonneg fun o _ => abs_nonneg _)
      (mul_nonneg zero_le_two (Nat.cast_nonneg _))
  set C : ℝ := ∑ key in K, c key
  have hcC : ∀ key ∈ K, c key ≤ C := fun key hkey =>
    Finset.single_le_sum (fun key _ => hc0 key) hkey
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun key _ => hc0 key
  set δ : ℝ := 1 / (C + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  set B : ℕ := ⌈C⌉₊ + 1 with hB
  have hB1 : 1 ≤ B := Nat.le_add_left 1 _
  have hCB : C < B := by
    rw [hB]
    push_cast
    exact lt_of_le_of_lt (Nat.le_ceil C) (lt_add_one _)
  -- the functional applied to the expansion
  have hfun : Maximum (r + 1 + 1) = (∑ key in K, d key • realUnitY key) + auxiliary a := by
    funext x
    rw [h x, Pi.add_apply, Finset.sum_apply]
    rfl
  have hval := congrArg (mixedDiff k B δ π) hfun
  rw [mixedDiff_maximum (le_trans (by norm_num) hk) hkN hB1 hδ0.le, map_add,
    mixedDiff_auxiliary hk hkN B δ π a, add_zero, map_sum] at hval
  have hne : ∑ key in K, mixedDiff k B δ π (d key • realUnitY key) ≠ 0 := by
    rw [← hval]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num))) hδ0.ne'
  obtain ⟨key, hkey, hkey0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [map_smul, smul_eq_mul] at hkey0
  have hU : mixedDiff k B δ π (realUnitY key) ≠ 0 := right_ne_zero_of_mul hkey0
  have hδb : δ * c key < 1 := by
    calc δ * c key ≤ δ * C := mul_le_mul_of_nonneg_left (hcC key hkey) hδ0.le
      _ < δ * (C + 1) := mul_lt_mul_of_pos_left (lt_add_one C) hδ0
      _ = 1 := by rw [hδ]; field_simp
  obtain ⟨h0, hact⟩ := pass_of_mixedDiff_unit_ne (hK hkey) hk hkN hB1 hδ0 hδb π hU
  have hBk : ∑ o, |keyHead key o| + ((pairSet key).card : ℝ) < B := by
    have : ∑ o, |keyHead key o| + ((pairSet key).card : ℝ) ≤ c key := by
      simp only [hc]
      have : (0 : ℝ) ≤ ((pairSet key).card : ℝ) := Nat.cast_nonneg _
      linarith
    linarith [hcC key hkey]
  exact ⟨key, hkey, balanced_of_realUnitArg_eq_zero (hK hkey) hBk π h0, hact⟩

/-- **Headline.** Any expansion of the maximum of `N = r + 2` coordinates by
normalized caterpillar face functions `K` and an auxiliary remainder satisfies
`C(N, k) ≤ 6^k |K|` for every `3 ≤ k ≤ N`. -/
theorem choose_le_six_pow_mul_card (r : ℕ) (K : Finset (RealKey (r + 1)))
    (hK : K ⊆ normalizedKeys r) (d : RealKey (r + 1) → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ k in K, d k * realUnitY k x + auxiliary a x)
    {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) :
    (r + 1 + 1).choose k ≤ 6 ^ k * K.card := by
  classical
  have hcover : (univ : Finset (Equiv.Perm (Fin (r + 1 + 1)))) ⊆ K.biUnion fun key =>
      passSet key k := by
    intro π _
    obtain ⟨key, hkey, hp⟩ := exists_passes r K hK d a h hk hkN π
    refine Finset.mem_biUnion.mpr ⟨key, hkey, ?_⟩
    unfold passSet
    convert Finset.mem_filter.mpr ⟨Finset.mem_univ π, hp⟩
  have h1 := Finset.card_le_of_subset hcover
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h1
  have h2 : (r + 1 + 1)! ≤ K.card * (k ! * (r + 1 + 1 - k)! * 6 ^ k) :=
    calc (r + 1 + 1)! ≤ (K.biUnion fun key => passSet key k).card := h1
      _ ≤ ∑ key in K, (passSet key k).card := Finset.card_biUnion_le
      _ ≤ ∑ _key in K, k ! * (r + 1 + 1 - k)! * 6 ^ k :=
          Finset.sum_le_sum fun key hkey => card_passSet_le (hK hkey) hkN
      _ = K.card * (k ! * (r + 1 + 1 - k)! * 6 ^ k) := by
          rw [Finset.sum_const, smul_eq_mul]
  rw [← Nat.choose_mul_factorial_mul_factorial hkN] at h2
  have hpos : 0 < k ! * (r + 1 + 1 - k)! := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have h3 : (r + 1 + 1).choose k * (k ! * (r + 1 + 1 - k)!) ≤
      6 ^ k * K.card * (k ! * (r + 1 + 1 - k)!) := by
    calc (r + 1 + 1).choose k * (k ! * (r + 1 + 1 - k)!)
        = (r + 1 + 1).choose k * k ! * (r + 1 + 1 - k)! := by ring
      _ ≤ K.card * (k ! * (r + 1 + 1 - k)! * 6 ^ k) := h2
      _ = 6 ^ k * K.card * (k ! * (r + 1 + 1 - k)!) := by ring
  exact le_of_mul_le_mul_right h3 hpos

/-- The same for every `k ≤ N` when `N ≥ 3` (`k < 3` from `caterpillar_count_lower`). -/
theorem choose_le_six_pow_mul_card' (r : ℕ) (hr : 1 ≤ r) (K : Finset (RealKey (r + 1)))
    (hK : K ⊆ normalizedKeys r) (d : RealKey (r + 1) → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ k in K, d k * realUnitY k x + auxiliary a x)
    {k : ℕ} (hkN : k ≤ r + 1 + 1) :
    (r + 1 + 1).choose k ≤ 6 ^ k * K.card := by
  rcases Nat.lt_or_ge k 3 with hk | hk
  · have hlow := caterpillar_count_lower r hr K hK d a h
    have hN : r + 1 + 1 ≤ (r + 1 + 1) * (r + 1) := Nat.le_mul_of_pos_right (Nat.succ_pos r)
    have h6 : 6 ≤ (r + 1 + 1) * (r + 1) :=
      Nat.mul_le_mul (Nat.add_le_add_right (Nat.add_le_add_right hr 1) 1)
        (Nat.add_le_add_right hr 1)
    interval_cases k
    · rw [Nat.choose_zero_right, pow_zero, one_mul]
      by_contra hc
      push_neg at hc
      have : K.card = 0 := Nat.lt_one_iff.mp hc
      rw [this] at hlow
      exact absurd (le_trans h6 hlow) (by norm_num)
    · rw [Nat.choose_one_right, pow_one]
      exact le_trans hN hlow
    · rw [Nat.choose_two_right]
      calc (r + 1 + 1) * (r + 1 + 1 - 1) / 2 ≤ (r + 1 + 1) * (r + 1 + 1 - 1) := Nat.div_le_self _ _
        _ = (r + 1 + 1) * (r + 1) := rfl
        _ ≤ 6 * K.card := hlow
        _ ≤ 6 ^ 2 * K.card := Nat.mul_le_mul_right _ (by norm_num)
  · exact choose_le_six_pow_mul_card r K hK d a h hk hkN

/-- **Exponential corollary.** `7^N ≤ (N + 1) 6^N |K|`, i.e. `|K| ≥ (7/6)^N/(N + 1)`. -/
theorem seven_pow_le (r : ℕ) (hr : 1 ≤ r) (K : Finset (RealKey (r + 1)))
    (hK : K ⊆ normalizedKeys r) (d : RealKey (r + 1) → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ k in K, d k * realUnitY k x + auxiliary a x) :
    7 ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * 6 ^ (r + 1 + 1) * K.card := by
  have hbin : 7 ^ (r + 1 + 1) =
      ∑ m in range (r + 1 + 1 + 1), 1 ^ m * 6 ^ (r + 1 + 1 - m) * (r + 1 + 1).choose m := by
    rw [show (7 : ℕ) = 1 + 6 from rfl, add_pow]
    simp only [Nat.cast_id]
  rw [hbin]
  calc ∑ m in range (r + 1 + 1 + 1), 1 ^ m * 6 ^ (r + 1 + 1 - m) * (r + 1 + 1).choose m
      ≤ ∑ _m in range (r + 1 + 1 + 1), 6 ^ (r + 1 + 1) * K.card := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hmN : m ≤ r + 1 + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        have hc := choose_le_six_pow_mul_card' r hr K hK d a h hmN
        calc 1 ^ m * 6 ^ (r + 1 + 1 - m) * (r + 1 + 1).choose m
            ≤ 1 ^ m * 6 ^ (r + 1 + 1 - m) * (6 ^ m * K.card) := Nat.mul_le_mul_left _ hc
          _ = 6 ^ (r + 1 + 1 - m + m) * K.card := by rw [one_pow, pow_add]; ring
          _ = 6 ^ (r + 1 + 1) * K.card := by rw [Nat.sub_add_cancel hmN]
    _ = (r + 1 + 1 + 1) * 6 ^ (r + 1 + 1) * K.card := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_assoc]

end MaxCaterpillar.CountExp
