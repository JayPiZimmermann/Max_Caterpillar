import MaxCaterpillar.Frontier.RandomRestriction.BraidCoinColumn
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.LiftedPoint
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.PrefixSwap

/-! Pair-supported rows have exact activation signs at every positive gap scale. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction
open BigOperators NormalizedNetwork
variable {N m : ℕ}

theorem lin_pair_row_eq (A x : Point N) (u v : Fin N) (huv : u ≠ v)
    (hsum : ∑ i, A i = 0) (hsupp : rowSupport A ⊆ {u,v}) :
    lin A x = A u * (x u - x v) := by
  calc
    lin A x = ∑ i in ({u,v} : Finset (Fin N)), A i * x i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hia : i ≠ u := fun h => hi (by simp [h])
      have hib : i ≠ v := fun h => hi (by simp [h])
      rw [row_zero_off_pair A u v hsupp i hia hib,zero_mul]
    _ = A u * x u + A v * x v := Finset.sum_pair huv
    _ = A u * (x u - x v) := by rw [row_other_endpoint A u v huv hsum hsupp]; ring

theorem pair_row_activation_iff (A x : Point N) (u v : Fin N) (huv : u ≠ v)
    (hsum : ∑ i, A i = 0) (hsupp : rowSupport A ⊆ {u,v}) (hgap : x v < x u) :
    (0 < lin A x ↔ 0 < A u) := by
  rw [lin_pair_row_eq A x u v huv hsum hsupp]
  constructor
  · intro h
    by_contra hn
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (sub_pos.mpr hgap).le
    exact (not_lt_of_ge hnonpos) h
  · intro h; exact mul_pos h (sub_pos.mpr hgap)

/-- Only the two endpoint values matter; all other coordinates may be arbitrary. -/
theorem pair_row_swapped_activation (A x y : Point N) (u v : Fin N) (huv : u ≠ v)
    (hsum : ∑ i, A i = 0) (hsupp : rowSupport A ⊆ {u,v}) (hgap : x v < x u)
    (hyu : y u = x v) (hyv : y v = x u) :
    (0 < lin A x ↔ 0 < A u) ∧ (0 < lin A y ↔ 0 < A v) := by
  constructor
  · exact pair_row_activation_iff A x u v huv hsum hsupp hgap
  · apply pair_row_activation_iff A y v u (Ne.symm huv) hsum
    · simpa only [Finset.pair_comm] using hsupp
    · rw [hyu,hyv]; exact hgap

theorem pair_row_activation_difference (A x y : Point N) (u v : Fin N) (huv : u ≠ v)
    (hsum : ∑ i, A i = 0) (hsupp : rowSupport A ⊆ {u,v}) (hgap : x v < x u)
    (hyu : y u = x v) (hyv : y v = x u) :
    (if 0 < lin A x then (1:ℝ) else 0) - (if 0 < lin A y then 1 else 0) =
      edgeCoinDifference A u v := by
  obtain ⟨hx,hy⟩ := pair_row_swapped_activation A x y u v huv hsum hsupp hgap hyu hyv
  simp only [edgeCoinDifference,hx,hy]

open Cartesian DominantGap

/-- Adjacent actual tail coordinates differ by the original separating gap power. -/
theorem actualGapPoint_adjacent_difference (e : Fin m ↪ Fin N) (p : RawConfig m)
    (T : ℝ) (a b : Fin m) (hab : a.val+1=b.val) :
    actualGapPoint e p T (e (p.1 a)) - actualGapPoint e p T (e (p.1 b)) =
      T^((p.2 b).val) := by
  classical
  have hfilter : (Finset.univ.filter (fun k : Fin m => k.val ≤ b.val)) =
      insert b (Finset.univ.filter (fun k : Fin m => k.val ≤ a.val)) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
    constructor
    · intro hk
      by_cases hkb : k = b
      · exact Or.inl hkb
      · right
        have hne : k.val ≠ b.val := fun h => hkb (Fin.ext h)
        have hlt := lt_of_le_of_ne hk hne
        linarith
    · rintro (rfl | hk) <;> linarith
  have hnot : b ∉ Finset.univ.filter (fun k : Fin m => k.val ≤ a.val) := by
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    linarith
  rw [actualGapPoint_selected,actualGapPoint_selected]
  simp only [gapPoint,Equiv.symm_apply_apply]
  rw [hfilter,Finset.sum_insert hnot]
  ring

/-- Swapping the two positions exchanges the actual endpoint coordinate values. -/
theorem actualGapPoint_swap_endpoints (e : Fin m ↪ Fin N) (p : RawConfig m)
    (T : ℝ) (a b : Fin m) :
    actualGapPoint e (swapAdjacentConfig p a b) T (e (p.1 a)) =
      actualGapPoint e p T (e (p.1 b)) ∧
    actualGapPoint e (swapAdjacentConfig p a b) T (e (p.1 b)) =
      actualGapPoint e p T (e (p.1 a)) := by
  simp [actualGapPoint_selected,gapPoint,swapAdjacentConfig]

/-- Actual original-row activation at a positive-scale adjacent tail swap. -/
theorem actualGapPoint_pair_activation (e : Fin m ↪ Fin N) (p : RawConfig m)
    (T : ℝ) (hT : 0 < T) (a b : Fin m) (hab : a.val+1=b.val)
    (A : Point N) (hsum : ∑ i, A i = 0)
    (hsupp : rowSupport A ⊆ {e (p.1 a),e (p.1 b)}) :
    (0 < lin A (actualGapPoint e p T) ↔ 0 < A (e (p.1 a))) ∧
    (0 < lin A (actualGapPoint e (swapAdjacentConfig p a b) T) ↔
      0 < A (e (p.1 b))) := by
  have hne : a ≠ b := by intro h; have := congrArg Fin.val h; linarith
  have huv : e (p.1 a) ≠ e (p.1 b) := fun h => hne (p.1.injective (e.injective h))
  have hg := actualGapPoint_adjacent_difference e p T a b hab
  have hp : 0 < T^((p.2 b).val) := pow_pos hT _
  have hgap : actualGapPoint e p T (e (p.1 b)) < actualGapPoint e p T (e (p.1 a)) := by
    linarith
  obtain ⟨hyu,hyv⟩ := actualGapPoint_swap_endpoints e p T a b
  exact pair_row_swapped_activation A _ _ _ _ huv hsum hsupp hgap hyu hyv

theorem actualGapPoint_pair_activation_difference (e : Fin m ↪ Fin N) (p : RawConfig m)
    (T : ℝ) (hT : 0 < T) (a b : Fin m) (hab : a.val+1=b.val)
    (A : Point N) (hsum : ∑ i, A i = 0)
    (hsupp : rowSupport A ⊆ {e (p.1 a),e (p.1 b)}) :
    (if 0 < lin A (actualGapPoint e p T) then (1:ℝ) else 0) -
      (if 0 < lin A (actualGapPoint e (swapAdjacentConfig p a b) T) then 1 else 0) =
      edgeCoinDifference A (e (p.1 a)) (e (p.1 b)) := by
  obtain ⟨hx,hy⟩ := actualGapPoint_pair_activation e p T hT a b hab A hsum hsupp
  simp only [edgeCoinDifference,hx,hy]

/-- Forward change (new minus old) has the opposite sign to the root column. -/
theorem actualGapPoint_pair_activation_change (e : Fin m ↪ Fin N) (p : RawConfig m)
    (T : ℝ) (hT : 0 < T) (a b : Fin m) (hab : a.val+1=b.val)
    (A : Point N) (hsum : ∑ i, A i = 0)
    (hsupp : rowSupport A ⊆ {e (p.1 a),e (p.1 b)}) :
    (if 0 < lin A (actualGapPoint e (swapAdjacentConfig p a b) T) then (1:ℝ) else 0) -
      (if 0 < lin A (actualGapPoint e p T) then 1 else 0) =
      - edgeCoinDifference A (e (p.1 a)) (e (p.1 b)) := by
  have h := actualGapPoint_pair_activation_difference e p T hT a b hab A hsum hsupp
  linarith only [h]

end MaxCaterpillar.Frontier.RandomRestriction
