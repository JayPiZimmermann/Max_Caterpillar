import MaxNN.Constructions.Paramid.Caterpillar.Geometry.Pairing
import MaxNN.Constructions.Paramid.Caterpillar.Words.Adjacent
import MaxNN.Constructions.Paramid.Caterpillar.Words.Crossing.Base
import MaxNN.Constructions.Paramid.Caterpillar.Block.Patterns

/-! # Adjacent block moves preserve the relevant outer germs

The scalar edge identities imply equal analytic germs for the actual units.
Opposite germs are lower-order because the apex/base maximum is strict.
-/

namespace MaxNN.Caterpillar

open ParamidGeom

variable {m r : ℕ}

theorem germ_caterpillarUnit_insert_left (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1))) (j : Fin r)
    (hj : j.succ ∈ S) (u : Fin m → ℝ)
    (hp : dot (A j.castSucc) u < dot (A j.succ) u)
    (hq : dot (A (parent S j.succ)) u < dot (A j.succ) u) :
    germ (caterpillarUnit apex A S) u =
      germ (caterpillarUnit apex A (insert j.castSucc S)) u := by
  apply germ_caterpillarUnit_eq_of_pair_difference apex A A S (insert j.castSucc S) u
    (A j.castSucc) (A (parent S j.succ)) (A j.succ) hp hq
  intro y
  exact baseMax_insert_left_of_right_mem (values A y) S j hj

theorem germ_caterpillarUnit_adjacentSwap_insert_right (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1))) (j : Fin r)
    (ha0 : (0 : Fin (r + 1)) < j.castSucc) (haS : j.castSucc ∈ S) (hbS : j.succ ∉ S)
    (u : Fin m → ℝ)
    (hp : dot (A j.succ) u < dot (A (parent S j.castSucc)) u)
    (hq : dot (A j.castSucc) u < dot (A (parent S j.castSucc)) u) :
    germ (caterpillarUnit apex A S) u =
      germ (caterpillarUnit apex (fun i => A (adjacentSwap j i)) (insert j.succ S)) u := by
  apply germ_caterpillarUnit_eq_of_pair_difference apex A (fun i => A (adjacentSwap j i))
    S (insert j.succ S) u (A j.succ) (A j.castSucc) (A (parent S j.castSucc)) hp hq
  intro y
  have h := baseMax_adjacentSwap_insert_right (values A y) S j ha0 haS hbS
  simpa only [values, max_comm] using h

theorem SplitValues.neg {A : Fin (r + 1) → Fin m → ℝ} {u : Fin m → ℝ} {j : Fin r}
    (h : SplitValues (values A u) j) : SplitValues (values A (-u)) j := by
  constructor
  · simp only [values, UnitGermAux.dot_neg_right, ne_eq, neg_inj]
    exact h.1
  · intro i
    simp only [values, UnitGermAux.dot_neg_right]
    have hi := h.2 i
    by_cases hl : i < j.succ
    · rw [if_pos hl] at hi ⊢
      exact congrArg Neg.neg hi
    · rw [if_neg hl] at hi ⊢
      exact congrArg Neg.neg hi

theorem baseMax_of_split (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (u : Fin m → ℝ) (j : Fin r)
    (hj : j.succ ∈ S) (h : SplitValues (values A u) j) :
    baseMax (values A u) S = max (dot (A 0) u) (dot (A j.succ) u) :=
  baseMax_unique_cut S (values A u) j hj (fun k hk => h.parent_eq hj k hk)

theorem germ_caterpillarUnit_neg_prefix_mem_LSpan_one (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1))) (j : Fin r)
    (hj : j.succ ∈ S) (u : Fin m → ℝ) (h : SplitValues (values A u) j)
    (ha : dot apex u = dot (A j.succ) u) (hl : dot (A 0) u < dot apex u) :
    germ (caterpillarUnit apex A S) (-u) ∈ LSpan m 1 := by
  apply germ_caterpillarUnit_mem_LSpan_one_of_ne
  rw [baseMax_of_split A S (-u) j hj h.neg]
  simp only [UnitGermAux.dot_neg_right]
  rw [max_eq_left (neg_le_neg (le_of_lt (hl.trans_eq ha)))]
  exact fun he => (ne_of_lt hl) (neg_injective he.symm)

theorem germDiff_insert_left_sub_mem_LSpan_one (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1))) (j : Fin r)
    (hj : j.succ ∈ S) (u : Fin m → ℝ) (h : SplitValues (values A u) j)
    (ha : dot apex u = dot (A j.succ) u) (hl : dot (A 0) u < dot apex u) :
    germDiff u (caterpillarUnit apex A S) -
      germDiff u (caterpillarUnit apex A (insert j.castSucc S)) ∈ LSpan m 1 := by
  have hcast : dot (A j.castSucc) u = dot (A 0) u := by
    have hi := h.2 j.castSucc
    simpa only [if_pos (Fin.castSucc_lt_succ j)] using hi
  have hparent : dot (A (parent S j.succ)) u = dot (A 0) u := by
    have hi := h.2 (parent S j.succ)
    simpa only [if_pos (parent_lt (Fin.succ_pos j))] using hi
  apply germDiff_sub_mem_of_germ_eq
    (germ_caterpillarUnit_insert_left apex A S j hj u
      (by rw [hcast, ← ha]; exact hl) (by rw [hparent, ← ha]; exact hl))
  · exact germ_caterpillarUnit_neg_prefix_mem_LSpan_one apex A S j hj u h ha hl
  · exact germ_caterpillarUnit_neg_prefix_mem_LSpan_one apex A (insert j.castSucc S) j
      (Finset.mem_insert_of_mem hj) u h ha hl

theorem germDiff_insert_left_sub_mem_LSpan_one_of_prefix (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1))) (j : Fin r)
    (hj : j.succ ∈ S) (u : Fin m → ℝ) (h : SplitValues (values A u) j)
    (ha : dot apex u = dot (A j.succ) u) :
    germDiff u (caterpillarUnit apex A S) -
      germDiff u (caterpillarUnit apex A (insert j.castSucc S)) ∈ LSpan m 1 := by
  have hne : dot (A 0) u ≠ dot apex u := fun he => h.1 (he.trans ha)
  rcases lt_or_gt_of_ne hne with hl | hl
  · exact germDiff_insert_left_sub_mem_LSpan_one apex A S j hj u h ha hl
  · apply germDiff_sub_mem_of_neg_direction
    exact germDiff_insert_left_sub_mem_LSpan_one apex A S j hj (-u) h.neg
      (by simp only [UnitGermAux.dot_neg_right]; exact congrArg Neg.neg ha)
      (by simp only [UnitGermAux.dot_neg_right]; exact neg_lt_neg hl)

theorem values_adjacentSwap (A : Fin (r + 1) → Fin m → ℝ) (j : Fin r) (u : Fin m → ℝ)
    (he : dot (A j.castSucc) u = dot (A j.succ) u) :
    values (fun i => A (adjacentSwap j i)) u = values A u := by
  funext i
  by_cases ha : i = j.castSucc
  · subst i
    simp only [values, adjacentSwap, Equiv.swap_apply_left]
    exact he.symm
  · by_cases hb : i = j.succ
    · subst i
      simp only [values, adjacentSwap, Equiv.swap_apply_right]
      exact he
    · simp only [values, adjacentSwap, Equiv.swap_apply_of_ne_of_ne ha hb]

theorem germ_caterpillarUnit_neg_suffix_mem_LSpan_one_of_split (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1))) (k : Fin r)
    (hk : k.succ ∈ S) (u : Fin m → ℝ) (h : SplitValues (values A u) k)
    (ha : dot apex u = dot (A 0) u) (hl : dot (A k.succ) u < dot apex u) :
    germ (caterpillarUnit apex A S) (-u) ∈ LSpan m 1 := by
  apply germ_caterpillarUnit_mem_LSpan_one_of_ne
  rw [baseMax_of_split A S (-u) k hk h.neg]
  simp only [UnitGermAux.dot_neg_right]
  rw [max_eq_right (neg_le_neg (le_of_lt (hl.trans_eq ha)))]
  exact fun he => (ne_of_lt hl) (neg_injective he.symm)

theorem germDiff_adjacentSwap_insert_right_sub_mem_LSpan_one (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1))) (k j : Fin r)
    (hjk : j.castSucc = k.succ) (hk : k.succ ∈ S) (hj : j.succ ∉ S)
    (u : Fin m → ℝ) (h : SplitValues (values A u) k)
    (ha : dot apex u = dot (A 0) u) (hl : dot (A k.succ) u < dot apex u) :
    germDiff u (caterpillarUnit apex A S) -
      germDiff u (caterpillarUnit apex (fun i => A (adjacentSwap j i)) (insert j.succ S)) ∈
        LSpan m 1 := by
  have hja : (0 : Fin (r + 1)) < j.castSucc := by rw [hjk]; exact Fin.succ_pos k
  have hjs : j.castSucc ∈ S := by rw [hjk]; exact hk
  have hcast : dot (A j.castSucc) u = dot (A k.succ) u := congrArg (fun i => dot (A i) u) hjk
  have hlast : dot (A j.succ) u = dot (A k.succ) u := by
    have hi := h.2 j.succ
    have hle : k.succ ≤ j.succ := by rw [← hjk]; exact le_of_lt (Fin.castSucc_lt_succ j)
    simpa only [if_neg (not_lt.mpr hle)] using hi
  have hparent : dot (A (parent S j.castSucc)) u = dot (A 0) u := by
    have hi := h.2 (parent S j.castSucc)
    simpa only [if_pos ((parent_lt (S := S) hja).trans_eq hjk)] using hi
  have hv := values_adjacentSwap A j u (hcast.trans hlast.symm)
  apply germDiff_sub_mem_of_germ_eq
    (germ_caterpillarUnit_adjacentSwap_insert_right apex A S j hja hjs hj u
      (by rw [hlast, hparent, ← ha]; exact hl) (by rw [hcast, hparent, ← ha]; exact hl))
  · exact germ_caterpillarUnit_neg_suffix_mem_LSpan_one_of_split apex A S k hk u h ha hl
  · apply germ_caterpillarUnit_neg_suffix_mem_LSpan_one_of_split apex
      (fun i => A (adjacentSwap j i)) (insert j.succ S) k (Finset.mem_insert_of_mem hk) u
    · rwa [hv]
    · exact ha.trans (congrFun hv 0).symm
    · exact (congrFun hv k.succ).trans_lt hl

theorem germDiff_adjacentSwap_insert_right_sub_mem_LSpan_one_of_suffix (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1))) (k j : Fin r)
    (hjk : j.castSucc = k.succ) (hk : k.succ ∈ S) (hj : j.succ ∉ S)
    (u : Fin m → ℝ) (h : SplitValues (values A u) k)
    (ha : dot apex u = dot (A 0) u) :
    germDiff u (caterpillarUnit apex A S) -
      germDiff u (caterpillarUnit apex (fun i => A (adjacentSwap j i)) (insert j.succ S)) ∈
        LSpan m 1 := by
  have hne : dot (A k.succ) u ≠ dot apex u := fun he => h.1 (ha.symm.trans he.symm)
  rcases lt_or_gt_of_ne hne with hl | hl
  · exact germDiff_adjacentSwap_insert_right_sub_mem_LSpan_one apex A S k j hjk hk hj u h ha hl
  · apply germDiff_sub_mem_of_neg_direction
    exact germDiff_adjacentSwap_insert_right_sub_mem_LSpan_one apex A S k j hjk hk hj (-u) h.neg
      (by simp only [UnitGermAux.dot_neg_right]; exact congrArg Neg.neg ha)
      (by simp only [UnitGermAux.dot_neg_right]; exact neg_lt_neg hl)

end MaxNN.Caterpillar
