import MaxCaterpillar.Fiber.Count65.TwoRoots.OneActive

/-! # An opposite root pair cannot accompany a third root and one nonroot

These are necessary conditions on an arbitrary decoder of four first-layer
ReLU observations. No second-layer width or generic-point hypothesis occurs.
The third root may have either orientation, with arbitrary nonzero scale.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.ThreeRoots
open MaxCaterpillar.Frontier BigOperators
open MaxCaterpillar.Fiber.Count65.TwoRoots

noncomputable def oppositeAdjacentRows (s : ℝ) (t : Point 4) : Fin 4 → Point 4 :=
  ![![1,-1,0,0], ![-1,1,0,0], ![0,s,-s,0], t]

noncomputable def oppositeDisjointRows (s : ℝ) (t : Point 4) : Fin 4 → Point 4 :=
  ![![1,-1,0,0], ![-1,1,0,0], ![0,0,s,-s], t]

lemma oppositeAdjacent_cover_forces_zero (s : ℝ) (t : Point 4) (hs : s ≠ 0)
    (hcover : ∀ i, ∃ j, oppositeAdjacentRows s t j i = 0) : t 1 = 0 := by
  obtain ⟨j,hj⟩ := hcover 1
  fin_cases j
  · norm_num [oppositeAdjacentRows] at hj
  · norm_num [oppositeAdjacentRows] at hj
  · exact False.elim (hs (by simpa [oppositeAdjacentRows] using hj))
  · exact hj

/-- C3 reduces the adjacent case to a triple-supported row; one top facet
then forces that row to be a coordinate root, a contradiction. -/
theorem opposite_adjacent_excluded (s : ℝ) (t : Point 4) (hs : s ≠ 0)
    (hsum : ∑ i, t i = 0) (ht : Nonroot t)
    (hcover : ∀ i, ∃ j, oppositeAdjacentRows s t j i = 0) :
    ¬ Represents (oppositeAdjacentRows s t) := by
  intro h
  have ht1 := oppositeAdjacent_cover_forces_zero s t hs hcover
  have hsum' : t 0 + t 1 + t 2 + t 3 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  obtain ⟨ell,Phi,h⟩ := h
  by_cases hsp : 0 < s
  · let q : Point 4 := ![0,-1,0,-1]
    let w : Point 4 := ![t 2,t 2,-t 0,0]
    have hthird : lin (oppositeAdjacentRows s t 2) q < 0 := by
      norm_num [lin_four,oppositeAdjacentRows,q]
      exact hsp
    have he := active_kernel_top_coordinates_eq (oppositeAdjacentRows s t) ell Phi h q w
      (fun j hj => by
        fin_cases j
        · norm_num [lin_four,oppositeAdjacentRows,w]
        · norm_num [lin_four,oppositeAdjacentRows,q] at hj
        · exact False.elim (not_lt_of_ge hj hthird)
        · change lin t w = 0
          simp [lin_four,w,ht1]
          ring) 0 2 (by norm_num [q,Maximum_four]) (by norm_num [q,Maximum_four])
    have h02 : t 2 = -t 0 := by exact he
    have ht3 : t 3 = 0 := by linarith only [hsum',ht1,h02]
    exact nonroot_not_supported_on_pair t hsum ht 0 2 (by decide) (by
      intro l hl0 hl2
      fin_cases l
      · exact False.elim (hl0 rfl)
      · exact ht1
      · exact False.elim (hl2 rfl)
      · exact ht3)
  · have hsn : s < 0 := lt_of_le_of_ne (not_lt.mp hsp) hs
    let q : Point 4 := ![0,-1,-2,0]
    let w : Point 4 := ![t 3,t 3,0,-t 0]
    have hthird : lin (oppositeAdjacentRows s t 2) q < 0 := by
      norm_num [lin_four,oppositeAdjacentRows,q]
      linarith only [hsn]
    have he := active_kernel_top_coordinates_eq (oppositeAdjacentRows s t) ell Phi h q w
      (fun j hj => by
        fin_cases j
        · norm_num [lin_four,oppositeAdjacentRows,w]
        · norm_num [lin_four,oppositeAdjacentRows,q] at hj
        · exact False.elim (not_lt_of_ge hj hthird)
        · change lin t w = 0
          simp [lin_four,w,ht1]
          ring) 0 3 (by norm_num [q,Maximum_four]) (by norm_num [q,Maximum_four])
    have h03 : t 3 = -t 0 := by exact he
    have ht2 : t 2 = 0 := by linarith only [hsum',ht1,h03]
    exact nonroot_not_supported_on_pair t hsum ht 0 3 (by decide) (by
      intro l hl0 hl3
      fin_cases l
      · exact False.elim (hl0 rfl)
      · exact ht1
      · exact ht2
      · exact False.elim (hl3 rfl))

/-- Every fourth-row coefficient must be nonpositive: a boundary top tie is
enough, so no continuity or perturbation argument is needed. -/
lemma opposite_disjoint_coeff_nonpos (s : ℝ) (t : Point 4)
    (h : Represents (oppositeDisjointRows s t)) : ∀ i, t i ≤ 0 := by
  let w : Point 4 := ![0,0,1,1]
  have hker (q : Point 4) : ∀ j, j ≠ (3 : Fin 4) →
      0 ≤ lin (oppositeDisjointRows s t j) q →
      lin (oppositeDisjointRows s t j) w = 0 := by
    intro j hj _
    fin_cases j
    · norm_num [lin_four,oppositeDisjointRows,w]
    · norm_num [lin_four,oppositeDisjointRows,w]
    · norm_num [lin_four,oppositeDisjointRows,w]
    · exact False.elim (hj rfl)
  intro i
  fin_cases i
  · have hn := row_nonneg_of_tie_kernel (oppositeDisjointRows s t) h
      ![-1,0,0,0] w 1 2 3 (by norm_num [Maximum_four])
      (by norm_num [Maximum_four]) (by norm_num [w]) (hker _)
    change 0 ≤ lin t ![-1,0,0,0] at hn
    norm_num [lin_four] at hn
    exact hn
  · have hn := row_nonneg_of_tie_kernel (oppositeDisjointRows s t) h
      ![0,-1,0,0] w 0 2 3 (by norm_num [Maximum_four])
      (by norm_num [Maximum_four]) (by norm_num [w]) (hker _)
    change 0 ≤ lin t ![0,-1,0,0] at hn
    norm_num [lin_four] at hn
    exact hn
  · have hn := row_nonneg_of_tie_kernel (oppositeDisjointRows s t) h
      ![0,0,-1,0] w 0 3 3 (by norm_num [Maximum_four])
      (by norm_num [Maximum_four]) (by norm_num [w]) (hker _)
    change 0 ≤ lin t ![0,0,-1,0] at hn
    norm_num [lin_four] at hn
    exact hn
  · have hn := row_nonneg_of_tie_kernel (oppositeDisjointRows s t) h
      ![0,0,0,-1] w 0 2 3 (by norm_num [Maximum_four])
      (by norm_num [Maximum_four]) (by norm_num [w]) (hker _)
    change 0 ≤ lin t ![0,0,0,-1] at hn
    norm_num [lin_four] at hn
    exact hn

/-- The disjoint case is impossible for every real scale, even zero.
No coordinate-cover hypothesis is needed. -/
theorem opposite_disjoint_excluded (s : ℝ) (t : Point 4)
    (hsum : ∑ i, t i = 0) (ht : Nonroot t) :
    ¬ Represents (oppositeDisjointRows s t) := by
  intro h
  have hn := opposite_disjoint_coeff_nonpos s t h
  have hsum' : t 0 + t 1 + t 2 + t 3 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  have hz : ∀ i, t i = 0 := by
    intro i
    have h0 := hn 0
    have h1 := hn 1
    have h2 := hn 2
    have h3 := hn 3
    fin_cases i
    · change t 0 = 0
      linarith only [hsum',h0,h1,h2,h3]
    · change t 1 = 0
      linarith only [hsum',h0,h1,h2,h3]
    · change t 2 = 0
      linarith only [hsum',h0,h1,h2,h3]
    · change t 3 = 0
      linarith only [hsum',h0,h1,h2,h3]
  exact nonroot_not_supported_on_pair t hsum ht 0 1 (by decide) (by
    intro l _ _
    exact hz l)

#print axioms opposite_adjacent_excluded
#print axioms opposite_disjoint_excluded
end MaxCaterpillar.Fiber.Count65.ThreeRoots
