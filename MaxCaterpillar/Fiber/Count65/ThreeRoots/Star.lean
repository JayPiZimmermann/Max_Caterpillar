import MaxCaterpillar.Fiber.Count65.TwoRoots.OneActive

/-! # The only possible orientation of three star roots

The decoder is arbitrary. C3 forces the fourth row to omit the center.
A genuine nonroot then has a nonzero coefficient at every leaf. A top tie
between two leaves excludes every orientation with an inward root.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.ThreeRoots
open MaxCaterpillar.Frontier BigOperators
open TwoRoots

/-- `true` points from the leaf towards the center; `false` is outward. -/
def orientation (b : Bool) : ℝ := if b then 1 else -1

noncomputable def starRows (b₁ b₂ b₃ : Bool) (t : Point 4) : Fin 4 → Point 4 :=
  ![![orientation b₁,-orientation b₁,0,0],
    ![orientation b₂,0,-orientation b₂,0],
    ![orientation b₃,0,0,-orientation b₃],t]

lemma orientation_ne_zero (b : Bool) : orientation b ≠ 0 := by
  cases b <;> norm_num [orientation]

/-- C3 omitting the center cannot be supplied by a star root. -/
theorem star_cover_omits_center (b₁ b₂ b₃ : Bool) (t : Point 4)
    (hcover : ∀ i, ∃ j, starRows b₁ b₂ b₃ t j i = 0) : t 0 = 0 := by
  obtain ⟨j,hj⟩ := hcover 0
  fin_cases j
  · exact False.elim (orientation_ne_zero b₁ hj)
  · exact False.elim (orientation_ne_zero b₂ hj)
  · exact False.elim (orientation_ne_zero b₃ hj)
  · exact hj

/-- A nonroot supported on the three leaves uses every leaf. -/
theorem star_nonroot_leaf_nonzero (t : Point 4) (hsum : ∑ i, t i = 0)
    (ht : Nonroot t) (h0 : t 0 = 0) : t 1 ≠ 0 ∧ t 2 ≠ 0 ∧ t 3 ≠ 0 := by
  refine ⟨?_,?_,?_⟩
  · intro h1
    apply nonroot_not_supported_on_pair t hsum ht 2 3 (by decide)
    intro i hi2 hi3
    fin_cases i
    · exact h0
    · exact h1
    · exact False.elim (hi2 rfl)
    · exact False.elim (hi3 rfl)
  · intro h2
    apply nonroot_not_supported_on_pair t hsum ht 1 3 (by decide)
    intro i hi1 hi3
    fin_cases i
    · exact h0
    · exact False.elim (hi1 rfl)
    · exact h2
    · exact False.elim (hi3 rfl)
  · intro h3
    apply nonroot_not_supported_on_pair t hsum ht 1 2 (by decide)
    intro i hi1 hi2
    fin_cases i
    · exact h0
    · exact False.elim (hi1 rfl)
    · exact False.elim (hi2 rfl)
    · exact h3

private theorem inward_pair_12_excluded (b : Bool) (t : Point 4)
    (hsum : ∑ i, t i = 0) (h0 : t 0 = 0) (ht : Nonroot t) :
    ¬ Represents (starRows true true b t) := by
  intro h
  obtain ⟨ell,Phi,h⟩ := h
  let q : Point 4 := ![0,1,1,-1]
  let w : Point 4 := ![0,t 2,-t 1,0]
  have he := active_kernel_top_coordinates_eq (starRows true true b t) ell Phi h q w
    (fun j hj => by
      fin_cases j <;> norm_num [lin_four,starRows,orientation,q,w] at hj ⊢
      ring) 1 2 (by norm_num [q,Maximum_four]) (by norm_num [q,Maximum_four])
  have h12 : t 2 = -t 1 := he
  have hs : t 0 + t 1 + t 2 + t 3 = 0 := by
    simpa [Fin.sum_univ_succ,show (Fin.succ (2 : Fin 3) : Fin 4) = 3 by decide,add_assoc] using hsum
  exact (star_nonroot_leaf_nonzero t hsum ht h0).2.2 (by linarith only [hs,h12,h0])

private theorem inward_pair_13_excluded (b : Bool) (t : Point 4)
    (hsum : ∑ i, t i = 0) (h0 : t 0 = 0) (ht : Nonroot t) :
    ¬ Represents (starRows true b true t) := by
  intro h
  obtain ⟨ell,Phi,h⟩ := h
  let q : Point 4 := ![0,1,-1,1]
  let w : Point 4 := ![0,t 3,0,-t 1]
  have he := active_kernel_top_coordinates_eq (starRows true b true t) ell Phi h q w
    (fun j hj => by
      fin_cases j <;> norm_num [lin_four,starRows,orientation,q,w] at hj ⊢
      ring) 1 3 (by norm_num [q,Maximum_four]) (by norm_num [q,Maximum_four])
  have h13 : t 3 = -t 1 := he
  have hs : t 0 + t 1 + t 2 + t 3 = 0 := by
    simpa [Fin.sum_univ_succ,show (Fin.succ (2 : Fin 3) : Fin 4) = 3 by decide,add_assoc] using hsum
  exact (star_nonroot_leaf_nonzero t hsum ht h0).2.1 (by linarith only [hs,h13,h0])

private theorem inward_pair_23_excluded (b : Bool) (t : Point 4)
    (hsum : ∑ i, t i = 0) (h0 : t 0 = 0) (ht : Nonroot t) :
    ¬ Represents (starRows b true true t) := by
  intro h
  obtain ⟨ell,Phi,h⟩ := h
  let q : Point 4 := ![0,-1,1,1]
  let w : Point 4 := ![0,0,t 3,-t 2]
  have he := active_kernel_top_coordinates_eq (starRows b true true t) ell Phi h q w
    (fun j hj => by
      fin_cases j <;> norm_num [lin_four,starRows,orientation,q,w] at hj ⊢
      ring) 2 3 (by norm_num [q,Maximum_four]) (by norm_num [q,Maximum_four])
  have h23 : t 3 = -t 2 := he
  have hs : t 0 + t 1 + t 2 + t 3 = 0 := by
    simpa [Fin.sum_univ_succ,show (Fin.succ (2 : Fin 3) : Fin 4) = 3 by decide,add_assoc] using hsum
  exact (star_nonroot_leaf_nonzero t hsum ht h0).1 (by linarith only [hs,h23,h0])

private theorem single_inward_1_excluded (t : Point 4)
    (hsum : ∑ i, t i = 0) (h0 : t 0 = 0) (ht : Nonroot t) :
    ¬ Represents (starRows true false false t) := by
  intro h
  obtain ⟨ell,Phi,h⟩ := h
  let q : Point 4 := ![0,1,1,-1]
  let w : Point 4 := ![0,t 3,0,-t 1]
  have he := active_kernel_top_coordinates_eq (starRows true false false t) ell Phi h q w
    (fun j hj => by
      fin_cases j <;> norm_num [lin_four,starRows,orientation,q,w] at hj ⊢
      ring) 1 2 (by norm_num [q,Maximum_four]) (by norm_num [q,Maximum_four])
  exact (star_nonroot_leaf_nonzero t hsum ht h0).2.2 he

private theorem single_inward_2_excluded (t : Point 4)
    (hsum : ∑ i, t i = 0) (h0 : t 0 = 0) (ht : Nonroot t) :
    ¬ Represents (starRows false true false t) := by
  intro h
  obtain ⟨ell,Phi,h⟩ := h
  let q : Point 4 := ![0,1,1,-1]
  let w : Point 4 := ![0,0,t 3,-t 2]
  have he := active_kernel_top_coordinates_eq (starRows false true false t) ell Phi h q w
    (fun j hj => by
      fin_cases j <;> norm_num [lin_four,starRows,orientation,q,w] at hj ⊢
      ring) 2 1 (by norm_num [q,Maximum_four]) (by norm_num [q,Maximum_four])
  exact (star_nonroot_leaf_nonzero t hsum ht h0).2.2 he

private theorem single_inward_3_excluded (t : Point 4)
    (hsum : ∑ i, t i = 0) (h0 : t 0 = 0) (ht : Nonroot t) :
    ¬ Represents (starRows false false true t) := by
  intro h
  obtain ⟨ell,Phi,h⟩ := h
  let q : Point 4 := ![0,1,-1,1]
  let w : Point 4 := ![0,0,-t 3,t 2]
  have he := active_kernel_top_coordinates_eq (starRows false false true t) ell Phi h q w
    (fun j hj => by
      fin_cases j <;> norm_num [lin_four,starRows,orientation,q,w] at hj ⊢
      ring) 3 1 (by norm_num [q,Maximum_four]) (by norm_num [q,Maximum_four])
  exact (star_nonroot_leaf_nonzero t hsum ht h0).2.1 he

/-- Among all eight orientations, an arbitrary-decoder factorization forces
all three star roots to point outwards. Every real fourth-row coefficient is
allowed; nonroot means no scalar multiple of any coordinate difference. -/
theorem star_orientation_forced (b₁ b₂ b₃ : Bool) (t : Point 4)
    (hsum : ∑ i, t i = 0) (ht : Nonroot t)
    (hcover : ∀ i, ∃ j, starRows b₁ b₂ b₃ t j i = 0)
    (h : Represents (starRows b₁ b₂ b₃ t)) :
    b₁ = false ∧ b₂ = false ∧ b₃ = false := by
  have h0 := star_cover_omits_center b₁ b₂ b₃ t hcover
  cases b₁ <;> cases b₂ <;> cases b₃
  · exact ⟨rfl,rfl,rfl⟩
  · exact False.elim (single_inward_3_excluded t hsum h0 ht h)
  · exact False.elim (single_inward_2_excluded t hsum h0 ht h)
  · exact False.elim (inward_pair_23_excluded false t hsum h0 ht h)
  · exact False.elim (single_inward_1_excluded t hsum h0 ht h)
  · exact False.elim (inward_pair_13_excluded false t hsum h0 ht h)
  · exact False.elim (inward_pair_12_excluded false t hsum h0 ht h)
  · exact False.elim (inward_pair_12_excluded true t hsum h0 ht h)

#print axioms star_orientation_forced
end MaxCaterpillar.Fiber.Count65.ThreeRoots
