import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Directional

/-! # Exact support bookkeeping for indexed coordinate restriction

A retained row has exactly its original support cardinality when its support
is inside the selected coordinates. A discarded row contributes zero. The
resulting indexed cost bound needs no monotonicity assumption on the cost.
No network normalization theorem is assumed in this finite bookkeeping leaf.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
open BigOperators
variable {N m h₁ : ℕ}

@[simp] theorem rowSupport_zero : rowSupport (0 : Point N) = ∅ := by
  classical
  ext i
  simp

/-- Restriction keeps exactly those nonzero coordinates that were selected. -/
theorem image_rowSupport_restrict (e : Fin m ↪ Fin N) (a : Point N) :
    (rowSupport (restrict e a)).image e =
      rowSupport a ∩ Finset.univ.image e := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_inter.mpr
      ⟨(mem_rowSupport a (e j)).mpr ((mem_rowSupport (restrict e a) j).mp hj),
        Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩
  · intro hi
    obtain ⟨ha,he⟩ := Finset.mem_inter.mp hi
    obtain ⟨j,_hj,hji⟩ := Finset.mem_image.mp he
    refine Finset.mem_image.mpr ⟨j,?_,hji⟩
    apply (mem_rowSupport (restrict e a) j).mpr
    change a (e j) ≠ 0
    rw [hji]
    exact (mem_rowSupport a i).mp ha

/-- A row supported inside the selected coordinates loses no support. -/
theorem image_rowSupport_restrict_of_subset (e : Fin m ↪ Fin N) (a : Point N)
    (ha : rowSupport a ⊆ Finset.univ.image e) :
    (rowSupport (restrict e a)).image e = rowSupport a := by
  rw [image_rowSupport_restrict,Finset.inter_eq_left.mpr ha]

/-- Exact support cardinality, including the empty-support boundary. -/
theorem card_rowSupport_restrict (e : Fin m ↪ Fin N) (a : Point N)
    (ha : rowSupport a ⊆ Finset.univ.image e) :
    (rowSupport (restrict e a)).card = (rowSupport a).card := by
  classical
  have hcard := Finset.card_image_of_injective (rowSupport (restrict e a)) e.injective
  rw [image_rowSupport_restrict_of_subset e a ha] at hcard
  exact hcard.symm

/-- A row supported inside the selected coordinates also retains its exact
coordinate sum; no sign or positivity condition is needed. -/
theorem sum_restrict_of_subset (e : Fin m ↪ Fin N) (a : Point N)
    (ha : rowSupport a ⊆ Finset.univ.image e) :
    (∑ i, restrict e a i) = ∑ i, a i := by
  classical
  calc
    (∑ i, restrict e a i) = ∑ i in Finset.univ.image e, a i := by
      rw [Finset.sum_image]
      · rfl
      · exact fun i _ j _ hij => e.injective hij
    _ = ∑ i, a i := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _hi hnot
      by_contra hne
      exact hnot (ha ((mem_rowSupport a i).mpr hne))

/-- Any natural row cost is paid only by original large-support rows wholly
inside the selected set. The first hidden indices are never reindexed. -/
theorem indexed_support_cost_le (A : Fin h₁ → Point N) (Q : Fin h₁ → Point m)
    (S : Finset (Fin N)) (cost : ℕ → ℕ)
    (hQ : ∀ j, (rowSupport (Q j)).card = 0 ∨
      ((rowSupport (Q j)).card = (rowSupport (A j)).card ∧ rowSupport (A j) ⊆ S)) :
    (∑ j, if 3 ≤ (rowSupport (Q j)).card then cost (rowSupport (Q j)).card else 0) ≤
      ∑ j, if 3 ≤ (rowSupport (A j)).card ∧ rowSupport (A j) ⊆ S
        then cost (rowSupport (A j)).card else 0 := by
  classical
  apply Finset.sum_le_sum
  intro j _hj
  rcases hQ j with hzero | ⟨hcard,hsub⟩
  · simp [hzero]
  · by_cases hlarge : 3 ≤ (rowSupport (A j)).card
    · simp [hcard,hlarge,hsub]
    · simp [hcard,hlarge]

/-- Masked restriction satisfies the precise zero-or-equal-support premise;
the only retention hypothesis is containment in the selected coordinates. -/
theorem support_cases_of_masked_restriction (e : Fin m ↪ Fin N)
    (A : Fin h₁ → Point N) (Q : Fin h₁ → Point m)
    (keep : Fin h₁ → Prop) [DecidablePred keep]
    (hkeep : ∀ j, keep j → rowSupport (A j) ⊆ Finset.univ.image e)
    (hQ : ∀ j, Q j = if keep j then restrict e (A j) else 0) :
    ∀ j, (rowSupport (Q j)).card = 0 ∨
      ((rowSupport (Q j)).card = (rowSupport (A j)).card ∧
        rowSupport (A j) ⊆ Finset.univ.image e) := by
  classical
  intro j
  by_cases hj : keep j
  · right
    rw [hQ j,if_pos hj]
    exact ⟨card_rowSupport_restrict e (A j) (hkeep j hj),hkeep j hj⟩
  · left
    rw [hQ j,if_neg hj,rowSupport_zero,Finset.card_empty]

/-- The support-budget comparison for any masked indexed restriction. -/
theorem indexed_support_cost_le_of_masked_restriction (e : Fin m ↪ Fin N)
    (A : Fin h₁ → Point N) (Q : Fin h₁ → Point m)
    (keep : Fin h₁ → Prop) [DecidablePred keep] (cost : ℕ → ℕ)
    (hkeep : ∀ j, keep j → rowSupport (A j) ⊆ Finset.univ.image e)
    (hQ : ∀ j, Q j = if keep j then restrict e (A j) else 0) :
    (∑ j, if 3 ≤ (rowSupport (Q j)).card then cost (rowSupport (Q j)).card else 0) ≤
      ∑ j, if 3 ≤ (rowSupport (A j)).card ∧ rowSupport (A j) ⊆ Finset.univ.image e
        then cost (rowSupport (A j)).card else 0 :=
  indexed_support_cost_le A Q (Finset.univ.image e) cost
    (support_cases_of_masked_restriction e A Q keep hkeep hQ)

#check @rowSupport_zero
#check @image_rowSupport_restrict
#check @card_rowSupport_restrict
#check @sum_restrict_of_subset
#check @indexed_support_cost_le
#check @support_cases_of_masked_restriction
#check @indexed_support_cost_le_of_masked_restriction
#print axioms rowSupport_zero
#print axioms image_rowSupport_restrict
#print axioms image_rowSupport_restrict_of_subset
#print axioms card_rowSupport_restrict
#print axioms sum_restrict_of_subset
#print axioms indexed_support_cost_le
#print axioms support_cases_of_masked_restriction
#print axioms indexed_support_cost_le_of_masked_restriction
end MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
