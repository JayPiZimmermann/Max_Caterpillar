import MaxCaterpillar.Frontier.FirstWidthN

/-! # Exact tied-top points for arbitrary finite families of real rows

The existing polynomial avoidance construction gives a point which is zero on
the selected coordinates and at most -1 elsewhere. The elementary converse
upgrades its row-vanishing implication to an exact equivalence. No row-sum,
nonzero-row, nonempty-coordinate, or nonempty-selected-set premise is needed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction
open BigOperators

variable {N : ℕ} {ι : Type*} [Fintype ι]

/-- A supported row vanishes at every point zero on the selected coordinates. -/
theorem lin_eq_zero_of_zero_on_selected (a q : Point N) (S : Finset (Fin N))
    (hq : ∀ i ∈ S,q i=0) (ha : ∀ i ∉ S,a i=0) : lin a q=0 := by
  classical
  unfold lin
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i∈S
  · rw [hq i hi,mul_zero]
  · rw [ha i hi,zero_mul]

/-- The zero forms at a tied-top point are exactly the rows supported inside S.
The off-S margin is uniformly at least one. -/
theorem exists_tied_point_le_neg_one (A : ι → Point N) (S : Finset (Fin N)) :
    ∃ q : Point N, (∀ i ∈ S,q i=0) ∧ (∀ i ∉ S,q i≤-1) ∧
      ∀ j, (lin (A j) q=0 ↔ ∀ i ∉ S,A j i=0) := by
  obtain ⟨q,hq0,hq1,hgen⟩ := exists_generic_point A S
  refine ⟨q,hq0,hq1,fun j => ⟨hgen j,?_⟩⟩
  exact fun ha => lin_eq_zero_of_zero_on_selected (A j) q S hq0 ha

/-- Every finite family admits an exact tied-top localization point: all
selected coordinates are zero, all others strictly negative, and a row
vanishes there exactly when every coefficient outside S vanishes. -/
theorem exists_tied_point (A : ι → Point N) (S : Finset (Fin N)) :
    ∃ q : Point N, (∀ i ∈ S,q i=0) ∧ (∀ i ∉ S,q i<0) ∧
      ∀ j, (lin (A j) q=0 ↔ ∀ i ∉ S,A j i=0) := by
  obtain ⟨q,hq0,hq1,hgen⟩ := exists_tied_point_le_neg_one A S
  exact ⟨q,hq0,(fun i hi => lt_of_le_of_lt (hq1 i hi) (by norm_num)),hgen⟩

#print axioms exists_tied_point_le_neg_one
#print axioms exists_tied_point
end MaxCaterpillar.Frontier.RandomRestriction
