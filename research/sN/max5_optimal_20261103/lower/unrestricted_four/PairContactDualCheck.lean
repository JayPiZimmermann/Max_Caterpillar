import research.sN.max5_optimal_20261103.lower.unrestricted_four.PairContactDual

set_option autoImplicit false

namespace MaxCaterpillar.Max5.PairContactDual.Check

open BigOperators

/-- The consumer states the contact hypothesis literally, without the
producer's predicate abbreviation. -/
theorem literal_type {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0)
    (h : ∀ i j (s t : ℝ), 0 ≤ s → 0 ≤ t →
      ¬ (s * a i + t * a j < 0 ∧ s * b i + t * b j < 0)) :
    a = 0 ∨ b = 0 ∨ ∃ c : ℝ, 0 < c ∧ ∀ i, b i = -c * a i :=
  zero_or_negatively_proportional a b ha hb h

/-- A concrete two-coordinate nonzero control; the first vector is (1,-1)
and the second is (-1,1). -/
theorem two_coordinate_control :
    let a : Fin 2 → ℝ := fun i => if i = 0 then 1 else -1
    let b : Fin 2 → ℝ := fun i => -(a i)
    (∑ i, a i) = 0 ∧ (∑ i, b i) = 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧
      (∀ i j (s t : ℝ), 0 ≤ s → 0 ≤ t →
        ¬ (s * a i + t * a j < 0 ∧ s * b i + t * b j < 0)) := by
  dsimp
  refine ⟨by norm_num [Fin.sum_univ_succ], by norm_num [Fin.sum_univ_succ], ?_, ?_, ?_⟩
  · intro h
    have hh := congr_fun h 0
    norm_num at hh
  · intro h
    have hh := congr_fun h 0
    norm_num at hh
  · simpa only [neg_one_mul] using
      noNegativePair_of_opposite (fun i : Fin 2 => if i = 0 then (1 : ℝ) else -1) 1
        (by norm_num)

#check @literal_type
#print axioms literal_type
#print axioms two_coordinate_control

end MaxCaterpillar.Max5.PairContactDual.Check
