import MaxCaterpillar.Frontier.RandomRestriction.BraidModelRow

/-! # Actual Boolean quadratic coefficients of finite braid-row combinations

The rows and combination weights are arbitrary. Nonzero quadratic interactions
are traced back through the sum to an actual nonzero-weight row support.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.BraidModel
open BigOperators StarCertificate
variable {ι : Type*} [Fintype ι]

noncomputable def linearCombinationCoeff (U : Point 5) (c : ι → ℝ)
    (A : ι → Point 5) (pairs : ∀ j, BraidPair (A j)) (i : Fin 5) : ℝ :=
  U i + ∑ j, c j * (pairs j).linearCoeff i

noncomputable def quadraticCombinationCoeff (c : ι → ℝ)
    (A : ι → Point 5) (pairs : ∀ j, BraidPair (A j)) (i l : Fin 5) : ℝ :=
  ∑ j, c j * (pairs j).quadraticCoeff i l

theorem braid_linear_combination_boolean (U : Point 5) (c : ι → ℝ)
    (A : ι → Point 5) (pairs : ∀ j, BraidPair (A j)) (B : Finset (Fin 5)) :
    lin U (fun i => booleanCoordinate i B) +
        ∑ j, c j * relu (lin (A j) (fun i => booleanCoordinate i B)) =
      booleanQuadratic 0 (linearCombinationCoeff U c A pairs)
        (quadraticCombinationCoeff c A pairs) B := by
  classical
  have hrows : (∑ j, c j * relu (lin (A j) (fun i => booleanCoordinate i B))) =
      ∑ j, c j * booleanQuadratic 0 (pairs j).linearCoeff (pairs j).quadraticCoeff B := by
    apply Finset.sum_congr rfl
    intro j _
    rw [(pairs j).relu_boolean]
  have hlinear : (∑ i, linearCombinationCoeff U c A pairs i * booleanCoordinate i B) =
      lin U (fun i => booleanCoordinate i B) +
        ∑ j, c j * (∑ i, (pairs j).linearCoeff i * booleanCoordinate i B) := by
    simp only [linearCombinationCoeff, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum, mul_assoc, lin]
    congr 1
    exact Finset.sum_comm
  have hquadratic :
      (∑ i, ∑ l, quadraticCombinationCoeff c A pairs i l *
          (booleanCoordinate i B * booleanCoordinate l B)) =
        ∑ j, c j * (∑ i, ∑ l, (pairs j).quadraticCoeff i l *
          (booleanCoordinate i B * booleanCoordinate l B)) := by
    simp only [quadraticCombinationCoeff, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    calc
      _ = ∑ i, ∑ j, ∑ l, c j * ((pairs j).quadraticCoeff i l *
          (booleanCoordinate i B * booleanCoordinate l B)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hrows]
  unfold booleanQuadratic
  rw [hlinear, hquadratic]
  simp only [zero_add, mul_add, Finset.sum_add_distrib]
  ring

theorem quadraticCombination_symm_nonzero_support (c : ι → ℝ)
    (A : ι → Point 5) (pairs : ∀ j, BraidPair (A j)) (i l : Fin 5)
    (h : quadraticCombinationCoeff c A pairs i l +
      quadraticCombinationCoeff c A pairs l i ≠ 0) :
    ∃ j, c j ≠ 0 ∧ A j i ≠ 0 ∧ A j l ≠ 0 := by
  classical
  have hs : (∑ j, (c j * (pairs j).quadraticCoeff i l +
      c j * (pairs j).quadraticCoeff l i)) ≠ 0 := by
    simpa only [Finset.sum_add_distrib, quadraticCombinationCoeff] using h
  obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  have hc : c j ≠ 0 := by
    intro hz
    exact hj (by simp [hz])
  by_cases hq : (pairs j).quadraticCoeff i l = 0
  · have hq' : (pairs j).quadraticCoeff l i ≠ 0 := by
      intro hz
      exact hj (by simp [hq, hz])
    have hp := (pairs j).quadraticCoeff_ne_zero_support l i hq'
    exact ⟨j, hc, hp.2, hp.1⟩
  · have hp := (pairs j).quadraticCoeff_ne_zero_support i l hq
    exact ⟨j, hc, hp.1, hp.2⟩

theorem quadraticCombination_diagonal (c : ι → ℝ)
    (A : ι → Point 5) (pairs : ∀ j, BraidPair (A j)) (i : Fin 5) :
    quadraticCombinationCoeff c A pairs i i = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j _
  have hq : (pairs j).quadraticCoeff i i = 0 := by
    by_contra hn
    exact ((pairs j).quadraticCoeff_ne_zero_distinct i i hn) rfl
  rw [hq, mul_zero]

theorem quadraticCombination_symm_nonzero_distinct (c : ι → ℝ)
    (A : ι → Point 5) (pairs : ∀ j, BraidPair (A j)) (i l : Fin 5)
    (h : quadraticCombinationCoeff c A pairs i l +
      quadraticCombinationCoeff c A pairs l i ≠ 0) : i ≠ l := by
  intro heq
  subst l
  exact h (by rw [quadraticCombination_diagonal]; simp)

end MaxCaterpillar.Frontier.RandomRestriction.BraidModel
