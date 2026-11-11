import MaxCaterpillar.Fiber.Count65.PhysicalExtraction

/-! # A dictionary-independent bridge from actual networks to residual folds

Any four homogeneous invariant linear forms followed by the signed common
translation coordinate have this bridge. All six physical parameter arrays
are kept; arbitrary original biases are removed only by proved recession.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.PhysicalExtraction
open BigOperators MaxCaterpillar.Frontier

/-- Coordinates relative to the third input, followed by common translation. -/
noncomputable def inputFrame (x : Point 3) (z : ℝ) : Point 4 :=
  ![x 0 + z, x 1 + z, z, x 2 + z]

/-- The invariant target is the maximum of zero and three coordinates. -/
noncomputable def target (x : Point 3) : ℝ :=
  max (max (x 0) (x 1)) (relu (x 2))

/-- Lift a linear form in relative coordinates to a zero-sum input row. -/
noncomputable def liftRow (a : Point 3) : Point 4 :=
  ![a 0, a 1, -a 0 - a 1 - a 2, a 2]

/-- Four arbitrary invariant rows and one signed translation pair. -/
noncomputable def carrierRows (A : Fin 4 → Point 3) : Fin 6 → Point 4 :=
  ![liftRow (A 0), liftRow (A 1), liftRow (A 2), liftRow (A 3),
    ![0, 0, 1, 0], ![0, 0, -1, 0]]

noncomputable def features (A : Fin 4 → Point 3) (x : Point 3) : Fin 4 → ℝ :=
  fun i => relu (lin (A i) x)

noncomputable def invariantPart (net : Network 4 6 5) (A : Fin 4 → Point 3)
    (j : Fin 5) (x : Point 3) : ℝ :=
  ∑ i : Fin 4, net.W₂ j (Fin.castAdd 2 i) * features A x i

lemma liftRow_inputFrame (a : Point 3) (x : Point 3) (z : ℝ) :
    lin (liftRow a) (inputFrame x z) = lin a x := by
  simp [lin, liftRow, inputFrame, Fin.sum_univ_succ]
  ring

lemma maximum_inputFrame (x : Point 3) (z : ℝ) :
    Maximum 4 (inputFrame x z) = z + target x := by
  rw [Maximum_four]
  change max (max (x 0 + z) (x 1 + z)) (max z (x 2 + z)) =
    z + max (max (x 0) (x 1)) (max 0 (x 2))
  have hz : max z (x 2 + z) = max 0 (x 2) + z := by
    simpa only [zero_add] using max_add_add_right (0 : ℝ) (x 2) z
  rw [max_add_add_right, hz, max_add_add_right]
  ring

lemma carrierRows_first (A : Fin 4 → Point 3) (i : Fin 4) :
    carrierRows A (Fin.castAdd 2 i) = liftRow (A i) := by
  fin_cases i <;> rfl

lemma carrierRows_last_pos (A : Fin 4 → Point 3) (x : Point 3) (z : ℝ) :
    lin (carrierRows A 4) (inputFrame x z) = z := by
  change lin (![0, 0, 1, 0] : Point 4) (inputFrame x z) = z
  simp [inputFrame, lin, Fin.sum_univ_succ]

lemma carrierRows_last_neg (A : Fin 4 → Point 3) (x : Point 3) (z : ℝ) :
    lin (carrierRows A 5) (inputFrame x z) = -z := by
  change lin (![0, 0, -1, 0] : Point 4) (inputFrame x z) = -z
  simp [inputFrame, lin, Fin.sum_univ_succ]

lemma preactivation_inputFrame (net : Network 4 6 5) (A : Fin 4 → Point 3)
    (hW : net.W₁ = carrierRows A) (j : Fin 5) (x : Point 3) (z : ℝ) :
    (∑ i : Fin 6, net.W₂ j i * relu (lin (net.W₁ i) (inputFrame x z))) =
      net.W₂ j 4 * relu z + net.W₂ j 5 * relu (-z) + invariantPart net A j x := by
  rw [hW, Fin.sum_univ_add (a := 4) (b := 2)]
  have hfirst : (∑ i : Fin 4, net.W₂ j (Fin.castAdd 2 i) *
        relu (lin (carrierRows A (Fin.castAdd 2 i)) (inputFrame x z))) =
      invariantPart net A j x := by
    apply Finset.sum_congr rfl
    intro i _
    rw [carrierRows_first, liftRow_inputFrame]
    rfl
  have hlast : (∑ i : Fin 2, net.W₂ j (Fin.natAdd 4 i) *
        relu (lin (carrierRows A (Fin.natAdd 4 i)) (inputFrame x z))) =
      net.W₂ j 4 * relu z + net.W₂ j 5 * relu (-z) := by
    rw [Fin.sum_univ_two]
    change net.W₂ j 4 * relu (lin (carrierRows A 4) (inputFrame x z)) +
      net.W₂ j 5 * relu (lin (carrierRows A 5) (inputFrame x z)) = _
    rw [carrierRows_last_pos, carrierRows_last_neg]
  rw [hfirst, hlast]
  ring

/-- Actual all-input exactness gives the signed-carrier identity without
assuming a residual or physical head normal form. -/
theorem signed_carrier_identity (net : Network 4 6 5) (A : Fin 4 → Point 3)
    (hW : net.W₁ = carrierRows A) (hmax : ∀ x, net.eval x = Maximum 4 x) :
    ∀ x z, (∑ j, net.w₃ j * relu (net.W₂ j 4 * relu z +
      net.W₂ j 5 * relu (-z) + invariantPart net A j x)) = z + target x := by
  have hzmax : ∀ y, net.zeroBias.eval y = Maximum 4 y :=
    net.eval_zeroBias_of_posHom (Maximum 4) (fun c hc y => Maximum_smul hc y) hmax
  intro x z
  have he := hzmax (inputFrame x z)
  rw [maximum_inputFrame] at he
  simp only [Network.eval, Network.zeroBias, Pi.zero_apply, add_zero] at he
  change (∑ j, net.w₃ j * relu
    (∑ i : Fin 6, net.W₂ j i * relu (lin (net.W₁ i) (inputFrame x z)))) =
      z + target x at he
  simp_rw [preactivation_inputFrame net A hW] at he
  exact he

lemma invariantPart_linearCombination (net : Network 4 6 5) (A : Fin 4 → Point 3)
    (l : Fin 5 → ℝ) (x : Point 3) :
    (∑ j, l j * invariantPart net A j x) =
      ∑ i : Fin 4, (∑ j, l j * net.W₂ j (Fin.castAdd 2 i)) * features A x i := by
  simp only [invariantPart, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every actual width-(6,5) network over this arbitrary invariant dictionary
has a residual representation with at most three unchanged physical gates.
All original biases are allowed. -/
theorem physical_residual_at_most_three (net : Network 4 6 5)
    (A : Fin 4 → Point 3) (hW : net.W₁ = carrierRows A)
    (hmax : ∀ x, net.eval x = Maximum 4 x) :
    ∃ S : Finset (Fin 5), S.card ≤ 3 ∧ ∃ R : Fin 4 → ℝ,
      ∀ x : Point 3, target x = (∑ i, R i * features A x i) +
        ∑ j in S, net.w₃ j * relu (invariantPart net A j x) := by
  obtain ⟨S, hS, l, hl⟩ := five_gate_residual_extraction_le_three net.w₃
    (fun j => net.W₂ j 4) (fun j => net.W₂ j 5) (invariantPart net A) target
    (signed_carrier_identity net A hW hmax)
  refine ⟨S, hS, (fun i => ∑ j, l j * net.W₂ j (Fin.castAdd 2 i)), ?_⟩
  intro x
  simpa only [invariantPart_linearCombination] using hl x

end MaxCaterpillar.Fiber.Count65.PhysicalExtraction
