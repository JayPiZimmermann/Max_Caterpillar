import MaxCaterpillar.Fiber.Count65.TwoInvariantPairing.NetworkBridge

/-! # Two-increment extraction from an actual first-layer frame

Every intercept below is a first activation of the actual zero-bias recession
network at a concrete input. The original network may have arbitrary biases.
The comparison features vanish at this input, so the resulting linear
identity is supported on the four diagonal carriers only.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.TwoInvariantPairing
open BigOperators Frontier

variable {h₂ : ℕ} {net : Network 4 6 h₂}

/-- Independent increments above the two inactive anchors. -/
def input (fr : TwoInvariantAnchorFrame net) (a b Q R : ℝ) : Point 4 :=
  fun i => if i = fr.p then a + Q else if i = fr.q then a else if i = fr.r then b + R else b

@[simp] lemma input_p (fr : TwoInvariantAnchorFrame net) (a b Q R : ℝ) :
    input fr a b Q R fr.p = a + Q := by simp [input]
@[simp] lemma input_q (fr : TwoInvariantAnchorFrame net) (a b Q R : ℝ) :
    input fr a b Q R fr.q = a := by simp [input, fr.pq_ne.symm]
@[simp] lemma input_r (fr : TwoInvariantAnchorFrame net) (a b Q R : ℝ) :
    input fr a b Q R fr.r = b + R := by simp [input, fr.pr_ne.symm, fr.qr_ne.symm]
@[simp] lemma input_s (fr : TwoInvariantAnchorFrame net) (a b Q R : ℝ) :
    input fr a b Q R fr.s = b := by simp [input, fr.ps_ne.symm, fr.qs_ne.symm, fr.rs_ne.symm]

lemma max_input (fr : TwoInvariantAnchorFrame net) (a b Q R : ℝ)
    (hQ : 0 ≤ Q) (hR : 0 ≤ R) :
    Maximum 4 (input fr a b Q R) = max (a + Q) (b + R) := by
  apply le_antisymm
  · apply (Maximum_le_iff _ _).mpr
    intro i
    unfold input
    split_ifs
    · exact le_max_left _ _
    · exact le_trans (by linarith : a ≤ a + Q) (le_max_left _ _)
    · exact le_max_right _ _
    · exact le_trans (by linarith : b ≤ b + R) (le_max_right _ _)
  · apply max_le
    · simpa only [input_p] using le_Maximum (input fr a b Q R) fr.p
    · simpa only [input_r] using le_Maximum (input fr a b Q R) fr.r

lemma lin_supported_on_anchors (fr : TwoInvariantAnchorFrame net) (v : Point 4)
    (hv : ∀ i, i ≠ fr.q → i ≠ fr.s → v i = 0) (x : Point 4) :
    lin v x = v fr.q * x fr.q + v fr.s * x fr.s := by
  classical
  unfold lin
  calc
    (∑ i, v i * x i) = ∑ i in ({fr.q,fr.s} : Finset (Fin 4)), v i * x i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hqi : i ≠ fr.q := by intro he; apply hi; simp [he]
      have hsi : i ≠ fr.s := by intro he; apply hi; simp [he]
      rw [hv i hqi hsi, zero_mul]
    _ = _ := Finset.sum_pair fr.qs_ne

/-- The zero-bias recession carrier activation at zero comparison increments. -/
noncomputable def feature (fr : TwoInvariantAnchorFrame net) (j : Fin 6) (a b : ℝ) : ℝ :=
  relu (lin (net.W₁ j) (input fr a b 0 0))

lemma first_root_linear (fr : TwoInvariantAnchorFrame net) (a b Q R : ℝ) :
    lin (net.W₁ fr.firstRoot) (input fr a b Q R) = fr.firstScale * Q := by
  have he : net.W₁ fr.firstRoot = fr.firstScale • (unitVec fr.p - unitVec fr.q) :=
    root_vector_of_coordinates (net.W₁ fr.firstRoot) fr.p fr.q fr.firstScale fr.first_form
  rw [he, lin_smul_left, lin_coordinate_difference, input_p, input_q]
  ring

lemma second_root_linear (fr : TwoInvariantAnchorFrame net) (a b Q R : ℝ) :
    lin (net.W₁ fr.secondRoot) (input fr a b Q R) = fr.secondScale * R := by
  have he : net.W₁ fr.secondRoot = fr.secondScale • (unitVec fr.r - unitVec fr.s) :=
    root_vector_of_coordinates (net.W₁ fr.secondRoot) fr.r fr.s fr.secondScale fr.second_form
  rw [he, lin_smul_left, lin_coordinate_difference, input_r, input_s]
  ring

@[simp] lemma feature_firstRoot (fr : TwoInvariantAnchorFrame net) (a b : ℝ) :
    feature fr fr.firstRoot a b = 0 := by
  simp [feature, first_root_linear, relu]
@[simp] lemma feature_secondRoot (fr : TwoInvariantAnchorFrame net) (a b : ℝ) :
    feature fr fr.secondRoot a b = 0 := by
  simp [feature, second_root_linear, relu]

lemma carrier_feature_formula (fr : TwoInvariantAnchorFrame net) (j : Fin 6)
    (hj : (∑ i, net.W₁ j i) ≠ 0) (a b : ℝ) :
    feature fr j a b = relu (net.W₁ j fr.q * a + net.W₁ j fr.s * b) := by
  rw [feature, lin_supported_on_anchors fr _ (fr.carrier_plane j hj), input_q, input_s]

lemma first_activation (fr : TwoInvariantAnchorFrame net) (j : Fin 6) (a b Q R : ℝ)
    (hQ : 0 ≤ Q) (hR : 0 ≤ R) :
    relu (lin (net.W₁ j) (input fr a b Q R)) = feature fr j a b +
      (if j = fr.firstRoot then fr.firstScale * Q else 0) +
      (if j = fr.secondRoot then fr.secondScale * R else 0) := by
  classical
  by_cases hj : j = fr.firstRoot
  · subst j
    rw [first_root_linear, relu_of_nonneg (mul_nonneg fr.firstScale_pos.le hQ)]
    simp [fr.roots_ne]
  · by_cases hk : j = fr.secondRoot
    · subst j
      rw [second_root_linear, relu_of_nonneg (mul_nonneg fr.secondScale_pos.le hR)]
      simp [fr.roots_ne.symm]
    · have hz : (∑ i, net.W₁ j i) ≠ 0 := by
        intro he
        have hm : j ∈ Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0 := by simp [he]
        rw [fr.invariant_rows] at hm
        simpa [hj,hk] using hm
      rw [lin_supported_on_anchors fr _ (fr.carrier_plane j hz),
        input_q, input_s, carrier_feature_formula fr j hz]
      simp [hj,hk]

lemma second_input (fr : TwoInvariantAnchorFrame net) (k : Fin h₂) (a b Q R : ℝ)
    (hQ : 0 ≤ Q) (hR : 0 ≤ R) :
    (∑ j, net.W₂ k j * relu (lin (net.W₁ j) (input fr a b Q R))) =
      (∑ j, net.W₂ k j * feature fr j a b) +
        (net.W₂ k fr.firstRoot * fr.firstScale) * Q +
        (net.W₂ k fr.secondRoot * fr.secondScale) * R := by
  classical
  simp only [first_activation fr _ a b Q R hQ hR, mul_add,
    Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- Actual-network exactness forces a fixed linear combination of its four
carrier features to recover the inactive-anchor difference. -/
theorem actual_anchor_difference_feature_span (net : Network 4 6 h₂)
    (hexact : ∀ x, net.eval x = Maximum 4 x) (fr : TwoInvariantAnchorFrame net) :
    ∃ c : Fin 6 → ℝ, ∀ a b : ℝ,
      a - b = ∑ j, c j * feature fr j a b := by
  obtain ⟨c,hc⟩ := two_increment_feature_span
    (m := h₂) (p := 6) (X := ℝ × ℝ) Prod.fst Prod.snd
    (fun j x => feature fr j x.1 x.2) net.w₃
    (fun k => net.W₂ k fr.firstRoot * fr.firstScale)
    (fun k => net.W₂ k fr.secondRoot * fr.secondScale) net.W₂ (by
      intro x Q R hQ hR
      have he := net.toZ_eval_of_max hexact (input fr x.1 x.2 Q R)
      rw [max_input fr x.1 x.2 Q R hQ hR] at he
      rw [← he]
      unfold ZNet.eval
      dsimp only [Network.toZ]
      apply Finset.sum_congr rfl
      intro k _
      congr 2
      exact second_input fr k x.1 x.2 Q R hQ hR)
  exact ⟨c,fun a b => hc (a,b)⟩

#check @actual_anchor_difference_feature_span
#print axioms actual_anchor_difference_feature_span
end MaxCaterpillar.Fiber.Count65.TwoInvariantPairing
