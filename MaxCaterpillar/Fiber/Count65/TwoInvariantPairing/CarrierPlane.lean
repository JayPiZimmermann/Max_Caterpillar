import MaxCaterpillar.Fiber.Count65.TwoInvariantPairing

/-! # The actual-network carrier-plane bridge

When the two invariant first rows compare complementary input pairs, the
positive and negative diagonal carrier pairs separately span the inactive
anchor plane. No restriction on the second hidden width is used.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65
open BigOperators Frontier

variable {N h₁ h₂ : ℕ}

lemma lin_coordinate_difference (p q : Fin N) (x : Point N) :
    lin (unitVec p - unitVec q) x = x p - x q := by
  have hc : lin (unitVec p - unitVec q) x = lin x (unitVec p - unitVec q) := by
    unfold lin
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hc, lin_sub_right, lin_unitVec, lin_unitVec]

/-- Two carriers at one end of the diagonal ray are a basis of the two
inactive anchors, provided every invariant first row is one of the two
positive comparison directions. -/
theorem two_carriers_anchor_geometry [NeZero N]
    (net : ZNet N h₁ h₂) (hexact : ∀ x, net.eval x = Maximum N x)
    (p q r s : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hroots : ∀ j, net.s j = 0 →
      (∃ c : ℝ, 0 < c ∧ net.A j = c • (unitVec p - unitVec q)) ∨
      (∃ c : ℝ, 0 < c ∧ net.A j = c • (unitVec r - unitVec s)))
    (δ : ℝ) (hδ : δ ≠ 0) (a b : Fin h₁)
    (hcarriers : ∀ j, 0 < δ * net.s j → j = a ∨ j = b) :
    net.A a q * net.A b s - net.A a s * net.A b q ≠ 0 ∧
      ∀ i, i ≠ q → i ≠ s → net.A a i = 0 ∧ net.A b i = 0 := by
  let left : Point N := unitVec q - unitVec r
  let right : Point N := unitVec s - unitVec p
  have hleft : left q = 1 := by simp [left, unitVec, hqr]
  have hright : right s = 1 := by simp [right, unitVec, hps.symm]
  have hleft_top : left q = Maximum N left := by
    rw [hleft]
    symm
    apply Maximum_eq_of left 1 q hleft
    intro i
    simp only [left, Pi.sub_apply, unitVec]
    split_ifs <;> norm_num
  have hright_top : right s = Maximum N right := by
    rw [hright]
    symm
    apply Maximum_eq_of right 1 s hright
    intro i
    simp only [right, Pi.sub_apply, unitVec]
    split_ifs <;> norm_num
  have hzero_left : ∀ j, net.s j = 0 → lin (net.A j) left < 0 := by
    intro j hj
    rcases hroots j hj with ⟨c,hc,he⟩ | ⟨c,hc,he⟩
    · rw [he, lin_smul_left, lin_coordinate_difference]
      simpa [left, unitVec, hpq, hpr, hqr] using neg_neg_of_pos hc
    · rw [he, lin_smul_left, lin_coordinate_difference]
      simpa [left, unitVec, hqr.symm, hqs.symm, hrs.symm] using neg_neg_of_pos hc
  have hzero_right : ∀ j, net.s j = 0 → lin (net.A j) right < 0 := by
    intro j hj
    rcases hroots j hj with ⟨c,hc,he⟩ | ⟨c,hc,he⟩
    · rw [he, lin_smul_left, lin_coordinate_difference]
      simpa [right, unitVec, hps, hpq.symm, hqs] using neg_neg_of_pos hc
    · rw [he, lin_smul_left, lin_coordinate_difference]
      simpa [right, unitVec, hrs, hpr.symm, hps.symm] using neg_neg_of_pos hc
  apply two_observation_anchor_plane (net.A a) (net.A b) q s hqs
  intro w hwa hwb
  have hw : ∀ j, 0 < δ * net.s j → lin (net.A j) w = 0 := by
    intro j hj
    rcases hcarriers j hj with rfl | rfl
    · exact hwa
    · exact hwb
  exact ⟨diagonal_carrier_kernel_top_coordinate net hexact left w δ hδ hzero_left hw q hleft_top,
    diagonal_carrier_kernel_top_coordinate net hexact right w δ hδ hzero_right hw s hright_top⟩

/-- The root rows furnished by the actual-network classification have exactly
the vector form needed by the carrier-plane argument. -/
lemma root_vector_of_coordinates [NeZero N] (v : Point N) (p q : Fin N) (c : ℝ)
    (h : ∀ i, v i = c * (if i = p then 1 else 0) - c * (if i = q then 1 else 0)) :
    v = c • (unitVec p - unitVec q) := by
  funext i
  rw [h i]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, unitVec]
  ring

#check @two_carriers_anchor_geometry
#print axioms two_carriers_anchor_geometry
end MaxCaterpillar.Fiber.Count65
