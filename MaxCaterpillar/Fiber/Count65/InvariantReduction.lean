import MaxCaterpillar.Fiber.First65

/-! # The invariant representation forced by an actual width-six network

These are network-to-representation bridges. Biases in the original network
are arbitrary; homogeneous recession is used in the proof. No classification
of the first hidden layer is assumed.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65
open BigOperators MaxCaterpillar.Frontier

/-- Only the translation-invariant first-row features are retained. -/
noncomputable def invariantState (net : Network 4 6 5) (x : Point 4) : Fin 6 → ℝ :=
  net.toZ.rho x

/-- The residual decoder supplied by the diagonal limit is positively homogeneous. -/
theorem psi_posHom (net : ZNet 4 6 5) (z : Fin 6 → ℝ) {t : ℝ} (ht : 0 < t) :
    net.Psi (t • z) = t * net.Psi z := by
  rw [ZNet.Psi, ZNet.Psi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hs : (∑ j, net.W k j * (t • z) j) = t * (∑ j, net.W k j * z j) := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs, relu_mul_pos ht]
  unfold pick
  split_ifs <;> ring

lemma psi_zero (net : ZNet 4 6 5) : net.Psi 0 = 0 := by
  unfold ZNet.Psi
  apply Finset.sum_eq_zero
  intro k _
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, relu, max_self]
  unfold pick
  split_ifs <;> ring

/-- The four-invariant-row stratum has one positive carrier, and the exact
function factors through its invariant state plus one linear readout. -/
theorem four_invariant_factorization (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 4) :
    ∃ ell : Point 4, ∃ Phi : (Fin 6 → ℝ) → ℝ,
      (∀ x, Maximum 4 x = lin ell x + Phi (invariantState net x)) ∧
      Phi 0 = 0 ∧
      (∀ z t, 0 < t → Phi (t • z) = t * Phi z) ∧
      lin ell (diag 1) = 1 := by
  classical
  have hp1 : (Finset.univ.filter fun j => 0 < net.toZ.s j).card = 1 := by
    rcases max4_six_slope_counts net hnet with h | h
    · change (Finset.univ.filter fun j => 0 < ∑ i, net.W₁ j i).card = 1
      omega
    · exact h.1
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hp1
  have hsp : 0 < net.toZ.s p := by
    have hm : p ∈ Finset.univ.filter fun j => 0 < net.toZ.s j := by rw [hp]; simp
    simpa using hm
  have hsingle : ∀ j, 0 < net.toZ.s j → j = p := by
    intro j hj
    have hm : j ∈ Finset.univ.filter fun j => 0 < net.toZ.s j := by simp [hj]
    rw [hp] at hm
    exact Finset.mem_singleton.mp hm
  let κ : ℝ := ∑ k, net.toZ.d k * pick (net.toZ.Tp k) (net.toZ.W k p) 0
  let ell : Point 4 := κ • net.toZ.A p
  have hfactor : ∀ x, Maximum 4 x = lin ell x + net.toZ.Psi (invariantState net x) := by
    intro x
    have h := net.toZ.max_eq_of_single (net.toZ_eval_of_max hnet) p hsp hsingle x
    simpa only [ell, κ, invariantState, lin_smul_left] using h
  have hz : invariantState net (diag 1) = 0 := by
    funext j
    unfold invariantState ZNet.rho
    split_ifs with hj
    · rw [lin_diag]
      change relu (1 * net.toZ.s j) = 0
      rw [hj]
      norm_num [relu]
    · rfl
  refine ⟨ell, net.toZ.Psi, hfactor, psi_zero _, ?_, ?_⟩
  · intro z t ht
    exact psi_posHom net.toZ z ht
  · have h := hfactor (diag 1)
    rw [Maximum_diag, hz, psi_zero, add_zero] at h
    exact h.symm

/-- If a positively homogeneous maximum has a one-positive-carrier
representation, its invariant rows retain all input differences. -/
theorem invariant_kernel_diagonal (net : ZNet 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (p : Fin 6) (hp : 0 < net.s p)
    (hsingle : ∀ j, 0 < net.s j → j = p)
    (w : Point 4) (hw : ∀ j, net.s j = 0 → lin (net.A j) w = 0) :
    ∃ t, w = diag t := by
  let t : ℝ := lin (net.A p) w / net.s p
  have hz : w - diag t = 0 := by
    apply net.ker_plus hnet
    intro j hj
    rw [lin_sub_right, lin_diag]
    rcases hj.eq_or_lt with hs | hs
    · rw [hw j hs.symm]
      change 0 - t * net.s j = 0
      rw [← hs]
      ring
    · rw [hsingle j hs]
      change lin (net.A p) w - (lin (net.A p) w / net.s p) * net.s p = 0
      rw [div_mul_cancel _ hp.ne', sub_self]
  exact ⟨t, sub_eq_zero.mp hz⟩

#print axioms four_invariant_factorization
#print axioms invariant_kernel_diagonal
end MaxCaterpillar.Fiber.Count65
