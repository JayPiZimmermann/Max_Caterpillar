import MaxCaterpillar.Fiber.Count65.ZeroOneRoots.PositiveCircuit
import MaxCaterpillar.Fiber.Count65.ZeroOneRoots.MixedCircuit
import MaxCaterpillar.Fiber.Count65.ZeroOneRoots.Halfspace

/-! # A genuine four-feature information obstruction

The quantified rows, coefficients, circuit, and test inputs are arbitrary
real objects. Every circuit and every sign case is exhausted in the proof.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.ZeroOneRoots
open BigOperators Frontier

private theorem same_sign_nonroot_pair (A : Fin 4 → Point 4) (c : Point 4)
    (hc : ∀ j, c j ≠ 0)
    (hn : 3 ≤ (Finset.univ.filter fun j => 3 ≤ (nonzeroCoordinates (A j)).card).card) :
    ∃ p q : Fin 4, p ≠ q ∧ 3 ≤ (nonzeroCoordinates (A p)).card ∧
      3 ≤ (nonzeroCoordinates (A q)).card ∧ 0 < c q / c p := by
  obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ :=
    Finset.two_lt_card_iff.mp (show 2 <
      (Finset.univ.filter fun j => 3 ≤ (nonzeroCoordinates (A j)).card).card by omega)
  have han : 3 ≤ (nonzeroCoordinates (A a)).card := (Finset.mem_filter.mp ha).2
  have hbn : 3 ≤ (nonzeroCoordinates (A b)).card := (Finset.mem_filter.mp hb).2
  have hdn : 3 ≤ (nonzeroCoordinates (A d)).card := (Finset.mem_filter.mp hd).2
  rcases lt_or_gt_of_ne (hc a) with ha | ha <;>
    rcases lt_or_gt_of_ne (hc b) with hb | hb <;>
    rcases lt_or_gt_of_ne (hc d) with hd | hd
  · exact ⟨a,b,hab,han,hbn,div_pos_of_neg_of_neg hb ha⟩
  · exact ⟨a,b,hab,han,hbn,div_pos_of_neg_of_neg hb ha⟩
  · exact ⟨a,d,had,han,hdn,div_pos_of_neg_of_neg hd ha⟩
  · exact ⟨b,d,hbd,hbn,hdn,div_pos hd hb⟩
  · exact ⟨b,d,hbd,hbn,hdn,div_pos_of_neg_of_neg hd hb⟩
  · exact ⟨a,d,had,han,hdn,div_pos hd ha⟩
  · exact ⟨a,b,hab,han,hbn,div_pos hb ha⟩
  · exact ⟨a,b,hab,han,hbn,div_pos hb ha⟩

/-- Four invariant features cannot decode Max4 if at least three rows are
nonroots, every input coordinate is omitted by a row, and every coordinate
is used by at least two rows. This is a universal exclusion, with no circuit
classification hypotheses and no condition on second hidden width. -/
theorem no_four_features_with_three_nonroots (A : Fin 4 → Point 4)
    (ell : Point 4) (Phi : (Fin 4 → ℝ) → ℝ)
    (h : ∀ x, Maximum 4 x = lin ell x + Phi (fun j => relu (lin (A j) x)))
    (hph : ∀ z t, 0 < t → Phi (t • z) = t * Phi z)
    (hsum : ∀ j, ∑ i, A j i = 0)
    (hcover : ∀ i, ∃ j, A j i = 0)
    (hused : ∀ i, ∃ j k, j ≠ k ∧ A j i ≠ 0 ∧ A k i ≠ 0)
    (hn : 3 ≤ (Finset.univ.filter fun j => 3 ≤ (nonzeroCoordinates (A j)).card).card) :
    False := by
  classical
  have hkernel := factorization_kernel_diagonal A ell Phi h
  have hnorm := factorization_readout_normalized A ell Phi h hsum
  obtain ⟨c, hc, hrel⟩ := exists_circuit_relation A hsum
  by_cases hfull : ∀ v, c v ≠ 0
  · obtain ⟨p, q, hpq, hpn, hqn, hratio⟩ := same_sign_nonroot_pair A c hfull hn
    by_cases hpall : ∀ j, 0 < c j
    · exact no_positive_circuit_with_two_nonroots A ell Phi h hph hnorm hsum hcover
        c hpall hrel hkernel p q hpq hpn hqn
    by_cases hnall : ∀ j, c j < 0
    · have hc' : ∀ j, 0 < (-c) j := fun j => neg_pos.mpr (hnall j)
      have hrel' : ∀ x, ∑ j, (-c) j * lin (A j) x = 0 := by
        intro x
        simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hrel x, neg_zero]
      exact no_positive_circuit_with_two_nonroots A ell Phi h hph hnorm hsum hcover
        (-c) hc' hrel' hkernel p q hpq hpn hqn
    push_neg at hpall hnall
    obtain ⟨s, hs⟩ := hpall
    obtain ⟨r, hr⟩ := hnall
    exact no_mixed_circuit_with_same_sign_nonroots A ell Phi h hph hsum hkernel c hrel
      r s (lt_of_le_of_ne hr (Ne.symm (hfull r)))
      (lt_of_le_of_ne hs (hfull s)) p q hpq (hfull p) hratio hpn hqn
  · push_neg at hfull
    obtain ⟨v, hv⟩ := hfull
    have htriple : ∀ i, ∃ k, k ≠ v ∧ A k i ≠ 0 := by
      intro i
      obtain ⟨j,k,hjk,hj,hk⟩ := hused i
      by_cases hjv : j = v
      · exact ⟨k, fun hkv => hjk (hjv.trans hkv.symm), hk⟩
      · exact ⟨j,hjv,hj⟩
    exact no_circuit_with_covered_dependent_triple A ell Phi h hsum hkernel c hc hrel v hv htriple

end MaxCaterpillar.Fiber.Count65.ZeroOneRoots
