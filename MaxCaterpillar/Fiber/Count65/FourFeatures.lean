import MaxCaterpillar.Fiber.Count65.InvariantReduction

/-! # The four invariant features of an actual Max4 network

The chosen enumeration is a bijection with the actual zero-sum first rows.
No root, code-pair, or coefficient-case classification is assumed.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65
open BigOperators MaxCaterpillar.Frontier

/-- Recovering a maximum up to a linear readout retains every input difference. -/
theorem factorization_kernel_diagonal {N m : ℕ} [NeZero N]
    (A : Fin m → Point N) (ell : Point N) (Phi : (Fin m → ℝ) → ℝ)
    (h : ∀ x, Maximum N x = lin ell x + Phi (fun j => relu (lin (A j) x)))
    (hzero : Phi 0 = 0) (w : Point N) (hw : ∀ j, lin (A j) w = 0) :
    ∃ t : ℝ, w = diag t := by
  have hp : (fun j => relu (lin (A j) w)) = 0 := by
    funext j
    rw [hw j]
    norm_num [relu]
  have hm : (fun j => relu (lin (A j) (-w))) = 0 := by
    funext j
    rw [lin_neg_right, hw j]
    norm_num [relu]
  have hplus := h w
  have hminus := h (-w)
  rw [hp, hzero, add_zero] at hplus
  rw [hm, hzero, add_zero, lin_neg_right] at hminus
  refine ⟨lin ell w, funext fun i => ?_⟩
  have hpbound := le_Maximum w i
  have hmbound := le_Maximum (-w) i
  rw [hplus] at hpbound
  rw [hminus] at hmbound
  change w i = lin ell w
  simp only [Pi.neg_apply] at hmbound
  linarith only [hpbound, hmbound]

noncomputable def invariantRows (net : Network 4 6 5) : Finset (Fin 6) :=
  Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0

/-- A concrete four-feature representation, selected from exactly the actual
invariant first rows. The enumeration and its source are part of the conclusion. -/
theorem four_feature_factorization (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (invariantRows net).card = 4) :
    ∃ e : Fin 4 ≃ invariantRows net,
      ∃ ell : Point 4, ∃ Phi : (Fin 4 → ℝ) → ℝ,
        (∀ x, Maximum 4 x = lin ell x +
          Phi (fun k => relu (lin (net.W₁ (e k).val) x))) ∧
        Phi 0 = 0 ∧
        (∀ z t, 0 < t → Phi (t • z) = t * Phi z) ∧
        (∑ i, ell i) = 1 ∧
        (∀ k, (∑ i, net.W₁ (e k).val i) = 0) ∧
        (∀ i, ∃ k, net.W₁ (e k).val i = 0) ∧
        (∀ w, (∀ k, lin (net.W₁ (e k).val) w = 0) → ∃ t, w = diag t) := by
  classical
  let e : Fin 4 ≃ invariantRows net := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe, hcard])
  obtain ⟨ell, Phi, hfactor, hzero, hhom, hell⟩ :=
    four_invariant_factorization net hnet hcard
  let extend : (Fin 4 → ℝ) → (Fin 6 → ℝ) := fun z j =>
    if hj : j ∈ invariantRows net then z (e.symm ⟨j, hj⟩) else 0
  let Phi4 : (Fin 4 → ℝ) → ℝ := fun z => Phi (extend z)
  have hstate : ∀ x, extend (fun k => relu (lin (net.W₁ (e k).val) x)) =
      invariantState net x := by
    intro x
    funext j
    by_cases hj : j ∈ invariantRows net
    · have hs : net.toZ.s j = 0 := by
        simpa only [invariantRows, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      simp only [extend, dif_pos hj, Equiv.apply_symm_apply, invariantState, ZNet.rho,
        hs, if_true]
      rfl
    · have hs : net.toZ.s j ≠ 0 := by
        simpa only [invariantRows, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      simp only [extend, dif_neg hj, invariantState, ZNet.rho, if_neg hs]
  have hfactor4 : ∀ x, Maximum 4 x = lin ell x +
      Phi4 (fun k => relu (lin (net.W₁ (e k).val) x)) := by
    intro x
    simpa only [Phi4, hstate] using hfactor x
  have hzero4 : Phi4 0 = 0 := by
    change Phi (extend 0) = 0
    have he : extend 0 = 0 := by
      funext j
      simp only [extend, Pi.zero_apply]
      split_ifs <;> rfl
    rw [he, hzero]
  refine ⟨e, ell, Phi4, hfactor4, hzero4, ?_, ?_, ?_, ?_, ?_⟩
  · intro z t ht
    change Phi (extend (t • z)) = t * Phi (extend z)
    have he : extend (t • z) = t • extend z := by
      funext j
      simp only [extend, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [he]
    exact hhom (extend z) t ht
  · simpa only [lin_diag, one_mul] using hell
  · intro k
    exact (Finset.mem_filter.mp (e k).property).2
  · intro i
    obtain ⟨j, hj, hji⟩ := max4_invariant_row_at_top_tie net hnet i
    have hjm : j ∈ invariantRows net := by simp [invariantRows, hj]
    refine ⟨e.symm ⟨j, hjm⟩, ?_⟩
    simpa only [Equiv.apply_symm_apply] using hji
  · exact fun w hw => factorization_kernel_diagonal
      (fun k => net.W₁ (e k).val) ell Phi4 hfactor4 hzero4 w hw

#print axioms four_feature_factorization
end MaxCaterpillar.Fiber.Count65
