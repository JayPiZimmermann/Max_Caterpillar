import MaxCaterpillar.Fiber.Symmetry

/-! # The allowed symmetries act by homeomorphisms on the exact fiber

Every generating positive rescaling or neuron/input permutation is a
homeomorphism of the actual parameter-space fiber. The reciprocal rescalings
are only used under strict positivity, including when some network weights
themselves vanish.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber

variable {N h₁ h₂ : ℕ}

theorem scaleFirst_inv_scaleFirst (net : Network N h₁ h₂) (s : Fin h₁ → ℝ)
    (hs : ∀ j, 0 < s j) :
    scaleFirst (scaleFirst net s) (fun j => (s j)⁻¹) = net := by
  cases net
  dsimp only [scaleFirst]
  congr 1
  · funext j i
    simp [mul_assoc, ne_of_gt (hs j)]
  · funext j
    simp [mul_assoc, ne_of_gt (hs j)]
  · funext k j
    simp [div_eq_mul_inv, mul_assoc, ne_of_gt (hs j)]

theorem scaleFirst_scaleFirst_inv (net : Network N h₁ h₂) (s : Fin h₁ → ℝ)
    (hs : ∀ j, 0 < s j) :
    scaleFirst (scaleFirst net (fun j => (s j)⁻¹)) s = net := by
  simpa only [inv_inv] using
    scaleFirst_inv_scaleFirst net (fun j => (s j)⁻¹) (fun j => inv_pos.mpr (hs j))

theorem scaleSecond_inv_scaleSecond (net : Network N h₁ h₂) (s : Fin h₂ → ℝ)
    (hs : ∀ k, 0 < s k) :
    scaleSecond (scaleSecond net s) (fun k => (s k)⁻¹) = net := by
  cases net
  dsimp only [scaleSecond]
  congr 1
  · funext k j
    simp [mul_assoc, ne_of_gt (hs k)]
  · funext k
    simp [mul_assoc, ne_of_gt (hs k)]
  · funext k
    simp [div_eq_mul_inv, mul_assoc, ne_of_gt (hs k)]

theorem scaleSecond_scaleSecond_inv (net : Network N h₁ h₂) (s : Fin h₂ → ℝ)
    (hs : ∀ k, 0 < s k) :
    scaleSecond (scaleSecond net (fun k => (s k)⁻¹)) s = net := by
  simpa only [inv_inv] using
    scaleSecond_inv_scaleSecond net (fun k => (s k)⁻¹) (fun k => inv_pos.mpr (hs k))

theorem permuteHidden_inv_permuteHidden (net : Network N h₁ h₂)
    (p : Equiv.Perm (Fin h₁)) (q : Equiv.Perm (Fin h₂)) :
    permuteHidden (permuteHidden net p q) p.symm q.symm = net := by
  cases net
  simp [permuteHidden]

theorem permuteHidden_permuteHidden_inv (net : Network N h₁ h₂)
    (p : Equiv.Perm (Fin h₁)) (q : Equiv.Perm (Fin h₂)) :
    permuteHidden (permuteHidden net p.symm q.symm) p q = net := by
  simpa only [Equiv.symm_symm] using
    permuteHidden_inv_permuteHidden net p.symm q.symm

theorem permuteInputs_inv_permuteInputs (net : Network N h₁ h₂)
    (p : Equiv.Perm (Fin N)) :
    permuteInputs (permuteInputs net p) p.symm = net := by
  cases net
  simp [permuteInputs]

theorem permuteInputs_permuteInputs_inv (net : Network N h₁ h₂)
    (p : Equiv.Perm (Fin N)) :
    permuteInputs (permuteInputs net p.symm) p = net := by
  simpa only [Equiv.symm_symm] using permuteInputs_inv_permuteInputs net p.symm

variable [NeZero N]

noncomputable def scaleFirstHomeomorph (s : Fin h₁ → ℝ) (hs : ∀ j, 0 < s j) :
    ExactFiber N h₁ h₂ ≃ₜ ExactFiber N h₁ h₂ where
  toFun := scaleFirstFiber s hs
  invFun := scaleFirstFiber (fun j => (s j)⁻¹) (fun j => inv_pos.mpr (hs j))
  left_inv net := Subtype.ext (scaleFirst_inv_scaleFirst net.val s hs)
  right_inv net := Subtype.ext (scaleFirst_scaleFirst_inv net.val s hs)
  continuous_toFun := continuous_scaleFirstFiber s hs
  continuous_invFun := continuous_scaleFirstFiber (fun j => (s j)⁻¹)
    (fun j => inv_pos.mpr (hs j))

noncomputable def scaleSecondHomeomorph (s : Fin h₂ → ℝ) (hs : ∀ k, 0 < s k) :
    ExactFiber N h₁ h₂ ≃ₜ ExactFiber N h₁ h₂ where
  toFun := scaleSecondFiber s hs
  invFun := scaleSecondFiber (fun k => (s k)⁻¹) (fun k => inv_pos.mpr (hs k))
  left_inv net := Subtype.ext (scaleSecond_inv_scaleSecond net.val s hs)
  right_inv net := Subtype.ext (scaleSecond_scaleSecond_inv net.val s hs)
  continuous_toFun := continuous_scaleSecondFiber s hs
  continuous_invFun := continuous_scaleSecondFiber (fun k => (s k)⁻¹)
    (fun k => inv_pos.mpr (hs k))

def permuteHiddenHomeomorph (p : Equiv.Perm (Fin h₁)) (q : Equiv.Perm (Fin h₂)) :
    ExactFiber N h₁ h₂ ≃ₜ ExactFiber N h₁ h₂ where
  toFun := permuteHiddenFiber p q
  invFun := permuteHiddenFiber p.symm q.symm
  left_inv net := Subtype.ext (permuteHidden_inv_permuteHidden net.val p q)
  right_inv net := Subtype.ext (permuteHidden_permuteHidden_inv net.val p q)
  continuous_toFun := continuous_permuteHiddenFiber p q
  continuous_invFun := continuous_permuteHiddenFiber p.symm q.symm

def permuteInputsHomeomorph (p : Equiv.Perm (Fin N)) :
    ExactFiber N h₁ h₂ ≃ₜ ExactFiber N h₁ h₂ where
  toFun := permuteInputsFiber p
  invFun := permuteInputsFiber p.symm
  left_inv net := Subtype.ext (permuteInputs_inv_permuteInputs net.val p)
  right_inv net := Subtype.ext (permuteInputs_permuteInputs_inv net.val p)
  continuous_toFun := continuous_permuteInputsFiber p
  continuous_invFun := continuous_permuteInputsFiber p.symm

/-- Every allowed generator is realized by a global homeomorphism, whose
action at every point remains within the same symmetry equivalence class. -/
theorem symmetryStep_homeomorph {a b : ExactFiber N h₁ h₂} (h : SymmetryStep a b) :
    ∃ e : ExactFiber N h₁ h₂ ≃ₜ ExactFiber N h₁ h₂,
      e a = b ∧ ∀ x, EqvGen SymmetryStep x (e x) := by
  cases h with
  | first s hs =>
      exact ⟨scaleFirstHomeomorph s hs, rfl,
        fun x => EqvGen.rel _ _ (SymmetryStep.first x s hs)⟩
  | second s hs =>
      exact ⟨scaleSecondHomeomorph s hs, rfl,
        fun x => EqvGen.rel _ _ (SymmetryStep.second x s hs)⟩
  | hidden p q =>
      exact ⟨permuteHiddenHomeomorph p q, rfl,
        fun x => EqvGen.rel _ _ (SymmetryStep.hidden x p q)⟩
  | input p =>
      exact ⟨permuteInputsHomeomorph p, rfl,
        fun x => EqvGen.rel _ _ (SymmetryStep.input x p)⟩

end MaxCaterpillar.Fiber
