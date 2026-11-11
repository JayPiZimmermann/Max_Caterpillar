import MaxCaterpillar.Fiber.Paired65.RecessionAtoms

/-!
# Arbitrary-slope scalar hinges normalize to signed atoms

Zero slopes and zero output weights remain permitted. Reversing a hinge adds
an affine term; that term is retained explicitly before invoking atom balance.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Frontier

/-- Exact normalization of a scalar affine ReLU, including zero slope. -/
theorem affine_relu_normalization (C a t : ℝ) :
    relu (C+a*t) = |a| * relu (t-(-C/a)) +
      (if a<0 then a else 0)*t +
      (if a<0 then C else if a=0 then relu C else 0) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [if_pos ha, if_pos ha, abs_of_neg ha]
    have he : -(C+a*t) = (-a)*(t-(-C/a)) := by
      field_simp [ha.ne]
      ring
    have h := relu_sub_relu_neg (C+a*t)
    rw [he, relu_mul_pos (neg_pos.mpr ha)] at h
    linear_combination h
  · subst a
    simp
  · rw [if_neg (not_lt.mpr ha.le), if_neg (not_lt.mpr ha.le),
      if_neg ha.ne', abs_of_pos ha]
    simp only [zero_mul, add_zero]
    have he : C+a*t = a*(t-(-C/a)) := by
      field_simp [ha.ne']
      ring
    rw [he, relu_mul_pos ha]

/-- An arbitrary signed scalar hinge identity gives exact atom balance after
normalization. The affine orientation remainder is part of the proof. -/
theorem atomBalance_of_general_affine_relu_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d C a : ι → ℝ) (A B : ℝ)
    (h : ∀ t : ℝ, (∑ i, d i*relu (C i+a i*t)) = relu t+A*t+B) :
    Paired65.AtomBalance (fun i => d i*|a i|) (fun i => -C i/a i) := by
  let S : ℝ := ∑ i, d i*(if a i<0 then a i else 0)
  let I : ℝ := ∑ i, d i*(if a i<0 then C i else if a i=0 then relu (C i) else 0)
  apply Paired65.atomBalance_of_affine_relu_identity _ _ (A-S) (B-I)
  intro t
  have he : (∑ i, d i*relu (C i+a i*t)) =
      (∑ i, (d i*|a i|)*relu (t-(-C i/a i))) + S*t+I := by
    simp only [S, I, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [affine_relu_normalization]
    ring
  have hh := h t
  nlinarith only [he, hh]

end MaxCaterpillar.Fiber.Count65.Paired
