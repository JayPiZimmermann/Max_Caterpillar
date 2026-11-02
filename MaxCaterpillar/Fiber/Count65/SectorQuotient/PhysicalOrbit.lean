import MaxCaterpillar.Fiber.Symmetry

/-! A finite composition of genuine network symmetries has a single physical
coordinate witness, including every bias and every weight array. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

variable {N h₁ h₂ : ℕ}

structure PhysicalOrbitWitness (a b : Network N h₁ h₂) where
  s₁ : Fin h₁ → ℝ
  s₂ : Fin h₂ → ℝ
  p₁ : Equiv.Perm (Fin h₁)
  p₂ : Equiv.Perm (Fin h₂)
  q : Equiv.Perm (Fin N)
  positive₁ : ∀ j, 0 < s₁ j
  positive₂ : ∀ k, 0 < s₂ k
  first_weights : ∀ j i, b.W₁ j i = s₁ j * a.W₁ (p₁ j) (q i)
  first_bias : ∀ j, b.b₁ j = s₁ j * a.b₁ (p₁ j)
  second_weights : ∀ k j, b.W₂ k j = s₂ k * a.W₂ (p₂ k) (p₁ j) / s₁ j
  second_bias : ∀ k, b.b₂ k = s₂ k * a.b₂ (p₂ k)
  output_weights : ∀ k, b.w₃ k = a.w₃ (p₂ k) / s₂ k
  output_bias : b.b₃ = a.b₃

namespace PhysicalOrbitWitness

noncomputable def refl (a : Network N h₁ h₂) : PhysicalOrbitWitness a a where
  s₁ := fun _ => 1
  s₂ := fun _ => 1
  p₁ := Equiv.refl _
  p₂ := Equiv.refl _
  q := Equiv.refl _
  positive₁ := fun _ => zero_lt_one
  positive₂ := fun _ => zero_lt_one
  first_weights := fun _ _ => by simp only [Equiv.refl_apply, one_mul]
  first_bias := fun _ => by simp only [Equiv.refl_apply, one_mul]
  second_weights := fun _ _ => by simp only [Equiv.refl_apply, one_mul, div_one]
  second_bias := fun _ => by simp only [Equiv.refl_apply, one_mul]
  output_weights := fun _ => by simp only [Equiv.refl_apply, div_one]
  output_bias := rfl

noncomputable def trans {a b c : Network N h₁ h₂}
    (u : PhysicalOrbitWitness a b) (v : PhysicalOrbitWitness b c) :
    PhysicalOrbitWitness a c where
  s₁ := fun j => v.s₁ j * u.s₁ (v.p₁ j)
  s₂ := fun k => v.s₂ k * u.s₂ (v.p₂ k)
  p₁ := v.p₁.trans u.p₁
  p₂ := v.p₂.trans u.p₂
  q := v.q.trans u.q
  positive₁ := fun j => mul_pos (v.positive₁ j) (u.positive₁ (v.p₁ j))
  positive₂ := fun k => mul_pos (v.positive₂ k) (u.positive₂ (v.p₂ k))
  first_weights := by
    intro j i
    rw [v.first_weights, u.first_weights]
    simp only [Equiv.trans_apply]
    ring
  first_bias := by
    intro j
    rw [v.first_bias, u.first_bias]
    simp only [Equiv.trans_apply]
    ring
  second_weights := by
    intro k j
    rw [v.second_weights, u.second_weights]
    simp only [Equiv.trans_apply]
    field_simp [(u.positive₁ (v.p₁ j)).ne', (v.positive₁ j).ne']
    ring
  second_bias := by
    intro k
    rw [v.second_bias, u.second_bias]
    simp only [Equiv.trans_apply]
    ring
  output_weights := by
    intro k
    rw [v.output_weights, u.output_weights]
    simp only [Equiv.trans_apply]
    rw [div_div, mul_comm (u.s₂ (v.p₂ k)) (v.s₂ k)]
  output_bias := v.output_bias.trans u.output_bias

noncomputable def symm {a b : Network N h₁ h₂} (u : PhysicalOrbitWitness a b) :
    PhysicalOrbitWitness b a where
  s₁ := fun j => (u.s₁ (u.p₁.symm j))⁻¹
  s₂ := fun k => (u.s₂ (u.p₂.symm k))⁻¹
  p₁ := u.p₁.symm
  p₂ := u.p₂.symm
  q := u.q.symm
  positive₁ := fun j => inv_pos.mpr (u.positive₁ (u.p₁.symm j))
  positive₂ := fun k => inv_pos.mpr (u.positive₂ (u.p₂.symm k))
  first_weights := by
    intro j i
    rw [u.first_weights]
    simp only [Equiv.apply_symm_apply]
    field_simp [(u.positive₁ (u.p₁.symm j)).ne']
    ring
  first_bias := by
    intro j
    rw [u.first_bias]
    simp only [Equiv.apply_symm_apply]
    field_simp [(u.positive₁ (u.p₁.symm j)).ne']
    ring
  second_weights := by
    intro k j
    rw [u.second_weights]
    simp only [Equiv.apply_symm_apply]
    field_simp [(u.positive₁ (u.p₁.symm j)).ne', (u.positive₂ (u.p₂.symm k)).ne']
    ring
  second_bias := by
    intro k
    rw [u.second_bias]
    simp only [Equiv.apply_symm_apply]
    field_simp [(u.positive₂ (u.p₂.symm k)).ne']
    ring
  output_weights := by
    intro k
    rw [u.output_weights]
    simp only [Equiv.apply_symm_apply]
    field_simp [(u.positive₂ (u.p₂.symm k)).ne']
  output_bias := u.output_bias.symm

noncomputable def first (a : Network N h₁ h₂) (s : Fin h₁ → ℝ)
    (hs : ∀ j, 0 < s j) : PhysicalOrbitWitness a (scaleFirst a s) where
  s₁ := s
  s₂ := fun _ => 1
  p₁ := Equiv.refl _
  p₂ := Equiv.refl _
  q := Equiv.refl _
  positive₁ := hs
  positive₂ := fun _ => zero_lt_one
  first_weights := fun _ _ => rfl
  first_bias := fun _ => rfl
  second_weights := fun _ _ => by simp only [scaleFirst, Equiv.refl_apply, one_mul]
  second_bias := fun _ => by simp only [scaleFirst, Equiv.refl_apply, one_mul]
  output_weights := fun _ => by simp only [scaleFirst, Equiv.refl_apply, div_one]
  output_bias := rfl

noncomputable def second (a : Network N h₁ h₂) (s : Fin h₂ → ℝ)
    (hs : ∀ k, 0 < s k) : PhysicalOrbitWitness a (scaleSecond a s) where
  s₁ := fun _ => 1
  s₂ := s
  p₁ := Equiv.refl _
  p₂ := Equiv.refl _
  q := Equiv.refl _
  positive₁ := fun _ => zero_lt_one
  positive₂ := hs
  first_weights := fun _ _ => by simp only [scaleSecond, Equiv.refl_apply, one_mul]
  first_bias := fun _ => by simp only [scaleSecond, Equiv.refl_apply, one_mul]
  second_weights := fun _ _ => by simp only [scaleSecond, Equiv.refl_apply, div_one]
  second_bias := fun _ => rfl
  output_weights := fun _ => rfl
  output_bias := rfl

noncomputable def hidden (a : Network N h₁ h₂)
    (p : Equiv.Perm (Fin h₁)) (r : Equiv.Perm (Fin h₂)) :
    PhysicalOrbitWitness a (permuteHidden a p r) where
  s₁ := fun _ => 1
  s₂ := fun _ => 1
  p₁ := p
  p₂ := r
  q := Equiv.refl _
  positive₁ := fun _ => zero_lt_one
  positive₂ := fun _ => zero_lt_one
  first_weights := fun _ _ => by simp only [permuteHidden, Equiv.refl_apply, one_mul]
  first_bias := fun _ => by simp only [permuteHidden, one_mul]
  second_weights := fun _ _ => by simp only [permuteHidden, one_mul, div_one]
  second_bias := fun _ => by simp only [permuteHidden, one_mul]
  output_weights := fun _ => by simp only [permuteHidden, div_one]
  output_bias := rfl

noncomputable def input (a : Network N h₁ h₂) (p : Equiv.Perm (Fin N)) :
    PhysicalOrbitWitness a (permuteInputs a p) where
  s₁ := fun _ => 1
  s₂ := fun _ => 1
  p₁ := Equiv.refl _
  p₂ := Equiv.refl _
  q := p
  positive₁ := fun _ => zero_lt_one
  positive₂ := fun _ => zero_lt_one
  first_weights := fun _ _ => by simp only [permuteInputs, Equiv.refl_apply, one_mul]
  first_bias := fun _ => by simp only [permuteInputs, Equiv.refl_apply, one_mul]
  second_weights := fun _ _ => by simp only [permuteInputs, Equiv.refl_apply, one_mul, div_one]
  second_bias := fun _ => by simp only [permuteInputs, Equiv.refl_apply, one_mul]
  output_weights := fun _ => by simp only [permuteInputs, Equiv.refl_apply, div_one]
  output_bias := rfl

end PhysicalOrbitWitness

variable [NeZero N]

theorem physicalOrbit_of_symmetryStep {a b : ExactFiber N h₁ h₂}
    (h : SymmetryStep a b) : Nonempty (PhysicalOrbitWitness a.val b.val) := by
  cases h with
  | first s hs => exact ⟨PhysicalOrbitWitness.first a.val s hs⟩
  | second s hs => exact ⟨PhysicalOrbitWitness.second a.val s hs⟩
  | hidden p q => exact ⟨PhysicalOrbitWitness.hidden a.val p q⟩
  | input p => exact ⟨PhysicalOrbitWitness.input a.val p⟩

theorem physicalOrbit_of_symmetry {a b : ExactFiber N h₁ h₂}
    (h : EqvGen SymmetryStep a b) : Nonempty (PhysicalOrbitWitness a.val b.val) := by
  induction h with
  | rel a b h => exact physicalOrbit_of_symmetryStep h
  | refl a => exact ⟨PhysicalOrbitWitness.refl a.val⟩
  | symm a b _ ih => obtain ⟨u⟩ := ih; exact ⟨u.symm⟩
  | trans a b c _ _ hab hbc =>
    obtain ⟨u⟩ := hab
    obtain ⟨v⟩ := hbc
    exact ⟨u.trans v⟩

theorem physicalOrbit_of_quotientMk_eq {a b : ExactFiber N h₁ h₂}
    (h : quotientMk a = quotientMk b) : Nonempty (PhysicalOrbitWitness a.val b.val) :=
  physicalOrbit_of_symmetry ((quotientMk_eq_iff a b).mp h)

end MaxCaterpillar.Fiber.Count65.SectorQuotient
