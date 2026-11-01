import MaxCaterpillar.Fiber.Symmetry
import MaxCaterpillar.Frontier.Main

/-! # Feasibility of the exact Max4 fiber

These theorems transfer the existing width frontier to the parameter fiber and
its symmetry quotient. They assert existence, not a connected-component count.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber

variable {N h₁ h₂ : ℕ}

theorem symmetryQuotient_nonempty_iff [NeZero N] :
    Nonempty (SymmetryQuotient N h₁ h₂) ↔ Nonempty (ExactFiber N h₁ h₂) := by
  constructor
  · rintro ⟨q⟩
    obtain ⟨net, _⟩ := quotientMk_surjective q
    exact ⟨net⟩
  · rintro ⟨net⟩
    exact ⟨quotientMk net⟩

/-- The all-input Max4 fiber exists exactly at widths at least `(6,3)`. -/
theorem max4_exactFiber_nonempty_iff :
    Nonempty (ExactFiber 4 h₁ h₂) ↔ 6 ≤ h₁ ∧ 3 ≤ h₂ :=
  exactFiber_nonempty_iff.trans Frontier.max4_widths_iff

/-- Taking the genuine symmetry quotient does not change the feasible widths. -/
theorem max4_symmetryQuotient_nonempty_iff :
    Nonempty (SymmetryQuotient 4 h₁ h₂) ↔ 6 ≤ h₁ ∧ 3 ≤ h₂ :=
  symmetryQuotient_nonempty_iff.trans max4_exactFiber_nonempty_iff

/-- A concrete witness in the minimal exact fiber, with the original parameter arrays. -/
noncomputable def max4_minimalPoint : ExactFiber 4 6 3 :=
  ⟨Frontier.maxFourNet, Frontier.maxFourNet_eval⟩

theorem max4_minimalPoint_zeroBiases : max4_minimalPoint.val.HasZeroBiases :=
  Frontier.maxFourNet_hasZeroBiases

end MaxCaterpillar.Fiber
