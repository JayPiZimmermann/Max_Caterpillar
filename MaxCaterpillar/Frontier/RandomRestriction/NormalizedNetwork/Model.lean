import MaxCaterpillar.Frontier.Asymptotics

/-! # Indexed homogeneous networks with the skips produced by localization

This is a presentation, not an assumed reduction theorem. The original first
and second neuron indices are retained, including zero slots. Translation
normalization is an explicit separate predicate.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction
open BigOperators

structure NormalizedNetwork (N h₁ h₂ : ℕ) where
  A : Fin h₁ → Point N
  U : Fin h₂ → Point N
  W : Fin h₂ → Fin h₁ → ℝ
  L : Point N
  B : Fin h₁ → ℝ
  d : Fin h₂ → ℝ

namespace NormalizedNetwork
variable {N h₁ h₂ : ℕ}

noncomputable def inner (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂)
    (x : Point N) : ℝ := lin (net.U k) x + ∑ j, net.W k j * relu (lin (net.A j) x)

noncomputable def eval (net : NormalizedNetwork N h₁ h₂) (x : Point N) : ℝ :=
  lin net.L x + (∑ j, net.B j * relu (lin (net.A j) x)) +
    ∑ k, net.d k * relu (net.inner k x)

/-- Every surviving first form and every second linear skip has zero sum;
the linear output carries the unit translation slope of MAX. -/
def TranslationNormalized (net : NormalizedNetwork N h₁ h₂) : Prop :=
  (∀ j, ∑ i, net.A j i = 0) ∧ (∀ k, ∑ i, net.U k i = 0) ∧ ∑ i, net.L i = 1

noncomputable def rowSupport (a : Point N) : Finset (Fin N) :=
  Finset.univ.filter fun i => a i ≠ 0

@[simp] theorem mem_rowSupport (a : Point N) (i : Fin N) :
    i ∈ rowSupport a ↔ a i ≠ 0 := by
  classical
  simp [rowSupport]

/-- Feeding concerns the nonlinear first-to-second coefficients, rather than
the unrestricted output-only first-layer terms. -/
def Feeding (net : NormalizedNetwork N h₁ h₂) (j : Fin h₁) : Prop :=
  ∃ k, net.W k j ≠ 0

@[simp] theorem inner_zero (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂) :
    net.inner k 0 = 0 := by
  simp [inner,lin_zero_right,relu]

@[simp] theorem eval_zero (net : NormalizedNetwork N h₁ h₂) : net.eval 0 = 0 := by
  simp [eval,lin_zero_right,relu]

end NormalizedNetwork
end MaxCaterpillar.Frontier.RandomRestriction
