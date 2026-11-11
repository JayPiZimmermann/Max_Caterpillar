import MaxCaterpillar.Fiber.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Tactic.Continuity

/-! # Exact motion of an unused second-hidden-layer neuron

A zero outgoing coefficient permits arbitrary changes to that neuron's
incoming row and bias. This elementary path is used to install an extra
comparison or to permute active neuron roles using a spare slot.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber

open BigOperators

variable {N h₁ h₂ : ℕ}

/-- Replace one second-hidden-layer affine preactivation, keeping its outgoing
coefficient and every other parameter unchanged. -/
def replaceSecond (net : Network N h₁ h₂) (k : Fin h₂)
    (row : Fin h₁ → ℝ) (bias : ℝ) : Network N h₁ h₂ :=
  {net with W₂ := Function.update net.W₂ k row, b₂ := Function.update net.b₂ k bias}

theorem replaceSecond_eval (net : Network N h₁ h₂) (k : Fin h₂)
    (hk : net.w₃ k = 0) (row : Fin h₁ → ℝ) (bias : ℝ) (x : Point N) :
    (replaceSecond net k row bias).eval x = net.eval x := by
  unfold Network.eval replaceSecond
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : j = k
  · subst j
    simp [hk]
  · simp [Function.update_noteq h]

/-- Linear parameter motion of an unused second neuron to a prescribed affine
preactivation. The output coefficient is unchanged throughout. -/
def unusedSecondMove (net : Network N h₁ h₂) (k : Fin h₂)
    (row : Fin h₁ → ℝ) (bias t : ℝ) : Network N h₁ h₂ :=
  replaceSecond net k ((1-t) • net.W₂ k + t • row)
    ((1-t) * net.b₂ k + t * bias)

theorem unusedSecondMove_eval (net : Network N h₁ h₂) (k : Fin h₂)
    (hk : net.w₃ k = 0) (row : Fin h₁ → ℝ) (bias t : ℝ) (x : Point N) :
    (unusedSecondMove net k row bias t).eval x = net.eval x :=
  replaceSecond_eval net k hk _ _ x

theorem unusedSecondMove_zero (net : Network N h₁ h₂) (k : Fin h₂)
    (row : Fin h₁ → ℝ) (bias : ℝ) : unusedSecondMove net k row bias 0 = net := by
  simp [unusedSecondMove, replaceSecond]

theorem unusedSecondMove_one (net : Network N h₁ h₂) (k : Fin h₂)
    (row : Fin h₁ → ℝ) (bias : ℝ) :
    unusedSecondMove net k row bias 1 = replaceSecond net k row bias := by
  simp [unusedSecondMove]

theorem continuous_unusedSecondMove (net : Network N h₁ h₂) (k : Fin h₂)
    (row : Fin h₁ → ℝ) (bias : ℝ) :
    Continuous (unusedSecondMove net k row bias) := by
  apply (continuous_network_iff _).2
  refine ⟨continuous_const, continuous_const, ?_, ?_, continuous_const, continuous_const⟩
  · apply continuous_pi
    intro j
    by_cases h : j = k
    · subst j
      simp only [unusedSecondMove, replaceSecond, Function.update_same]
      apply continuous_pi
      intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      continuity
    · simp only [unusedSecondMove, replaceSecond, Function.update_noteq h]
      exact continuous_const
  · apply continuous_pi
    intro j
    by_cases h : j = k
    · subst j
      simp only [unusedSecondMove, replaceSecond, Function.update_same]
      continuity
    · simp only [unusedSecondMove, replaceSecond, Function.update_noteq h]
      exact continuous_const

/-- The motion stays in the all-input exact fiber. -/
noncomputable def unusedSecondPoint [NeZero N] (net : ExactFiber N h₁ h₂) (k : Fin h₂)
    (hk : net.val.w₃ k = 0) (row : Fin h₁ → ℝ) (bias t : ℝ) :
    ExactFiber N h₁ h₂ :=
  ⟨unusedSecondMove net.val k row bias t, fun x =>
    (unusedSecondMove_eval net.val k hk row bias t x).trans (net.property x)⟩

theorem continuous_unusedSecondPoint [NeZero N] (net : ExactFiber N h₁ h₂) (k : Fin h₂)
    (hk : net.val.w₃ k = 0) (row : Fin h₁ → ℝ) (bias : ℝ) :
    Continuous (unusedSecondPoint net k hk row bias) :=
  (continuous_unusedSecondMove net.val k row bias).subtype_mk _

noncomputable def unusedSecondPath [NeZero N] (net : ExactFiber N h₁ h₂) (k : Fin h₂)
    (hk : net.val.w₃ k = 0) (row : Fin h₁ → ℝ) (bias : ℝ) :
    Path net (unusedSecondPoint net k hk row bias 1) where
  toFun t := unusedSecondPoint net k hk row bias t
  continuous_toFun := (continuous_unusedSecondPoint net k hk row bias).comp continuous_subtype_val
  source' := by
    apply Subtype.ext
    exact unusedSecondMove_zero net.val k row bias
  target' := rfl

end MaxCaterpillar.Fiber
