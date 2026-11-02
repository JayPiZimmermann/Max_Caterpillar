import MaxCaterpillar.Fiber.Connected64.UnusedSecond
import Mathlib.Algebra.BigOperators.Ring

/-! # Output interpolation and transfer between duplicate second neurons

These paths preserve the existing first and second hidden computations. They
are ingredients for spare-slot permutations and deletion of redundant terms.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber

open BigOperators

variable {N h₁ h₂ : ℕ}

def withOutput (net : Network N h₁ h₂) (a : Fin h₂ → ℝ) (b : ℝ) :
    Network N h₁ h₂ := {net with w₃ := a, b₃ := b}

def interpolateOutput (net : Network N h₁ h₂) (a : Fin h₂ → ℝ) (b t : ℝ) :
    Network N h₁ h₂ :=
  withOutput net ((1-t) • net.w₃ + t • a) ((1-t)*net.b₃ + t*b)

theorem interpolateOutput_eval (net : Network N h₁ h₂) (a : Fin h₂ → ℝ)
    (b t : ℝ) (x : Point N) :
    (interpolateOutput net a b t).eval x =
      (1-t)*net.eval x + t*(withOutput net a b).eval x := by
  simp only [interpolateOutput, withOutput, Network.eval, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]
  ring

theorem interpolateOutput_zero (net : Network N h₁ h₂) (a : Fin h₂ → ℝ) (b : ℝ) :
    interpolateOutput net a b 0 = net := by simp [interpolateOutput, withOutput]

theorem interpolateOutput_one (net : Network N h₁ h₂) (a : Fin h₂ → ℝ) (b : ℝ) :
    interpolateOutput net a b 1 = withOutput net a b := by simp [interpolateOutput]

theorem continuous_interpolateOutput (net : Network N h₁ h₂) (a : Fin h₂ → ℝ) (b : ℝ) :
    Continuous (interpolateOutput net a b) := by
  apply (continuous_network_iff _).2
  refine ⟨continuous_const, continuous_const, continuous_const, continuous_const, ?_, ?_⟩
  · apply continuous_pi
    intro k
    simp only [interpolateOutput, withOutput, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    continuity
  · simp only [interpolateOutput, withOutput]
    continuity

noncomputable def outputInterpolationPoint [NeZero N] (net : ExactFiber N h₁ h₂)
    (a : Fin h₂ → ℝ) (b : ℝ) (hfit : ∀ x, (withOutput net.val a b).eval x = Maximum N x)
    (t : ℝ) : ExactFiber N h₁ h₂ :=
  ⟨interpolateOutput net.val a b t, fun x => by
    rw [interpolateOutput_eval, net.property, hfit]
    ring⟩

theorem continuous_outputInterpolationPoint [NeZero N] (net : ExactFiber N h₁ h₂)
    (a : Fin h₂ → ℝ) (b : ℝ) (hfit : ∀ x, (withOutput net.val a b).eval x = Maximum N x) :
    Continuous (outputInterpolationPoint net a b hfit) :=
  (continuous_interpolateOutput net.val a b).subtype_mk _

/-- Any two exact readouts of the same hidden computations are joined by
straight interpolation in their actual output parameters. -/
noncomputable def outputInterpolationPath [NeZero N] (net : ExactFiber N h₁ h₂)
    (a : Fin h₂ → ℝ) (b : ℝ) (hfit : ∀ x, (withOutput net.val a b).eval x = Maximum N x) :
    Path net (⟨withOutput net.val a b, hfit⟩ : ExactFiber N h₁ h₂) where
  toFun t := outputInterpolationPoint net a b hfit t
  continuous_toFun := (continuous_outputInterpolationPoint net a b hfit).comp continuous_subtype_val
  source' := by
    apply Subtype.ext
    exact interpolateOutput_zero net.val a b
  target' := by
    apply Subtype.ext
    exact interpolateOutput_one net.val a b

/-- Transfer the entire output coefficient of slot `i` into slot `j`. -/
def transferOutput (a : Fin h₂ → ℝ) (i j : Fin h₂) : Fin h₂ → ℝ :=
  fun k => a k + (if k = j then a i else 0) - (if k = i then a i else 0)

theorem transferOutput_source (a : Fin h₂ → ℝ) (i j : Fin h₂) (hij : i ≠ j) :
    transferOutput a i j i = 0 := by simp [transferOutput, hij]

theorem transferOutput_target (a : Fin h₂ → ℝ) (i j : Fin h₂) (hij : i ≠ j) :
    transferOutput a i j j = a j + a i := by simp [transferOutput, Ne.symm hij]

/-- Duplicate affine preactivations allow exact output transfer. The coefficients
may have either sign; the endpoint empties the source slot. -/
theorem transferOutput_eval (net : Network N h₁ h₂) (i j : Fin h₂)
    (hrow : net.W₂ i = net.W₂ j) (hbias : net.b₂ i = net.b₂ j) (x : Point N) :
    (withOutput net (transferOutput net.w₃ i j) net.b₃).eval x = net.eval x := by
  unfold withOutput Network.eval transferOutput
  simp only [add_mul, sub_mul, ite_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hrow, hbias]
  ring

/-- The transfer is realized continuously in the exact network fiber. -/
noncomputable def duplicateTransferPath [NeZero N] (net : ExactFiber N h₁ h₂) (i j : Fin h₂)
    (hrow : net.val.W₂ i = net.val.W₂ j) (hbias : net.val.b₂ i = net.val.b₂ j) :
    Path net (⟨withOutput net.val (transferOutput net.val.w₃ i j) net.val.b₃,
      fun x => (transferOutput_eval net.val i j hrow hbias x).trans (net.property x)⟩ :
      ExactFiber N h₁ h₂) :=
  outputInterpolationPath net (transferOutput net.val.w₃ i j) net.val.b₃
    (fun x => (transferOutput_eval net.val i j hrow hbias x).trans (net.property x))

end MaxCaterpillar.Fiber
