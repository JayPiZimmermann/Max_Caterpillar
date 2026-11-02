import MaxCaterpillar.Fiber.PositiveKink
import MaxCaterpillar.Fiber.KinkCancellation
import MaxCaterpillar.Fiber.Mixed65.LinearCover

/-! # The two-root inward fork dictionary

These are arbitrary-real residual systems. No output signs, carrier normal
forms, or finite parameter alphabets are assumed by `Represents`.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion
open BigOperators MaxCaterpillar.Frontier

structure Coeff where
  a : ℝ
  b : ℝ
  r : ℝ
  s : ℝ

noncomputable def form (α β κ : ℝ) (d : Coeff) (u v w : ℝ) : ℝ :=
  d.a * relu u + d.b * relu v + d.r * relu (w - α*u - β*v) +
    d.s * relu (κ*w - α*u - β*v)

noncomputable def target (u v w : ℝ) : ℝ := max (max 0 u) (max v w)

structure ResidualSystem (ι : Type*) where
  base : Coeff
  gate : ι → Coeff
  out : ι → ℝ

noncomputable def ResidualSystem.eval {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (α β κ u v w : ℝ) : ℝ :=
  form α β κ d.base u v w + ∑ i, d.out i * relu (form α β κ (d.gate i) u v w)

def ResidualSystem.Represents {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (α β κ : ℝ) : Prop :=
  ∀ u v w, target u v w = d.eval α β κ u v w

/-- The preactivation carries the outer positive `u=w` facet. -/
def OuterU (κ : ℝ) (d : Coeff) : Prop :=
  d.r + d.s = 0 ∧ d.a + (κ-1)*d.s = 0 ∧ d.a ≠ 0

/-- The preactivation carries the outer positive `v=w` facet. -/
def OuterV (κ : ℝ) (d : Coeff) : Prop :=
  d.r + d.s = 0 ∧ d.b + (κ-1)*d.s = 0 ∧ d.b ≠ 0

/-- The preactivation carries `u=w>v>0` in the all-active feature cell. -/
def InnerU (α β κ : ℝ) (d : Coeff) : Prop :=
  d.b - β*(d.r+d.s) = 0 ∧ d.a + β*d.r + (κ-α)*d.s = 0 ∧
    d.r + κ*d.s ≠ 0

/-- The preactivation carries `v=w>u>0` in the all-active feature cell. -/
def InnerV (α β κ : ℝ) (d : Coeff) : Prop :=
  d.a - α*(d.r+d.s) = 0 ∧ d.b + α*d.r + (κ-β)*d.s = 0 ∧
    d.r + κ*d.s ≠ 0

/-- The preactivation carries `u=v>w>1/κ` in the `r=0,s>0` feature cell. -/
def Middle (d : Coeff) : Prop := d.s = 0 ∧ d.a+d.b = 0 ∧ d.a ≠ 0

noncomputable def Coeff.swap (d : Coeff) : Coeff := ⟨d.b,d.a,d.r,d.s⟩
noncomputable def ResidualSystem.swap {ι : Type*} (d : ResidualSystem ι) :
    ResidualSystem ι := ⟨d.base.swap, fun i => (d.gate i).swap, d.out⟩

lemma form_swap (α β κ : ℝ) (d : Coeff) (u v w : ℝ) :
    form β α κ d.swap v u w = form α β κ d u v w := by
  unfold form Coeff.swap
  have hr : w - β*v - α*u = w - α*u - β*v := by ring
  have hs : κ*w - β*v - α*u = κ*w - α*u - β*v := by ring
  rw [hr,hs]
  ring

lemma target_swap (u v w : ℝ) : target v u w = target u v w := by
  simp only [target,max_assoc]
  rw [max_left_comm v u w]

lemma ResidualSystem.Represents.swap {ι : Type*} [Fintype ι]
    {d : ResidualSystem ι} {α β κ : ℝ} (h : d.Represents α β κ) :
    d.swap.Represents β α κ := by
  intro u v w
  have hh := h v u w
  simpa only [ResidualSystem.eval, ResidualSystem.swap, form_swap, target_swap] using hh

end MaxCaterpillar.Fiber.Count65.ForkExclusion
