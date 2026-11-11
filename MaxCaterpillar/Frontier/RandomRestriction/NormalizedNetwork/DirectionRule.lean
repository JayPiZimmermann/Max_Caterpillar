import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Directional

/-! # Exact localization of the complete homogeneous skip model

The directional expression is first defined without imposing a target. Its
exact small-step identity is proved from the scalar ReLU rule twice.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
open BigOperators Filter Topology
variable {N m h₁ h₂ : ℕ}

lemma weighted_add_step {ι : Type*} [Fintype ι] (w a b : ι → ℝ) (ε : ℝ) :
    (∑ j, w j * (a j + ε*b j)) = (∑ j, w j*a j) + ε*(∑ j, w j*b j) := by
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def firstDirection (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (j : Fin h₁) (x : Point m) : ℝ :=
  pick (lin (net.A j) q) (lin (restrict e (net.A j)) x)
    (relu (lin (restrict e (net.A j)) x))

noncomputable def innerDirection (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (k : Fin h₂) (x : Point m) : ℝ :=
  lin (restrict e (net.U k)) x + ∑ j, net.W k j * net.firstDirection q e j x

noncomputable def directionalEval (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (x : Point m) : ℝ :=
  lin (restrict e net.L) x + (∑ j, net.B j * net.firstDirection q e j x) +
    ∑ k, net.d k * pick (net.inner k q) (net.innerDirection q e k x)
      (relu (net.innerDirection q e k x))

lemma eventually_first_direction (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (x : Point m) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j,
      relu (lin (net.A j) (q + ε • lift e x)) =
        relu (lin (net.A j) q) + ε * net.firstDirection q e j x := by
  refine Filter.eventually_all.mpr (fun j => ?_)
  have h := eventually_relu_direction (lin (net.A j) q) (lin (restrict e (net.A j)) x)
  simpa only [lin_add_right,lin_smul_right,lin_lift,firstDirection] using h

lemma inner_direction_at (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (x : Point m) (ε : ℝ)
    (hfirst : ∀ j, relu (lin (net.A j) (q + ε • lift e x)) =
      relu (lin (net.A j) q) + ε * net.firstDirection q e j x) (k : Fin h₂) :
    net.inner k (q + ε • lift e x) = net.inner k q + ε * net.innerDirection q e k x := by
  simp only [inner,hfirst]
  simp only [innerDirection,lin_add_right,lin_smul_right,lin_lift]
  rw [weighted_add_step]
  ring

/-- This is an exact germ equality for every real direction. -/
theorem eventually_eval_direction (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (x : Point m) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      net.eval (q + ε • lift e x) = net.eval q + ε * net.directionalEval q e x := by
  have hsecond : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ k,
      relu (net.inner k q + ε * net.innerDirection q e k x) =
        relu (net.inner k q) + ε * pick (net.inner k q) (net.innerDirection q e k x)
          (relu (net.innerDirection q e k x)) :=
    Filter.eventually_all.mpr (fun k => eventually_relu_direction _ _)
  filter_upwards [net.eventually_first_direction q e x,hsecond] with ε hfirst hsecond
  have hinner := net.inner_direction_at q e x ε hfirst
  simp only [eval,hfirst,hinner,hsecond]
  simp only [directionalEval,lin_add_right,lin_smul_right,lin_lift]
  rw [weighted_add_step,weighted_add_step]
  ring

/-- A concrete positive exact step exists in every direction. -/
theorem exists_eval_direction (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (x : Point m) :
    ∃ ε : ℝ, 0 < ε ∧
      net.eval (q + ε • lift e x) = net.eval q + ε * net.directionalEval q e x := by
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  exact ((hpos.and (net.eventually_eval_direction q e x)).exists)

#check @eventually_eval_direction
#print axioms eventually_eval_direction
end MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
