import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Model

/-! # Exact one-sided first-order rules and coordinate embeddings

Every equality is exact for all sufficiently small positive steps in a fixed
direction, rather than an equality of numerical approximations.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
open BigOperators Filter Topology
variable {N m h₁ h₂ : ℕ}

lemma eventually_relu_direction (a b : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      relu (a + ε*b) = relu a + ε*pick a b (relu b) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · filter_upwards [eventually_small b (neg_pos.mpr ha)] with ε hε
    rw [relu_of_nonpos ha.le,relu_of_nonpos (by linarith [(abs_lt.mp hε).2])]
    simp [pick,ha,not_lt.mpr ha.le]
  · rw [ha]
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    filter_upwards [hpos] with ε hε
    simp only [pick,lt_self_iff_false,if_false,zero_add]
    rw [relu_mul_pos hε]
    simp [relu]
  · filter_upwards [eventually_small b ha] with ε hε
    rw [relu_of_nonneg ha.le,relu_of_nonneg (by linarith [(abs_lt.mp hε).1])]
    simp [pick,ha]

/-- Restrict coefficients to a chosen ordered coordinate subset. -/
def restrict (e : Fin m ↪ Fin N) (a : Point N) : Point m := fun i => a (e i)

/-- Extend a direction by zero outside the chosen coordinates. -/
def lift (e : Fin m ↪ Fin N) (x : Point m) : Point N :=
  ∑ i, x i • unitVec (e i)

lemma lin_lift (e : Fin m ↪ Fin N) (a : Point N) (x : Point m) :
    lin a (lift e x) = lin (restrict e a) x := by
  rw [lift,lin_sum_right]
  simp only [lin_smul_right,lin_unitVec]
  change (∑ i, x i * a (e i)) = ∑ i, a (e i) * x i
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma lift_selected (e : Fin m ↪ Fin N) (x : Point m) (i : Fin m) :
    lift e x (e i) = x i := by
  classical
  simp only [lift,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,unitVec]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : e i ≠ e j := by intro h; exact hji (e.injective h).symm
    simp [hne,Ne.symm hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

lemma lift_outside (e : Fin m ↪ Fin N) (x : Point m) (i : Fin N)
    (hi : i ∉ Finset.univ.image e) : lift e x i = 0 := by
  classical
  simp only [lift,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,unitVec]
  apply Finset.sum_eq_zero
  intro j _
  have hne : i ≠ e j := by
    intro h
    exact hi (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,h.symm⟩)
  simp [hne]

#check @eventually_relu_direction
#print axioms eventually_relu_direction
end MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
