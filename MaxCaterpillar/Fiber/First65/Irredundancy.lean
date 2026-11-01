import MaxCaterpillar.Fiber.Minimal63.Nondegeneracy

/-! # No repeated positive first-row directions at minimal first width

An exact Max4 network with six first hidden neurons cannot have two distinct
first weight rows on the same positive ray. This holds with arbitrary biases:
first pass to the exact zero-bias recession network, merge the repeated
features, then delete the now unused neuron.

This is a necessary condition on the full exact fiber, not a classification
of its first layers or its connected components.
-/

set_option autoImplicit false

namespace MaxCaterpillar

open BigOperators
open Frontier

namespace Network

variable {N h₁ h₂ : ℕ}

/-- Move the outgoing contribution of first neuron `j` to first neuron `k`,
with multiplier `c`. The first hidden states and all biases stay unchanged. -/
noncomputable def mergeFirst (net : Network N h₁ h₂) (j k : Fin h₁) (c : ℝ) :
    Network N h₁ h₂ :=
  { net with W₂ := fun a i => net.W₂ a i + (if i = k then c * net.W₂ a j else 0) -
      (if i = j then net.W₂ a j else 0) }

/-- The merged neuron's outgoing column vanishes. -/
theorem mergeFirst_column_zero (net : Network N h₁ h₂) (j k : Fin h₁) (c : ℝ)
    (hjk : j ≠ k) (a : Fin h₂) : (net.mergeFirst j k c).W₂ a j = 0 := by
  simp [mergeFirst, hjk]

/-- Merging preserves every second preactivation when the first activations
are related by the multiplier `c`. This version does not assume a relation
between parameters, so it also applies to activation identities. -/
theorem mergeFirst_eval_of_activation_eq (net : Network N h₁ h₂)
    (j k : Fin h₁) (c : ℝ)
    (hjk : ∀ x : Point N,
      relu ((∑ i, net.W₁ j i * x i) + net.b₁ j) =
        c * relu ((∑ i, net.W₁ k i * x i) + net.b₁ k))
    (x : Point N) : (net.mergeFirst j k c).eval x = net.eval x := by
  have hsum (a : Fin h₂) :
      (∑ i, (net.W₂ a i + (if i = k then c * net.W₂ a j else 0) -
          (if i = j then net.W₂ a j else 0)) *
        relu ((∑ r, net.W₁ i r * x r) + net.b₁ i)) =
      ∑ i, net.W₂ a i * relu ((∑ r, net.W₁ i r * x r) + net.b₁ i) := by
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hjk x]
    ring
  unfold eval mergeFirst
  dsimp only
  simp only [hsum]

/-- Proportional incoming affine forms with a positive ratio can be merged. -/
theorem mergeFirst_eval (net : Network N h₁ h₂) (j k : Fin h₁) {c : ℝ}
    (hc : 0 < c) (hW : net.W₁ j = c • net.W₁ k)
    (hb : net.b₁ j = c * net.b₁ k) (x : Point N) :
    (net.mergeFirst j k c).eval x = net.eval x := by
  apply mergeFirst_eval_of_activation_eq
  intro y
  have he : (∑ i, net.W₁ j i * y i) + net.b₁ j =
      c * ((∑ i, net.W₁ k i * y i) + net.b₁ k) := by
    rw [hW, hb]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, mul_add]
  rw [he, relu_mul_pos hc]

/-- At first width six, two distinct first weight rows of an exact Max4
network cannot be positively proportional, even when biases are allowed. -/
theorem first_rows_not_pos_proportional_of_max4_six
    (net : Network 4 6 h₂) (h : ∀ x, net.eval x = Maximum 4 x)
    {j k : Fin 6} (hjk : j ≠ k) {c : ℝ} (hc : 0 < c) :
    net.W₁ j ≠ c • net.W₁ k := by
  intro hW
  let merged := net.zeroBias.mergeFirst j k c
  have hz : ∀ x, net.zeroBias.eval x = Maximum 4 x := by
    intro x
    rw [zeroBias_eval]
    exact net.toZ_eval_of_max h x
  have hm : ∀ x, merged.eval x = Maximum 4 x := by
    intro x
    change (net.zeroBias.mergeFirst j k c).eval x = Maximum 4 x
    rw [mergeFirst_eval net.zeroBias j k hc hW (by simp [zeroBias]), hz]
  obtain ⟨a, ha⟩ := merged.first_column_ne_zero_of_max4_six hm j
  exact ha (mergeFirst_column_zero net.zeroBias j k c hjk a)

/-- Change the second affine map along a linear relation among first hidden
activations. A relation can involve more than two neurons and arbitrary signs. -/
noncomputable def subtractFirstRelation (net : Network N h₁ h₂)
    (g : Fin h₁ → ℝ) (t : Fin h₂ → ℝ) : Network N h₁ h₂ :=
  { net with W₂ := fun k j => net.W₂ k j - t k * g j }

/-- An identically zero linear relation among first activations leaves every
second preactivation unchanged under `subtractFirstRelation`. -/
theorem subtractFirstRelation_eval (net : Network N h₁ h₂)
    (g : Fin h₁ → ℝ) (t : Fin h₂ → ℝ)
    (hg : ∀ x : Point N,
      ∑ j, g j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j) = 0)
    (x : Point N) : (net.subtractFirstRelation g t).eval x = net.eval x := by
  have hsum (k : Fin h₂) :
      (∑ j, (net.W₂ k j - t k * g j) *
        relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) =
      ∑ j, net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j) := by
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rw [hg x, mul_zero, sub_zero]
  unfold eval subtractFirstRelation
  dsimp only
  simp only [hsum]

/-- The six first activation functions of every exact width-six Max4 network
are linearly independent, as functions on all real inputs. -/
theorem first_activations_linearIndependent_of_max4_six
    (net : Network 4 6 h₂) (h : ∀ x, net.eval x = Maximum 4 x) :
    LinearIndependent ℝ (fun j : Fin 6 => fun x : Point 4 =>
      relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg j
  by_contra hj
  have hpoint : ∀ x : Point 4,
      ∑ i, g i * relu ((∑ r, net.W₁ i r * x r) + net.b₁ i) = 0 := by
    intro x
    have hx := congr_fun hg x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hx
  let recoded := net.subtractFirstRelation g (fun k => net.W₂ k j / g j)
  have hr : ∀ x, recoded.eval x = Maximum 4 x := by
    intro x
    exact (net.subtractFirstRelation_eval g (fun k => net.W₂ k j / g j)
      hpoint x).trans (h x)
  obtain ⟨k, hk⟩ := recoded.first_column_ne_zero_of_max4_six hr j
  apply hk
  change net.W₂ k j - (net.W₂ k j / g j) * g j = 0
  rw [div_mul_cancel _ hj, sub_self]

/-- The same independence holds for the homogeneous first activations obtained
by dropping biases from an arbitrary exact width-six network. -/
theorem first_recession_activations_linearIndependent_of_max4_six
    (net : Network 4 6 h₂) (h : ∀ x, net.eval x = Maximum 4 x) :
    LinearIndependent ℝ (fun j : Fin 6 => fun x : Point 4 =>
      relu (∑ i, net.W₁ j i * x i)) := by
  have hz : ∀ x, net.zeroBias.eval x = Maximum 4 x := by
    intro x
    rw [zeroBias_eval]
    exact net.toZ_eval_of_max h x
  simpa only [zeroBias, Pi.zero_apply, add_zero] using
    net.zeroBias.first_activations_linearIndependent_of_max4_six hz

end Network

end MaxCaterpillar
