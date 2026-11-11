import Mathlib

/-! # Finite outer-event and inner-fiber averaging

These generic lemmas are used by the actual per-neuron assembly. Their
counting inputs are proved in the graph and clean-coin modules before the
headline theorem instantiates them.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
open BigOperators

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- A literal tail fiber of an event on the actual three-factor space. -/
noncomputable def tailFiber (E : Finset (A × C × B)) (a : A) (b : B) : Finset C := by
  classical
  exact Finset.univ.filter fun c => (a, c, b) ∈ E

@[simp] theorem mem_tailFiber (E : Finset (A × C × B)) (a : A) (b : B) (c : C) :
    c ∈ tailFiber E a b ↔ (a, c, b) ∈ E := by
  classical
  simp only [tailFiber, Finset.mem_filter, Finset.mem_univ, true_and]

theorem card_eq_sum_tailFiber (E : Finset (A × C × B)) :
    (E.card : ℝ) = ∑ a : A, ∑ b : B, ((tailFiber E a b).card : ℝ) := by
  classical
  have hc : (E.card : ℝ) = ∑ ω : A × C × B, if ω ∈ E then (1 : ℝ) else 0 := by
    simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
      (Finset.natCast_card_filter (fun ω => ω ∈ E) Finset.univ)
  rw [hc]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [tailFiber, Finset.natCast_card_filter]

/-- A common density-weighted bound on every selected outer fiber cancels
with the proved outer-event density. The density-zero case is included. -/
theorem outer_density_fiber_count_le (selected : Finset A) (E : A → B → Finset C)
    (density bound : ℝ) (hdensity : 0 ≤ density) (hbound : 0 ≤ bound)
    (hselected : (selected.card : ℝ) ≤ density * Fintype.card A)
    (hoff : ∀ a ∉ selected, ∀ b, E a b = ∅)
    (hfiber : ∀ a ∈ selected, ∀ b,
      density * ((E a b).card : ℝ) ≤ bound * Fintype.card C) :
    (∑ a : A, ∑ b : B, ((E a b).card : ℝ)) ≤
      bound * Fintype.card A * Fintype.card B * Fintype.card C := by
  classical
  by_cases hz : density = 0
  · have hselzero : selected.card = 0 := by
      have hh : (selected.card : ℝ) ≤ 0 := by simpa only [hz, zero_mul] using hselected
      have he : (selected.card : ℝ) = 0 := le_antisymm hh (Nat.cast_nonneg _)
      exact_mod_cast he
    have hs : selected = ∅ := Finset.card_eq_zero.mp hselzero
    have hE : ∀ a b, E a b = ∅ := fun a b => hoff a (by rw [hs]; simp) b
    simp only [hE, Finset.card_empty, Nat.cast_zero, Finset.sum_const_zero]
    positivity
  · have hdpos : 0 < density := lt_of_le_of_ne hdensity (Ne.symm hz)
    have hweighted : density * (∑ a : A, ∑ b : B, ((E a b).card : ℝ)) ≤
        (selected.card : ℝ) * Fintype.card B * (bound * Fintype.card C) := by
      calc
        _ = ∑ a : A, ∑ b : B, density * ((E a b).card : ℝ) := by
          simp_rw [Finset.mul_sum]
        _ = ∑ a in selected, ∑ b : B, density * ((E a b).card : ℝ) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ selected)
          intro a _ ha
          simp only [hoff a ha, Finset.card_empty, Nat.cast_zero, mul_zero,
            Finset.sum_const_zero]
        _ ≤ ∑ _a in selected, ∑ _b : B, bound * Fintype.card C := by
          apply Finset.sum_le_sum
          intro a ha
          exact Finset.sum_le_sum fun b _ => hfiber a ha b
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring
    have hmul := mul_le_mul_of_nonneg_right hselected
      (show 0 ≤ (Fintype.card B : ℝ) * (bound * Fintype.card C) by positivity)
    have hh : density * (∑ a : A, ∑ b : B, ((E a b).card : ℝ)) ≤
        density * (bound * Fintype.card A * Fintype.card B * Fintype.card C) := by
      nlinarith only [hweighted, hmul]
    exact (mul_le_mul_left hdpos).mp hh

/-- Direct event-cardinality form on a finite three-factor configuration
space, retaining the density-zero case and all empty outer events. -/
theorem outer_density_event_card_le (selected : Finset A) (E : Finset (A × C × B))
    (density bound : ℝ) (hdensity : 0 ≤ density) (hbound : 0 ≤ bound)
    (hselected : (selected.card : ℝ) ≤ density * Fintype.card A)
    (hselected_event : ∀ a b c, (a, c, b) ∈ E → a ∈ selected)
    (hfiber : ∀ a ∈ selected, ∀ b,
      density * ((tailFiber E a b).card : ℝ) ≤ bound * Fintype.card C) :
    (E.card : ℝ) ≤ bound * Fintype.card (A × C × B) := by
  classical
  have hoff : ∀ a ∉ selected, ∀ b, tailFiber E a b = ∅ := by
    intro a ha b
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro c hc
    exact ha (hselected_event a b c ((mem_tailFiber E a b c).mp hc))
  rw [card_eq_sum_tailFiber]
  have hh := outer_density_fiber_count_le selected (tailFiber E) density bound
    hdensity hbound hselected hoff hfiber
  simpa only [Fintype.card_prod, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hh

end MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
