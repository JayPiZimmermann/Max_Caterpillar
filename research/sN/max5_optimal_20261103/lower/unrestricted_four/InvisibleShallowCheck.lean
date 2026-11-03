import research.sN.max5_optimal_20261103.lower.unrestricted_four.InvisibleShallow

set_option autoImplicit false

namespace MaxCaterpillar.Frontier.Max5Invisible.Check

open BigOperators Filter Topology

/-- A literal finite shallow-model statement, with both all-real contact
values and genuine neighborhood agreement. No network lower bound is part
of this conclusion. -/
theorem five_neuron_barrier :
    ∃ (A : Fin 5 → Fin 5 → ℝ) (c : Fin 5 → ℝ) (K : (Fin 5 → ℝ) → ℝ),
      (∀ i, ∑ k, A i k = 0) ∧
      (∀ i k, A i k ≠ 0) ∧
      (∀ x, K x = ∑ i, c i * relu (∑ k, A i k * x k)) ∧
      (∀ x t, K (fun k => x k + t) = K x) ∧
      (∀ x, K (fun k => -x k) = K x) ∧
      (∀ (i j : Fin 5) (m s t : ℝ), 0 ≤ s → 0 ≤ t →
        K (fun k => m - (if k = i then s else 0) - (if k = j then t else 0)) = 0) ∧
      (∀ i : Fin 5, ∀ᶠ x in 𝓝 (fun k => -(if k = i then (1 : ℝ) else 0)), K x = 0) ∧
      K ![0, 0, 2, 1, 2] = -1 := by
  refine ⟨firstRow, coefficient, invisible, firstRow_sum, firstRow_full_support, ?_,
    translation_invariant, even, shifted_contact_zero, ?_, nonzero_witness⟩
  · exact shallow_representation
  · exact eventually_zero_at_vertex

/-- The actual chosen function is nonzero. -/
theorem literal_nonzero : invisible ≠ (fun _ => 0) := by
  intro h
  have he := congr_fun h (![0, 0, 2, 1, 2] : Point 5)
  rw [nonzero_witness] at he
  norm_num at he

#check @five_neuron_barrier
#print axioms five_neuron_barrier
#print axioms literal_nonzero

end MaxCaterpillar.Frontier.Max5Invisible.Check
