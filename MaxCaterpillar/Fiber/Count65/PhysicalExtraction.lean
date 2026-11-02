import MaxCaterpillar.Fiber.Mixed65.PhysicalMinimalExtraction

/-!
# At most three original residual gates in every five-gate signed-carrier lift

The first theorem does not require a residual lower bound. If a diagonal tail
already leaves at most three gates, use it. Otherwise both tails leave at least
three gates and the existing exact three-gate extraction applies.

This is an extraction theorem, not a two-head classification or a component
count. The selected gates may still move along the other translation half-line.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.PhysicalExtraction
open BigOperators MaxCaterpillar.Frontier
open MaxCaterpillar.Fiber.Mixed65

/-- A signed-carrier lift of width five always has a residual using at most
three of the original gates. No residual floor or output-sign assumption. -/
theorem five_gate_residual_extraction_le_three {α : Type*} [Nonempty α]
    (d a b : Fin 5 → ℝ) (C : Fin 5 → α → ℝ) (H : α → ℝ)
    (h : ∀ x z, (∑ i, d i * relu (a i * relu z + b i * relu (-z) + C i x)) =
      z + H x) :
    ∃ S : Finset (Fin 5), S.card ≤ 3 ∧ ∃ l : Fin 5 → ℝ,
      ∀ x, H x = (∑ i, l i * C i x) + ∑ i in S, d i * relu (C i x) := by
  classical
  obtain ⟨_, _, hrem⟩ := finite_signed_carrier_extraction d a b C H h
  by_cases ha : 3 ≤ (Finset.univ.filter fun i => a i = 0).card
  · by_cases hb : 3 ≤ (Finset.univ.filter fun i => b i = 0).card
    · obtain ⟨S, hS, l, hl⟩ := five_gate_residual_extraction d a b C H h ha hb
      exact ⟨S, hS.le, l, hl⟩
    · refine ⟨Finset.univ.filter (fun i => b i = 0), ?_,
        (fun i => if 0 < b i then d i else 0), ?_⟩
      · exact le_of_lt (Nat.lt_of_not_ge hb)
      · intro x
        convert (hrem x).2 using 1
        congr 1
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs with hh <;> simp [hh]
  · refine ⟨Finset.univ.filter (fun i => a i = 0), ?_,
      (fun i => if 0 < a i then d i else 0), ?_⟩
    · exact le_of_lt (Nat.lt_of_not_ge ha)
    · intro x
      convert (hrem x).1 using 1
      congr 1
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with hh <;> simp [hh]

end MaxCaterpillar.Fiber.Count65.PhysicalExtraction
