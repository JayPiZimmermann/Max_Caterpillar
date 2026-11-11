import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! Generated bounded rational selector checks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem masked_compatible_96 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 96 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 96 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_96 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 96 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 96 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_97 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 97 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 97 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_97 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 97 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 97 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_98 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 98 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 98 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_98 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 98 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 98 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_99 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 99 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 99 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_99 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 99 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 99 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_100 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 100 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 100 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_100 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 100 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 100 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_101 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 101 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 101 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_101 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 101 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 101 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_102 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 102 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 102 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_102 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 102 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 102 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_103 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 103 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 103 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_103 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 103 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 103 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_chunk_12 (T : Fin 16) (p : Fin 8) :
    ∀ (t : Fin 10) (i : Fin 4),
    (maskedCoarse T ⟨96+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 96) (by decide)⟩ t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T ⟨96+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 96) (by decide)⟩ j).form subsetForms i := by
  fin_cases p
  · exact masked_compatible_96 T
  · exact masked_compatible_97 T
  · exact masked_compatible_98 T
  · exact masked_compatible_99 T
  · exact masked_compatible_100 T
  · exact masked_compatible_101 T
  · exact masked_compatible_102 T
  · exact masked_compatible_103 T

end MaxCaterpillar.Frontier.StarCertificate
