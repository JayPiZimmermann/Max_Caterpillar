import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! Generated bounded rational selector checks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem masked_compatible_8 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 8 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 8 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_8 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 8 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 8 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_9 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 9 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 9 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_9 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 9 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 9 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_10 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 10 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 10 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_10 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 10 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 10 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_11 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 11 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 11 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_11 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 11 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 11 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_12 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 12 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 12 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_12 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 12 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 12 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_13 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 13 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 13 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_13 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 13 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 13 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_14 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 14 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 14 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_14 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 14 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 14 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_15 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 15 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 15 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_15 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 15 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 15 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_chunk_1 (T : Fin 16) (p : Fin 8) :
    ∀ (t : Fin 10) (i : Fin 4),
    (maskedCoarse T ⟨8+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 8) (by decide)⟩ t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T ⟨8+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 8) (by decide)⟩ j).form subsetForms i := by
  fin_cases p
  · exact masked_compatible_8 T
  · exact masked_compatible_9 T
  · exact masked_compatible_10 T
  · exact masked_compatible_11 T
  · exact masked_compatible_12 T
  · exact masked_compatible_13 T
  · exact masked_compatible_14 T
  · exact masked_compatible_15 T

end MaxCaterpillar.Frontier.StarCertificate
