import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! Generated bounded rational selector checks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem masked_compatible_0 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 0 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 0 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_0 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 0 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 0 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_1 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 1 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 1 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_1 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 1 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 1 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_2 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 2 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 2 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_2 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 2 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 2 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_3 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 3 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 3 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_3 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 3 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 3 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_4 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 4 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 4 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_4 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 4 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 4 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_5 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 5 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 5 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_5 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 5 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 5 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_6 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 6 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 6 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_6 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 6 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 6 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_7 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 7 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 7 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_7 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 7 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 7 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_chunk_0 (T : Fin 16) (p : Fin 8) :
    ∀ (t : Fin 10) (i : Fin 4),
    (maskedCoarse T ⟨0+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 0) (by decide)⟩ t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T ⟨0+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 0) (by decide)⟩ j).form subsetForms i := by
  fin_cases p
  · exact masked_compatible_0 T
  · exact masked_compatible_1 T
  · exact masked_compatible_2 T
  · exact masked_compatible_3 T
  · exact masked_compatible_4 T
  · exact masked_compatible_5 T
  · exact masked_compatible_6 T
  · exact masked_compatible_7 T

end MaxCaterpillar.Frontier.StarCertificate
