import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! Generated bounded rational selector checks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem masked_compatible_24 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 24 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 24 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_24 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 24 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 24 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_25 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 25 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 25 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_25 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 25 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 25 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_26 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 26 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 26 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_26 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 26 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 26 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_27 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 27 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 27 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_27 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 27 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 27 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_28 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 28 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 28 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_28 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 28 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 28 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_29 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 29 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 29 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_29 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 29 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 29 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_30 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 30 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 30 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_30 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 30 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 30 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_31 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 31 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 31 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_31 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 31 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 31 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_chunk_3 (T : Fin 16) (p : Fin 8) :
    ∀ (t : Fin 10) (i : Fin 4),
    (maskedCoarse T ⟨24+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 24) (by decide)⟩ t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T ⟨24+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 24) (by decide)⟩ j).form subsetForms i := by
  fin_cases p
  · exact masked_compatible_24 T
  · exact masked_compatible_25 T
  · exact masked_compatible_26 T
  · exact masked_compatible_27 T
  · exact masked_compatible_28 T
  · exact masked_compatible_29 T
  · exact masked_compatible_30 T
  · exact masked_compatible_31 T

end MaxCaterpillar.Frontier.StarCertificate
