import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! Generated bounded rational selector checks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem masked_compatible_16 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 16 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 16 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_16 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 16 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 16 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_17 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 17 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 17 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_17 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 17 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 17 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_18 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 18 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 18 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_18 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 18 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 18 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_19 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 19 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 19 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_19 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 19 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 19 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_20 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 20 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 20 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_20 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 20 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 20 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_21 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 21 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 21 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_21 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 21 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 21 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_22 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 22 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 22 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_22 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 22 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 22 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_23 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 23 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 23 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_23 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 23 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 23 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_chunk_2 (T : Fin 16) (p : Fin 8) :
    ∀ (t : Fin 10) (i : Fin 4),
    (maskedCoarse T ⟨16+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 16) (by decide)⟩ t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T ⟨16+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 16) (by decide)⟩ j).form subsetForms i := by
  fin_cases p
  · exact masked_compatible_16 T
  · exact masked_compatible_17 T
  · exact masked_compatible_18 T
  · exact masked_compatible_19 T
  · exact masked_compatible_20 T
  · exact masked_compatible_21 T
  · exact masked_compatible_22 T
  · exact masked_compatible_23 T

end MaxCaterpillar.Frontier.StarCertificate
