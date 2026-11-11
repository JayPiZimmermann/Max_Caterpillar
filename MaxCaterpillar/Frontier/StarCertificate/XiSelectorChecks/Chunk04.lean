import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! Generated bounded rational selector checks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem masked_compatible_32 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 32 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 32 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_32 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 32 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 32 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_33 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 33 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 33 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_33 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 33 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 33 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_34 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 34 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 34 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_34 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 34 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 34 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_35 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 35 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 35 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_35 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 35 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 35 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_36 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 36 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 36 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_36 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 36 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 36 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_37 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 37 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 37 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_37 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 37 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 37 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_38 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 38 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 38 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_38 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 38 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 38 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_39 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 39 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 39 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_39 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 39 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 39 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_chunk_4 (T : Fin 16) (p : Fin 8) :
    ∀ (t : Fin 10) (i : Fin 4),
    (maskedCoarse T ⟨32+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 32) (by decide)⟩ t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T ⟨32+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 32) (by decide)⟩ j).form subsetForms i := by
  fin_cases p
  · exact masked_compatible_32 T
  · exact masked_compatible_33 T
  · exact masked_compatible_34 T
  · exact masked_compatible_35 T
  · exact masked_compatible_36 T
  · exact masked_compatible_37 T
  · exact masked_compatible_38 T
  · exact masked_compatible_39 T

end MaxCaterpillar.Frontier.StarCertificate
