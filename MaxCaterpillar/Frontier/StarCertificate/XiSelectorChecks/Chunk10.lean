import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! Generated bounded rational selector checks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem masked_compatible_80 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 80 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 80 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_80 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 80 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 80 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_81 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 81 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 81 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_81 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 81 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 81 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_82 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 82 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 82 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_82 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 82 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 82 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_83 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 83 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 83 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_83 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 83 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 83 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_84 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 84 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 84 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_84 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 84 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 84 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_85 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 85 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 85 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_85 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 85 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 85 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_86 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 86 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 86 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_86 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 86 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 86 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_87 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 87 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 87 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_87 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 87 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 87 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_chunk_10 (T : Fin 16) (p : Fin 8) :
    ∀ (t : Fin 10) (i : Fin 4),
    (maskedCoarse T ⟨80+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 80) (by decide)⟩ t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T ⟨80+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 80) (by decide)⟩ j).form subsetForms i := by
  fin_cases p
  · exact masked_compatible_80 T
  · exact masked_compatible_81 T
  · exact masked_compatible_82 T
  · exact masked_compatible_83 T
  · exact masked_compatible_84 T
  · exact masked_compatible_85 T
  · exact masked_compatible_86 T
  · exact masked_compatible_87 T

end MaxCaterpillar.Frontier.StarCertificate
