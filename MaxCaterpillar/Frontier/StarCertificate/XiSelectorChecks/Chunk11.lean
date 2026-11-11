import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! Generated bounded rational selector checks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem masked_compatible_88 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 88 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 88 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_88 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 88 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 88 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_89 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 89 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 89 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_89 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 89 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 89 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_90 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 90 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 90 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_90 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 90 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 90 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_91 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 91 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 91 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_91 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 91 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 91 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_92 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 92 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 92 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_92 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 92 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 92 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_93 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 93 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 93 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_93 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 93 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 93 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_94 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 94 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 94 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_94 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 94 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 94 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_95 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 95 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 95 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_95 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 95 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 95 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_chunk_11 (T : Fin 16) (p : Fin 8) :
    ∀ (t : Fin 10) (i : Fin 4),
    (maskedCoarse T ⟨88+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 88) (by decide)⟩ t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T ⟨88+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 88) (by decide)⟩ j).form subsetForms i := by
  fin_cases p
  · exact masked_compatible_88 T
  · exact masked_compatible_89 T
  · exact masked_compatible_90 T
  · exact masked_compatible_91 T
  · exact masked_compatible_92 T
  · exact masked_compatible_93 T
  · exact masked_compatible_94 T
  · exact masked_compatible_95 T

end MaxCaterpillar.Frontier.StarCertificate
