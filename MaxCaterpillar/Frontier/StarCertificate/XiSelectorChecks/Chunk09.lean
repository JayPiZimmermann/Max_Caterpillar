import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! Generated bounded rational selector checks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem masked_compatible_72 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 72 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 72 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_72 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 72 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 72 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_73 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 73 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 73 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_73 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 73 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 73 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_74 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 74 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 74 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_74 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 74 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 74 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_75 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 75 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 75 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_75 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 75 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 75 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_76 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 76 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 76 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_76 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 76 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 76 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_77 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 77 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 77 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_77 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 77 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 77 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_78 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 78 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 78 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_78 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 78 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 78 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_79 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 79 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 79 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_79 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 79 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 79 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_chunk_9 (T : Fin 16) (p : Fin 8) :
    ∀ (t : Fin 10) (i : Fin 4),
    (maskedCoarse T ⟨72+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 72) (by decide)⟩ t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T ⟨72+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 72) (by decide)⟩ j).form subsetForms i := by
  fin_cases p
  · exact masked_compatible_72 T
  · exact masked_compatible_73 T
  · exact masked_compatible_74 T
  · exact masked_compatible_75 T
  · exact masked_compatible_76 T
  · exact masked_compatible_77 T
  · exact masked_compatible_78 T
  · exact masked_compatible_79 T

end MaxCaterpillar.Frontier.StarCertificate
