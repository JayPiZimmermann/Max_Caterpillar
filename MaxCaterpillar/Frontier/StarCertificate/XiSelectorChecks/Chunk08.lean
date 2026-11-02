import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! Generated bounded rational selector checks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem masked_compatible_64 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 64 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 64 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_64 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 64 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 64 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_65 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 65 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 65 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_65 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 65 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 65 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_66 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 66 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 66 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_66 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 66 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 66 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_67 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 67 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 67 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_67 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 67 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 67 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_68 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 68 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 68 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_68 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 68 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 68 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_69 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 69 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 69 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_69 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 69 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 69 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_70 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 70 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 70 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_70 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 70 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 70 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_71 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 71 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 71 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_71 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 71 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 71 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_chunk_8 (T : Fin 16) (p : Fin 8) :
    ∀ (t : Fin 10) (i : Fin 4),
    (maskedCoarse T ⟨64+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 64) (by decide)⟩ t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T ⟨64+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 64) (by decide)⟩ j).form subsetForms i := by
  fin_cases p
  · exact masked_compatible_64 T
  · exact masked_compatible_65 T
  · exact masked_compatible_66 T
  · exact masked_compatible_67 T
  · exact masked_compatible_68 T
  · exact masked_compatible_69 T
  · exact masked_compatible_70 T
  · exact masked_compatible_71 T

end MaxCaterpillar.Frontier.StarCertificate
