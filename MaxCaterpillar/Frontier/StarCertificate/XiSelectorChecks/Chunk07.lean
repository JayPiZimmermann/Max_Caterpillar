import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! Generated bounded rational selector checks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem masked_compatible_56 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 56 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 56 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_56 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 56 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 56 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_57 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 57 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 57 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_57 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 57 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 57 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_58 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 58 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 58 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_58 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 58 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 58 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_59 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 59 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 59 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_59 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 59 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 59 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_60 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 60 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 60 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_60 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 60 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 60 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_61 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 61 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 61 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_61 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 61 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 61 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_62 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 62 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 62 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_62 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 62 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 62 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_63 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 63 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 63 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_63 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 63 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 63 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_chunk_7 (T : Fin 16) (p : Fin 8) :
    ∀ (t : Fin 10) (i : Fin 4),
    (maskedCoarse T ⟨56+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 56) (by decide)⟩ t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T ⟨56+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 56) (by decide)⟩ j).form subsetForms i := by
  fin_cases p
  · exact masked_compatible_56 T
  · exact masked_compatible_57 T
  · exact masked_compatible_58 T
  · exact masked_compatible_59 T
  · exact masked_compatible_60 T
  · exact masked_compatible_61 T
  · exact masked_compatible_62 T
  · exact masked_compatible_63 T

end MaxCaterpillar.Frontier.StarCertificate
