import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! Generated bounded rational selector checks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem masked_compatible_112 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 112 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 112 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_112 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 112 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 112 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_113 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 113 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 113 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_113 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 113 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 113 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_114 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 114 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 114 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_114 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 114 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 114 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_115 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 115 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 115 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_115 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 115 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 115 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_116 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 116 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 116 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_116 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 116 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 116 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_117 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 117 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 117 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_117 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 117 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 117 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_118 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 118 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 118 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_118 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 118 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 118 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_119 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 119 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 119 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_119 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 119 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 119 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_chunk_14 (T : Fin 16) (p : Fin 8) :
    ∀ (t : Fin 10) (i : Fin 4),
    (maskedCoarse T ⟨112+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 112) (by decide)⟩ t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T ⟨112+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 112) (by decide)⟩ j).form subsetForms i := by
  fin_cases p
  · exact masked_compatible_112 T
  · exact masked_compatible_113 T
  · exact masked_compatible_114 T
  · exact masked_compatible_115 T
  · exact masked_compatible_116 T
  · exact masked_compatible_117 T
  · exact masked_compatible_118 T
  · exact masked_compatible_119 T

end MaxCaterpillar.Frontier.StarCertificate
