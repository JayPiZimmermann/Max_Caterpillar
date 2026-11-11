import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! Generated bounded rational selector checks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem masked_compatible_104 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 104 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 104 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_104 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 104 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 104 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_105 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 105 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 105 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_105 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 105 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 105 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_106 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 106 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 106 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_106 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 106 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 106 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_107 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 107 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 107 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_107 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 107 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 107 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_108 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 108 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 108 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_108 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 108 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 108 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_109 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 109 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 109 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_109 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 109 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 109 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_110 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 110 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 110 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_110 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 110 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 110 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_111 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 111 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 111 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_111 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 111 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 111 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_chunk_13 (T : Fin 16) (p : Fin 8) :
    ∀ (t : Fin 10) (i : Fin 4),
    (maskedCoarse T ⟨104+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 104) (by decide)⟩ t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T ⟨104+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 104) (by decide)⟩ j).form subsetForms i := by
  fin_cases p
  · exact masked_compatible_104 T
  · exact masked_compatible_105 T
  · exact masked_compatible_106 T
  · exact masked_compatible_107 T
  · exact masked_compatible_108 T
  · exact masked_compatible_109 T
  · exact masked_compatible_110 T
  · exact masked_compatible_111 T

end MaxCaterpillar.Frontier.StarCertificate
