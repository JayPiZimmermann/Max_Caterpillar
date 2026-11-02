import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! Generated bounded rational selector checks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem masked_compatible_40 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 40 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 40 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_40 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 40 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 40 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_41 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 41 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 41 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_41 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 41 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 41 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_42 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 42 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 42 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_42 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 42 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 42 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_43 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 43 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 43 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_43 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 43 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 43 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_44 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 44 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 44 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_44 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 44 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 44 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_45 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 45 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 45 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_45 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 45 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 45 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_46 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 46 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 46 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_46 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 46 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 46 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_47 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 47 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 47 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_47 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 47 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 47 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_chunk_5 (T : Fin 16) (p : Fin 8) :
    ∀ (t : Fin 10) (i : Fin 4),
    (maskedCoarse T ⟨40+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 40) (by decide)⟩ t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T ⟨40+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 40) (by decide)⟩ j).form subsetForms i := by
  fin_cases p
  · exact masked_compatible_40 T
  · exact masked_compatible_41 T
  · exact masked_compatible_42 T
  · exact masked_compatible_43 T
  · exact masked_compatible_44 T
  · exact masked_compatible_45 T
  · exact masked_compatible_46 T
  · exact masked_compatible_47 T

end MaxCaterpillar.Frontier.StarCertificate
