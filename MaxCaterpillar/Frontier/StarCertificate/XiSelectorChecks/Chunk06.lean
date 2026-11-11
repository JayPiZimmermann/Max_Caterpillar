import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! Generated bounded rational selector checks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem masked_compatible_48 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 48 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 48 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_48 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 48 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 48 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_49 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 49 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 49 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_49 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 49 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 49 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_50 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 50 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 50 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_50 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 50 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 50 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_51 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 51 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 51 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_51 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 51 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 51 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_52 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 52 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 52 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_52 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 52 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 52 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_53 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 53 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 53 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_53 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 53 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 53 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_54 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 54 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 54 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_54 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 54 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 54 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_55 : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T 55 t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T 55 j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

theorem chain_masked_projection_55 : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T 55 j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 55 j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

theorem masked_compatible_chunk_6 (T : Fin 16) (p : Fin 8) :
    ∀ (t : Fin 10) (i : Fin 4),
    (maskedCoarse T ⟨48+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 48) (by decide)⟩ t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T ⟨48+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 48) (by decide)⟩ j).form subsetForms i := by
  fin_cases p
  · exact masked_compatible_48 T
  · exact masked_compatible_49 T
  · exact masked_compatible_50 T
  · exact masked_compatible_51 T
  · exact masked_compatible_52 T
  · exact masked_compatible_53 T
  · exact masked_compatible_54 T
  · exact masked_compatible_55 T

end MaxCaterpillar.Frontier.StarCertificate
