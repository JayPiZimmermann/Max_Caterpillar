import MaxNN.Constructions.Paramid.Caterpillar.Geometry.Paramid
import MaxNN.Constructions.Paramid.Caterpillar.Block.Patterns

/-! # The complete remainder outside unique spine crossings

The apex level occurs in the base and every other level occurs at least
twice. Under these hypotheses the only potentially nonzero top facet terms
are the constant-prefix / constant-suffix words with a cut at their boundary.
-/

namespace MaxNN.Caterpillar

open ParamidGeom

variable {m r : ℕ}

theorem germDiff_pendant_mem_LSpan_one_of_distinct_levels
    (apex : Fin m → ℝ) (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (j : Fin r) (hj : j.succ ∉ S)
    (u : Fin m → ℝ) (c : ℝ) (hc : c ≠ dot apex u)
    (he : dot (A j.succ) u = dot apex u)
    (hA : ∀ i, i ≠ j.succ → dot (A i) u = c) :
    germDiff u (caterpillarUnit apex A S) ∈ LSpan m 1 := by
  have hb := baseMax_single_pendant (values A u) S j hj c hA
  change baseMax (values A u) S = max c (dot (A j.succ) u) + c - dot (A j.succ) u at hb
  rw [he] at hb
  have hAn : ∀ i, i ≠ j.succ → dot (A i) (-u) = -c := by
    intro i hi
    rw [UnitGermAux.dot_neg_right, hA i hi]
  have hbn := baseMax_single_pendant (values A (-u)) S j hj (-c) hAn
  change baseMax (values A (-u)) S = max (-c) (dot (A j.succ) (-u)) + (-c) -
    dot (A j.succ) (-u) at hbn
  rw [UnitGermAux.dot_neg_right, he] at hbn
  have hp : dot apex u ≠ baseMax (values A u) S := by
    rw [hb]
    rcases lt_or_gt_of_ne hc with hlt | hgt
    · rw [max_eq_right (le_of_lt hlt)]
      linarith
    · rw [max_eq_left (le_of_lt hgt)]
      linarith
  have hn : dot apex (-u) ≠ baseMax (values A (-u)) S := by
    rw [UnitGermAux.dot_neg_right, hbn]
    rcases lt_or_gt_of_ne hc with hlt | hgt
    · rw [max_eq_left (neg_le_neg (le_of_lt hlt))]
      linarith
    · rw [max_eq_right (neg_le_neg (le_of_lt hgt))]
      linarith
  exact Submodule.sub_mem _ (germ_caterpillarUnit_mem_LSpan_one_of_ne apex A S u hp)
    (germ_caterpillarUnit_mem_LSpan_one_of_ne apex A S (-u) hn)

theorem germDiff_mem_LSpan_or_split (hr : 2 ≤ r)
    (apex : Fin m → ℝ) (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (hinj : Function.Injective (edgeVecs A S))
    (u : Fin m → ℝ)
    (ha : ∃ i, dot (A i) u = dot apex u)
    (ho : ∃ i, dot (A i) u ≠ dot apex u)
    (hrep : ∀ i, dot (A i) u ≠ dot apex u → ∃ k, k ≠ i ∧ dot (A k) u = dot (A i) u) :
    germDiff u (caterpillarUnit apex A S) ∈ LSpan m (r - 1) ∨
      ∃ j : Fin r, j.succ ∈ S ∧ SplitValues (values A u) j ∧
        (dot apex u = dot (A 0) u ∨ dot apex u = dot (A j.succ) u) := by
  classical
  have hex : ∃ j : Fin r, values A u j.succ ≠ values A u (parent S j.succ) := by
    by_cases hroot : dot (A 0) u = dot apex u
    · obtain ⟨i, hi⟩ := ho
      exact exists_parent_value_ne S (values A u) (fun he => hi (he.trans hroot))
    · obtain ⟨i, hi⟩ := ha
      exact exists_parent_value_ne S (values A u) (fun he => hroot (he.symm.trans hi))
  obtain ⟨j, hj⟩ := hex
  by_cases htwo : ∃ k : Fin r, k ≠ j ∧ values A u k.succ ≠ values A u (parent S k.succ)
  · obtain ⟨k, hk, hkc⟩ := htwo
    exact Or.inl (germDiff_caterpillarUnit_mem_LSpan_of_two apex A S hinj u j k
      (Ne.symm hk) (Ne.symm hj) (Ne.symm hkc))
  · have hother : ∀ k : Fin r, k ≠ j → values A u k.succ = values A u (parent S k.succ) := by
      intro k hk
      by_contra he
      exact htwo ⟨k, hk, he⟩
    by_cases hcut : j.succ ∈ S
    · have hw := unique_edge_cut_values S (values A u) j hcut hother
      have hne : values A u 0 ≠ values A u j.succ := by
        intro he
        apply hj
        rw [hw (parent S j.succ), if_pos (parent_lt (Fin.succ_pos j)), he]
      refine Or.inr ⟨j, hcut, ⟨hne, hw⟩, ?_⟩
      obtain ⟨i, hi⟩ := ha
      have hv := hw i
      by_cases hlt : i < j.succ
      · rw [if_pos hlt] at hv
        exact Or.inl (hi.symm.trans hv)
      · rw [if_neg hlt] at hv
        exact Or.inr (hi.symm.trans hv)
    · have hw := unique_edge_not_cut_values S (values A u) j hcut hother
      have hroot : dot (A 0) u ≠ dot apex u := by
        intro he
        have hjother : dot (A j.succ) u ≠ dot apex u := by
          intro hje
          apply hj
          rw [hw _ (parent_ne_pendant S j hcut _)]
          exact hje.trans he.symm
        obtain ⟨k, hk, hkv⟩ := hrep j.succ hjother
        exact hjother ((hkv.symm.trans (hw k hk)).trans he)
      have hAj : dot (A j.succ) u = dot apex u := by
        obtain ⟨i, hi⟩ := ha
        by_cases he : i = j.succ
        · exact he ▸ hi
        · exact False.elim (hroot ((hw i he).symm.trans hi))
      exact Or.inl (DoublingAux.LSpan_mono (Nat.le_sub_of_add_le (show 1 + 1 ≤ r from hr))
        (germDiff_pendant_mem_LSpan_one_of_distinct_levels apex A S j hcut u
          (dot (A 0) u) hroot hAj hw))

end MaxNN.Caterpillar
