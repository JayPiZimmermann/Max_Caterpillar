import MaxNN.Constructions.Paramid.Caterpillar.Words.Crossing.Base
import MaxNN.Constructions.Paramid.Caterpillar.Geometry.Paramid

/-! # DFS branch: possible facet patterns of a caterpillar unit

Target: for all word lengths, directions outside the block and braid value
patterns have lower-dimensional two-sided germs. The branch uses an exhaustive
split into zero, one and at least two crossing parent edges. A failure of the
single-edge scalar evaluation would refute this route; build failures alone do
not. This module does not assert cancellation of the exceptional patterns or
the global caterpillar identity.
-/

namespace MaxNN.Caterpillar

open ParamidGeom

variable {m r : ℕ}

/-- At most two normal values occur, one of them the apex value. On simplex
vertices this is the block pattern, including coordinate and constant cases. -/
def BlockValues (apex : Fin m → ℝ) (A : Fin (r + 1) → Fin m → ℝ)
    (u : Fin m → ℝ) : Prop :=
  ∃ c : ℝ, ∀ i, dot (A i) u = dot apex u ∨ dot (A i) u = c

/-- All base vertices except one nonroot vertex have the common normal value
`c`; the apex and exceptional vertex are equally far on opposite sides of it. -/
def BraidValues (apex : Fin m → ℝ) (A : Fin (r + 1) → Fin m → ℝ)
    (u : Fin m → ℝ) : Prop :=
  ∃ j : Fin r, ∃ c : ℝ,
    (∀ i : Fin (r + 1), i ≠ j.succ → dot (A i) u = c) ∧
    dot apex u + dot (A j.succ) u = 2 * c

theorem BlockValues.neg {apex : Fin m → ℝ} {A : Fin (r + 1) → Fin m → ℝ}
    {u : Fin m → ℝ} (h : BlockValues apex A u) : BlockValues apex A (-u) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨-c, fun i => ?_⟩
  simp only [UnitGermAux.dot_neg_right]
  rcases hc i with hi | hi
  · exact Or.inl (congrArg Neg.neg hi)
  · exact Or.inr (congrArg Neg.neg hi)

theorem BraidValues.neg {apex : Fin m → ℝ} {A : Fin (r + 1) → Fin m → ℝ}
    {u : Fin m → ℝ} (h : BraidValues apex A u) : BraidValues apex A (-u) := by
  obtain ⟨j, c, hc, he⟩ := h
  refine ⟨j, -c, ?_, ?_⟩
  · intro i hi
    rw [UnitGermAux.dot_neg_right, hc i hi]
  · simp only [UnitGermAux.dot_neg_right]
    linarith

theorem blockValues_of_no_crossing (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1))) (u : Fin m → ℝ)
    (h : ∀ j : Fin r, dot (A j.succ) u = dot (A (parent S j.succ)) u) :
    BlockValues apex A u := by
  refine ⟨dot (A 0) u, fun i => Or.inr ?_⟩
  by_contra hi
  obtain ⟨j, hj⟩ := exists_parent_value_ne S (values A u) hi
  exact hj (h j)

/-- With only one possibly crossing edge, an outer apex/base tie forces a
block or braid pattern. This is an equality implication, not a genericity
assumption on the direction. -/
theorem block_or_braid_of_unique_edge_tie (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1))) (u : Fin m → ℝ)
    (j : Fin r)
    (hother : ∀ k : Fin r, k ≠ j → dot (A k.succ) u = dot (A (parent S k.succ)) u)
    (htie : dot apex u = baseMax (values A u) S) :
    BlockValues apex A u ∨ BraidValues apex A u := by
  by_cases hj : j.succ ∈ S
  · left
    have hw := unique_edge_cut_values S (values A u) j hj hother
    rw [baseMax_unique_cut S (values A u) j hj hother] at htie
    simp only [values] at htie hw
    rcases le_total (dot (A 0) u) (dot (A j.succ) u) with hle | hle
    · rw [max_eq_right hle] at htie
      refine ⟨dot (A 0) u, fun i => ?_⟩
      by_cases hi : i < j.succ
      · exact Or.inr (by simpa only [if_pos hi] using hw i)
      · apply Or.inl
        rw [htie]
        simpa only [if_neg hi] using hw i
    · rw [max_eq_left hle] at htie
      refine ⟨dot (A j.succ) u, fun i => ?_⟩
      by_cases hi : i < j.succ
      · apply Or.inl
        rw [htie]
        simpa only [if_pos hi] using hw i
      · exact Or.inr (by simpa only [if_neg hi] using hw i)
  · have hw := unique_edge_not_cut_values S (values A u) j hj hother
    rw [baseMax_single_pendant (values A u) S j hj (dot (A 0) u) hw] at htie
    simp only [values] at htie hw
    rcases le_total (dot (A 0) u) (dot (A j.succ) u) with hle | hle
    · left
      rw [max_eq_right hle] at htie
      have he : dot apex u = dot (A 0) u := by change _ = _ + _ - _ at htie; linarith
      refine ⟨dot (A j.succ) u, fun i => ?_⟩
      by_cases hi : i = j.succ
      · exact Or.inr (by rw [hi])
      · exact Or.inl ((hw i hi).trans he.symm)
    · right
      rw [max_eq_left hle] at htie
      refine ⟨j, dot (A 0) u, hw, ?_⟩
      change dot apex u = dot (A 0) u + dot (A 0) u - dot (A j.succ) u at htie
      linarith

/-- Exhaustive all-length facet-pattern theorem. Every direction outside the
two displayed patterns has lower-dimensional two-sided germ. Edge-vector
injectivity is needed only in the branch with two crossing edges. -/
theorem germDiff_caterpillarUnit_mem_LSpan_of_no_patterns (hr : 2 ≤ r)
    (apex : Fin m → ℝ) (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (hinj : Function.Injective (edgeVecs A S))
    (u : Fin m → ℝ) (hblock : ¬ BlockValues apex A u) (hbraid : ¬ BraidValues apex A u) :
    germDiff u (caterpillarUnit apex A S) ∈ LSpan m (r - 1) := by
  classical
  by_cases htwo : ∃ j k : Fin r, j ≠ k ∧
      dot (A j.succ) u ≠ dot (A (parent S j.succ)) u ∧
      dot (A k.succ) u ≠ dot (A (parent S k.succ)) u
  · obtain ⟨j, k, hjk, hj, hk⟩ := htwo
    exact germDiff_caterpillarUnit_mem_LSpan_of_two apex A S hinj u j k hjk
      (Ne.symm hj) (Ne.symm hk)
  · have hex : ∃ j : Fin r, dot (A j.succ) u ≠ dot (A (parent S j.succ)) u := by
      by_contra he
      apply hblock
      apply blockValues_of_no_crossing apex A S u
      intro j
      by_contra hj
      exact he ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hex
    have hother : ∀ k : Fin r, k ≠ j →
        dot (A k.succ) u = dot (A (parent S k.succ)) u := by
      intro k hk
      by_contra he
      exact htwo ⟨j, k, Ne.symm hk, hj, he⟩
    have hne : dot apex u ≠ baseMax (values A u) S := by
      intro he
      exact (block_or_braid_of_unique_edge_tie apex A S u j hother he).elim hblock hbraid
    have hotherNeg : ∀ k : Fin r, k ≠ j →
        dot (A k.succ) (-u) = dot (A (parent S k.succ)) (-u) := by
      intro k hk
      rw [UnitGermAux.dot_neg_right, UnitGermAux.dot_neg_right, hother k hk]
    have hneNeg : dot apex (-u) ≠ baseMax (values A (-u)) S := by
      intro he
      rcases block_or_braid_of_unique_edge_tie apex A S (-u) j hotherNeg he with hb | hb
      · apply hblock
        simpa only [neg_neg] using hb.neg
      · apply hbraid
        simpa only [neg_neg] using hb.neg
    have hsmall : germDiff u (caterpillarUnit apex A S) ∈ LSpan m 1 :=
      Submodule.sub_mem _ (germ_caterpillarUnit_mem_LSpan_one_of_ne apex A S u hne)
        (germ_caterpillarUnit_mem_LSpan_one_of_ne apex A S (-u) hneNeg)
    have hdim : 1 ≤ r - 1 := Nat.le_sub_of_add_le (show 1 + 1 ≤ r from hr)
    exact DoublingAux.LSpan_mono hdim hsmall

end MaxNN.Caterpillar
