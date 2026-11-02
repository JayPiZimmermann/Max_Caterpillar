import MaxCaterpillar.Frontier.RandomRestriction.GoodEventCherriesGeometry

/-! # Literal disjoint tail pairs and rank-only slot layouts -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
variable {m K : ℕ}

/-- Distinct isolated selected gaps give disjoint two-element tail pairs. -/
theorem isolatedGapPairs_disjoint (Γ : Finset (Fin m))
    (g h : ↥(isolatedGaps Γ)) (hne : g ≠ h) :
    Disjoint ({isolatedGapPredecessor g.val,g.val} : Finset (Fin m))
      ({isolatedGapPredecessor h.val,h.val} : Finset (Fin m)) := by
  have hn (b c : Bool) : isolatedGapEndpoint Γ (g,b) ≠ isolatedGapEndpoint Γ (h,c) := by
    intro he
    exact hne (congrArg Prod.fst (isolatedGapEndpoint_injective Γ he))
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hn false false (hx.symm.trans hy)
  · exact hn false true (hx.symm.trans hy)
  · exact hn true false (hx.symm.trans hy)
  · exact hn true true (hx.symm.trans hy)

noncomputable def rankIsolatedGaps (ρ : Equiv.Perm (Fin m)) (K : ℕ) : Finset (Fin m) :=
  isolatedGaps (smallRankGaps ρ K)

/-- The full matching layout depends only on the actual rank permutation. -/
noncomputable def rankIsolatedSlots (ρ : Equiv.Perm (Fin m)) (K : ℕ) :
    (↥(rankIsolatedGaps ρ K) × Bool) ↪ Fin m :=
  isolatedGapSlots (smallRankGaps ρ K)

theorem rankIsolatedGaps_card_lower_bound (hKm : K ≤ m) (ρ : Equiv.Perm (Fin m)) :
    K - 1 - 2 * (selectedGapAdjacencies (smallRankGaps ρ K)).card ≤
      (rankIsolatedGaps ρ K).card := by
  have h := isolatedGaps_card_lower_bound (smallRankGaps ρ K)
  rw [card_smallRankGaps hKm] at h
  exact h

end MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
