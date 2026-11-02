import MaxCaterpillar.Frontier.RandomRestriction.MatchingFiber
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventCherriesPairs
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.PrefixSwapDominance
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Model

/-!
# Actual cleanliness is constant on local matching-data fibers

Actual cleanliness says that no feeding non-braid row has an isolated selected
gap as its actual dominant gap. Its invariance follows from the proved
adjacent-prefix dominant-swap law. The literal role good event only needs to
imply this condition; no measurability of that larger role description is
assumed or needed here.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction
open BigOperators GoodEvent DominantGap Cartesian

variable {N h₁ h₂ m : ℕ}

noncomputable def ActualClean (net : NormalizedNetwork N h₁ h₂)
    (e : Fin m ↪ Fin N) (k : Fin h₂) (rho : Equiv.Perm (Fin m)) (K : ℕ)
    (tau : Equiv.Perm (Fin m)) : Prop :=
  ∀ j, net.W k j ≠ 0 → 3 ≤ (NormalizedNetwork.rowSupport (net.A j)).card →
    ∀ g ∈ rankIsolatedGaps rho K,
      ¬GapDominant (tau, rho) (collapsedRow e (net.A j)) g

theorem isolatedGap_neighborRanksHigher (rho tau : Equiv.Perm (Fin m)) (K : ℕ)
    (g : ↥(rankIsolatedGaps rho K)) :
    neighborRanksHigher (tau, rho) (isolatedGapPredecessor g.val) g.val := by
  have hg := (mem_isolatedGaps g.val (smallRankGaps rho K)).mp g.property
  have hgsmall : (rho g.val).val < K := (mem_smallRankGaps _ _).mp hg.1
  have hpred : isolatedGapPredecessor g.val ∉ smallRankGaps rho K := by
    intro hp
    exact (hg.2.2 _ hp).1 (isolatedGapPredecessor_succ g.val hg.2.1)
  have hpredHigh : K ≤ (rho (isolatedGapPredecessor g.val)).val := by
    by_contra h
    exact hpred ((mem_smallRankGaps _ _).mpr (lt_of_not_ge h))
  refine ⟨lt_of_lt_of_le hgsmall hpredHigh, ?_⟩
  intro c hc
  have hnot : c ∉ smallRankGaps rho K := by
    intro hm
    exact (hg.2.2 c hm).2 hc.symm
  have hhigh : K ≤ (rho c).val := by
    by_contra h
    exact hnot ((mem_smallRankGaps _ _).mpr (lt_of_not_ge h))
  exact lt_of_lt_of_le hgsmall hhigh

lemma matchingSwap_raw_eq (rho tau : Equiv.Perm (Fin m)) (K : ℕ)
    (g : ↥(rankIsolatedGaps rho K)) :
    (Matching.swapTau (rankIsolatedSlots rho K) g tau, rho) =
      swapAdjacentConfig (tau, rho) (isolatedGapPredecessor g.val) g.val := rfl

theorem gapDominant_matchingSwap_iff (rho tau : Equiv.Perm (Fin m)) (K : ℕ)
    (g : ↥(rankIsolatedGaps rho K)) (w : Option (Fin m) → ℝ)
    (hzero : (∑ x, w x) = 0) (d : Fin m) :
    GapDominant (Matching.swapTau (rankIsolatedSlots rho K) g tau, rho) w d ↔
      GapDominant (tau, rho) w d := by
  have hg := (mem_isolatedGaps g.val (smallRankGaps rho K)).mp g.property
  have hadj := isolatedGapPredecessor_succ g.val hg.2.1
  constructor
  · intro hd
    have h := gapDominant_swap_and_leading
      (Matching.swapTau (rankIsolatedSlots rho K) g tau, rho) w hzero
      (isolatedGapPredecessor g.val) g.val d hadj
      (isolatedGap_neighborRanksHigher rho _ K g) hd
    have he : swapAdjacentConfig
        (Matching.swapTau (rankIsolatedSlots rho K) g tau, rho)
        (isolatedGapPredecessor g.val) g.val = (tau, rho) := by
      rw [← matchingSwap_raw_eq]
      rw [Matching.swapTau_involutive]
    simpa only [he] using h.1
  · intro hd
    have h := gapDominant_swap_and_leading (tau, rho) w hzero
      (isolatedGapPredecessor g.val) g.val d hadj
      (isolatedGap_neighborRanksHigher rho tau K g) hd
    simpa only [matchingSwap_raw_eq] using h.1

theorem actualClean_swapTau (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (e : Fin m ↪ Fin N) (k : Fin h₂)
    (rho : Equiv.Perm (Fin m)) (K : ℕ) (g : ↥(rankIsolatedGaps rho K))
    (tau : Equiv.Perm (Fin m)) :
    ActualClean net e k rho K (Matching.swapTau (rankIsolatedSlots rho K) g tau) ↔
      ActualClean net e k rho K tau := by
  constructor
  · intro hclean j hW hs d hd hdom
    exact hclean j hW hs d hd ((gapDominant_matchingSwap_iff rho tau K g
      (collapsedRow e (net.A j)) (collapsedRow_zero_sum e _ (hn.1 j)) d).mpr hdom)
  · intro hclean j hW hs d hd hdom
    exact hclean j hW hs d hd ((gapDominant_matchingSwap_iff rho tau K g
      (collapsedRow e (net.A j)) (collapsedRow_zero_sum e _ (hn.1 j)) d).mp hdom)

theorem actualClean_constant_on_fiber (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (e : Fin m ↪ Fin N) (k : Fin h₂)
    (rho : Equiv.Perm (Fin m)) (K : ℕ)
    (u : Matching.Data (↥(rankIsolatedGaps rho K)) m)
    (p q : Matching.Fiber (rankIsolatedSlots rho K) u) :
    ActualClean net e k rho K p.val ↔ ActualClean net e k rho K q.val := by
  have h := Matching.invariant_constant (rankIsolatedSlots rho K) u
    (fun p => ActualClean net e k rho K p.val)
    (fun g p => propext (actualClean_swapTau net hn e k rho K g p.val)) p q
  exact Iff.of_eq h

#check @ActualClean
#check @actualClean_constant_on_fiber
#print axioms isolatedGap_neighborRanksHigher
#print axioms gapDominant_matchingSwap_iff
#print axioms actualClean_swapTau
#print axioms actualClean_constant_on_fiber
end MaxCaterpillar.Frontier.RandomRestriction
