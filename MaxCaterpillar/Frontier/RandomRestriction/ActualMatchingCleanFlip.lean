import MaxCaterpillar.Frontier.RandomRestriction.ActualMatchingFlip
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.DominantPairSupport

/-! # Clean actual configurations supply the full network flip law

For small-support feeding rows, dominance at the selected gap forces the exact
swapped pair. Feeding larger-support rows are excluded by actual cleanliness.
Thus every original row is covered, without merging parallel rows or imposing
sign restrictions on first or second weights.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction
open BigOperators Cartesian DominantGap GoodEvent NormalizedNetwork
variable {N h₁ h₂ m : ℕ}

theorem actualClean_nonpair_not_dominant
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (e : Fin m ↪ Fin N) (k : Fin h₂) (rho tau : Equiv.Perm (Fin m)) (K : ℕ)
    (g : ↥(rankIsolatedGaps rho K)) (hclean : ActualClean net e k rho K tau)
    (j : Fin h₁) (hW : net.W k j ≠ 0)
    (hnot : ¬rowSupport (net.A j) ⊆
      {e (tau (isolatedGapPredecessor g.val)),e (tau g.val)}) :
    ¬GapDominant (tau,rho) (collapsedRow e (net.A j)) g.val := by
  intro hd
  by_cases hlarge : 3 ≤ (rowSupport (net.A j)).card
  · exact hclean j hW hlarge g.val g.property hd
  · have hsmall : (rowSupport (net.A j)).card ≤ 2 := by linarith
    have hg := (mem_isolatedGaps g.val (smallRankGaps rho K)).mp g.property
    have hp := dominant_gap_two_support_eq_pair e (tau,rho) (net.A j) (hn.1 j)
      hsmall (isolatedGapPredecessor g.val) g.val
      (isolatedGapPredecessor_succ g.val hg.2.1)
      (isolatedGap_neighborRanksHigher rho tau K g) hd
    exact hnot hp.le

/-- The actual restricted second-row change on a clean permutation is derived
from the actual first-layer activation changes and all original real weights. -/
theorem actualMatchingRow_swap (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (e : Fin m ↪ Fin N) (k : Fin h₂)
    (rho tau : Equiv.Perm (Fin m)) (K : ℕ)
    (g : ↥(rankIsolatedGaps rho K)) (T : ℝ) (hT : 0 < T)
    (hgeneric : GenericNetworkPoint net e (tau,rho) T)
    (hgeneric' : GenericNetworkPoint net e (Matching.swapTau (rankIsolatedSlots rho K) g tau,rho) T)
    (hclean : ActualClean net e k rho K tau) :
    actualMatchingRow net e k rho (Matching.swapTau (rankIsolatedSlots rho K) g tau) T -
      actualMatchingRow net e k rho tau T =
      braidEdgeWeight net.A (net.W k)
        (e (tau (isolatedGapPredecessor g.val))) (e (tau g.val)) •
          braidRoot (tau (isolatedGapPredecessor g.val)) (tau g.val) :=
  actualMatchingRow_swap_of_nonpair net hn e k rho tau K g T hT hgeneric hgeneric'
    (actualClean_nonpair_not_dominant net hn e k rho tau K g hclean)

#print axioms actualClean_nonpair_not_dominant
#print axioms actualMatchingRow_swap
end MaxCaterpillar.Frontier.RandomRestriction
