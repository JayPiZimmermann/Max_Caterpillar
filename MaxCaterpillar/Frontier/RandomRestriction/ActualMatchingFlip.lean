import MaxCaterpillar.Frontier.RandomRestriction.ActualMatchingRow

/-! # Actual effective-row flip identity from original-row dominance

Only a dominant gap at the swapped position can change a feeding activation.
Pair-supported rows are evaluated directly at the actual gap points, including
zero rows. The resulting indexed sum is the actual signed braid edge column.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction
open BigOperators Cartesian DominantGap GoodEvent NormalizedNetwork
variable {N h₁ h₂ m : ℕ}

theorem actualEffectiveRow_matchingSwap_of_nonpair
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (e : Fin m ↪ Fin N) (k : Fin h₂) (rho tau : Equiv.Perm (Fin m)) (K : ℕ)
    (g : ↥(rankIsolatedGaps rho K)) (T : ℝ) (hT : 0 < T)
    (hgeneric : GenericNetworkPoint net e (tau,rho) T)
    (hgeneric' : GenericNetworkPoint net e (Matching.swapTau (rankIsolatedSlots rho K) g tau,rho) T)
    (hnonpair : ∀ j, net.W k j ≠ 0 →
      ¬rowSupport (net.A j) ⊆ {e (tau (isolatedGapPredecessor g.val)),e (tau g.val)} →
      ¬GapDominant (tau,rho) (collapsedRow e (net.A j)) g.val) :
    actualEffectiveRow net k (actualGapPoint e (Matching.swapTau (rankIsolatedSlots rho K) g tau,rho) T) -
      actualEffectiveRow net k (actualGapPoint e (tau,rho) T) =
      braidEdgeWeight net.A (net.W k)
        (e (tau (isolatedGapPredecessor g.val))) (e (tau g.val)) •
          braidRoot (e (tau (isolatedGapPredecessor g.val))) (e (tau g.val)) := by
  classical
  let a := isolatedGapPredecessor g.val
  let c := g.val
  have hg := (mem_isolatedGaps g.val (smallRankGaps rho K)).mp g.property
  have hadj : a.val + 1 = c.val := isolatedGapPredecessor_succ g.val hg.2.1
  have hac : e (tau a) ≠ e (tau c) := by
    intro he
    have hv := congrArg Fin.val (tau.injective (e.injective he))
    linarith
  let b := activePattern net (actualGapPoint e (tau,rho) T)
  let b' := activePattern net (actualGapPoint e (Matching.swapTau (rankIsolatedSlots rho K) g tau,rho) T)
  have hpair : ∀ j, rowSupport (net.A j) ⊆ {e (tau a),e (tau c)} →
      coinCoefficient (b' j) - coinCoefficient (b j) = (-1:ℝ) * edgeCoinDifference (net.A j) (e (tau a)) (e (tau c)) := by
    intro j hj
    have hp := actualGapPoint_pair_activation_change e (tau,rho) T hT a c hadj
      (net.A j) (hn.1 j) hj
    simpa [b,b',activePattern,coinCoefficient,matchingSwap_raw_eq] using hp
  have hother : ∀ j, net.W k j ≠ 0 →
      ¬rowSupport (net.A j) ⊆ {e (tau a),e (tau c)} → b' j = b j := by
    intro j hW hj
    have hp := activation_matchingSwap_of_not_dominant e rho tau K g (net.A j) (hn.1 j) T
      (hgeneric.all_rows_stable (Sum.inl j)) (hgeneric'.all_rows_stable (Sum.inl j)) (hnonpair j hW hj)
    dsimp only [b,b',activePattern]
    congr 1
    exact propext hp
  have he := effectiveRow_sub_eq_braidCoinColumn net hn k b b' (e (tau a)) (e (tau c)) hac (-1) hpair hother
  change effectiveRow net b' k - effectiveRow net b k = _
  rw [he,smul_smul,neg_one_mul,neg_neg]

theorem actualMatchingRow_swap_of_nonpair
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (e : Fin m ↪ Fin N) (k : Fin h₂) (rho tau : Equiv.Perm (Fin m)) (K : ℕ)
    (g : ↥(rankIsolatedGaps rho K)) (T : ℝ) (hT : 0 < T)
    (hgeneric : GenericNetworkPoint net e (tau,rho) T)
    (hgeneric' : GenericNetworkPoint net e (Matching.swapTau (rankIsolatedSlots rho K) g tau,rho) T)
    (hnonpair : ∀ j, net.W k j ≠ 0 →
      ¬rowSupport (net.A j) ⊆ {e (tau (isolatedGapPredecessor g.val)),e (tau g.val)} →
      ¬GapDominant (tau,rho) (collapsedRow e (net.A j)) g.val) :
    actualMatchingRow net e k rho (Matching.swapTau (rankIsolatedSlots rho K) g tau) T -
      actualMatchingRow net e k rho tau T =
      braidEdgeWeight net.A (net.W k)
        (e (tau (isolatedGapPredecessor g.val))) (e (tau g.val)) •
          braidRoot (tau (isolatedGapPredecessor g.val)) (tau g.val) :=
  actualMatchingRow_sub_of_effective_difference net e k rho tau _ T _ _ _
    (actualEffectiveRow_matchingSwap_of_nonpair net hn e k rho tau K g T hT hgeneric hgeneric' hnonpair)

#print axioms actualEffectiveRow_matchingSwap_of_nonpair
#print axioms actualMatchingRow_swap_of_nonpair
end MaxCaterpillar.Frontier.RandomRestriction
