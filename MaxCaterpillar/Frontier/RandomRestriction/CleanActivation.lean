import MaxCaterpillar.Frontier.RandomRestriction.ActualClean
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.Linearization

/-! # Actual activation invariance away from a swapped dominant gap -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction
open BigOperators Cartesian DominantGap GoodEvent
variable {N h₁ h₂ m : ℕ}

/-- This includes identically zero restricted rows: their actual linear forms
vanish in both configurations. -/
theorem activation_matchingSwap_of_not_dominant
    (e : Fin m ↪ Fin N) (rho tau : Equiv.Perm (Fin m)) (K : ℕ)
    (g : ↥(rankIsolatedGaps rho K)) (w : Point N) (hz : (∑ i, w i) = 0)
    (T : ℝ)
    (hs : StableGap (tau,rho) (collapsedRow e w) T)
    (hs' : StableGap (Matching.swapTau (rankIsolatedSlots rho K) g tau,rho)
      (collapsedRow e w) T)
    (hnot : ¬GapDominant (tau,rho) (collapsedRow e w) g.val) :
    (0 < lin w (actualGapPoint e (Matching.swapTau (rankIsolatedSlots rho K) g tau,rho) T)) ↔
      0 < lin w (actualGapPoint e (tau,rho) T) := by
  classical
  by_cases hc : ∃ d, tailCoefficient (tau,rho) (collapsedRow e w) d ≠ 0
  · obtain ⟨d,hd⟩ := exists_dominant
      (tailCoefficient (tau,rho) (collapsedRow e w)) (fun d => (rho d).val)
      (fun a b h => rho.injective (Fin.ext h)) hc
    have hne : d ≠ g.val := by intro he; subst d; exact hnot hd
    have hg := (mem_isolatedGaps g.val (smallRankGaps rho K)).mp g.property
    have ha := actualGapPoint_swap_sign_iff_of_ne e (tau,rho) w hz
      (isolatedGapPredecessor g.val) g.val d
      (isolatedGapPredecessor_succ g.val hg.2.1)
      (isolatedGap_neighborRanksHigher rho tau K g) T hs
      (by simpa only [← matchingSwap_raw_eq] using hs') hd hne
    simpa only [← matchingSwap_raw_eq] using ha.1
  · have hall : ∀ d, tailCoefficient (tau,rho) (collapsedRow e w) d = 0 := by
      intro d; by_contra hn; exact hc ⟨d,hn⟩
    have htail := (tailCoefficient_all_zero_iff (tau,rho) (collapsedRow e w)).mp hall
    have h0 := hs.1.mpr htail
    have h0' := hs'.1.mpr htail
    have hl0 : lin w (actualGapPoint e (tau,rho) T) = 0 := by
      rw [lin_actualGapPoint_eq_weighted]
      exact h0
    have hl0' : lin w (actualGapPoint e (Matching.swapTau (rankIsolatedSlots rho K) g tau,rho) T) = 0 := by
      rw [lin_actualGapPoint_eq_weighted]
      exact h0'
    rw [hl0', hl0]

/-- Feeding non-braid first neurons have unchanged strict activation on every
actual isolated matching swap of a clean configuration. -/
theorem actualClean_nonbraid_activation (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (e : Fin m ↪ Fin N) (k : Fin h₂)
    (rho tau : Equiv.Perm (Fin m)) (K : ℕ) (g : ↥(rankIsolatedGaps rho K))
    (T : ℝ) (j : Fin h₁) (hW : net.W k j ≠ 0)
    (hcard : 3 ≤ (NormalizedNetwork.rowSupport (net.A j)).card)
    (hclean : ActualClean net e k rho K tau)
    (hs : StableGap (tau,rho) (collapsedRow e (net.A j)) T)
    (hs' : StableGap (Matching.swapTau (rankIsolatedSlots rho K) g tau,rho)
      (collapsedRow e (net.A j)) T) :
    activePattern net (actualGapPoint e (Matching.swapTau (rankIsolatedSlots rho K) g tau,rho) T) j =
      activePattern net (actualGapPoint e (tau,rho) T) j := by
  unfold activePattern
  congr 1
  exact propext (activation_matchingSwap_of_not_dominant e rho tau K g (net.A j)
    (hn.1 j) T hs hs' (hclean j hW hcard g.val g.property))

#print axioms activation_matchingSwap_of_not_dominant
#print axioms actualClean_nonbraid_activation
end MaxCaterpillar.Frontier.RandomRestriction
