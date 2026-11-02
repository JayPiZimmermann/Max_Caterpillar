import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.PrefixSwap
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.DominantSwap
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.LiftedPoint

/-! # Actual adjacent gap swaps preserve the dominant index

A locally lower-rank gap may change its coefficient arbitrarily when a higher
coefficient shields it. If no higher dominant coefficient shields the gap,
the higher-ranked neighbors have zero prefixes and the changed coefficient
negates. The final virtual boundary uses the actual total zero sum.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.DominantGap
open BigOperators Cartesian

/-- Both existing neighbors of the separating gap have higher original rho
rank. The quantified right neighbor is absent at the full-tail boundary. -/
def neighborRanksHigher {m : ℕ} (p : RawConfig m) (a b : Fin m) : Prop :=
  (p.2 b).val<(p.2 a).val ∧
    ∀ c : Fin m,c.val=b.val+1→(p.2 b).val<(p.2 c).val

/-- If the separating gap is not below the dominant gap, its higher-rank
neighbor prefixes vanish, including the virtual zero-sum boundary. -/
theorem neighborPrefixes_zero_of_dominant_not_above {m : ℕ}
    (p : RawConfig m) (w : Option (Fin m)→ℝ) (hzero : (∑ x,w x)=0)
    (a b d : Fin m) (hrank : neighborRanksHigher p a b)
    (hd : GapDominant p w d) (hnot : ¬(p.2 b).val<(p.2 d).val) :
    prefixCoeff p w a.val=0 ∧ prefixCoeff p w (b.val+1)=0 := by
  have hz (i : Fin m) (hi : (p.2 b).val<(p.2 i).val) : tailCoefficient p w i=0 := by
    by_contra hc
    by_cases he : i=d
    · exact hnot (by simpa only [he] using hi)
    · exact hnot (lt_trans hi (hd.2 i hc he))
  constructor
  · rw [← tailCoefficient_eq_prefixCoeff p w hzero a]
    exact hz a hrank.1
  · by_cases hright : b.val+1<m
    · let c : Fin m := ⟨b.val+1,hright⟩
      change prefixCoeff p w c.val=0
      rw [← tailCoefficient_eq_prefixCoeff p w hzero c]
      exact hz c (hrank.2 c rfl)
    · have hboundary : b.val+1=m :=
        Nat.le_antisymm (Nat.succ_le_iff.mpr b.isLt) (not_lt.mp hright)
      rw [hboundary,prefixCoeff_at_card,hzero]

/-- The actual dominant gap is invariant under the adjacent tau swap. Only
when that gap is the swapped gap does its leading coefficient negate. -/
theorem gapDominant_swap_and_leading {m : ℕ} (p : RawConfig m)
    (w : Option (Fin m)→ℝ) (hzero : (∑ x,w x)=0)
    (a b d : Fin m) (hab : a.val+1=b.val) (hrank : neighborRanksHigher p a b)
    (hd : GapDominant p w d) :
    GapDominant (swapAdjacentConfig p a b) w d ∧
      tailCoefficient (swapAdjacentConfig p a b) w d=
        if d=b then -tailCoefficient p w d else tailCoefficient p w d := by
  classical
  have haway : ∀ i : Fin m,i≠b→
      tailCoefficient (swapAdjacentConfig p a b) w i=tailCoefficient p w i :=
    fun i hi => tailCoefficient_swap_other_gap p w hzero a b hab i hi
  by_cases hcut : (p.2 b).val<(p.2 d).val
  · have h := dominant_and_leading_eq_of_change_below (g := b) hd hcut haway
    have hdb : d≠b := by
      intro he
      rw [he] at hcut
      exact Nat.lt_irrefl _ hcut
    exact ⟨h.1,by simpa only [if_neg hdb] using h.2⟩
  · obtain ⟨hl,hr⟩ := neighborPrefixes_zero_of_dominant_not_above p w hzero a b d hrank hd hcut
    have hflip := tailCoefficient_swap_neg_of_neighbors p w hzero a b hab hl hr
    exact ⟨dominant_of_single_sign_flip hd hflip haway,
      leading_eq_of_single_sign_flip hflip haway⟩

/-- The actual StableGap evidence supplies the generic stable-evaluation
hypothesis without changing the original coefficient family. -/
lemma stableGap_to_stableEvaluation {m : ℕ} {p : RawConfig m}
    {w : Option (Fin m)→ℝ} {T : ℝ} (hs : StableGap p w T) :
    StableEvaluation (tailCoefficient p w) (fun g => (p.2 g).val) T := by
  have hv : gapValue p w T=powerSum (tailCoefficient p w) (fun g => (p.2 g).val) T :=
    weighted_gapPoint_eq_sum p w T
  constructor
  · rw [← hv]
    exact hs.1.trans (tailCoefficient_all_zero_iff p w).symm
  · intro g hg
    rw [← hv]
    exact hs.2 g hg

/-- Actual scalar activation signs are unchanged when the dominant gap is not
this swapped gap. Lower coefficient magnitudes need not be invariant. -/
theorem stableGap_swap_sign_iff_of_ne {m : ℕ} (p : RawConfig m)
    (w : Option (Fin m)→ℝ) (hzero : (∑ x,w x)=0)
    (a b d : Fin m) (hab : a.val+1=b.val) (hrank : neighborRanksHigher p a b)
    (T : ℝ) (hs : StableGap p w T) (hs' : StableGap (swapAdjacentConfig p a b) w T)
    (hd : GapDominant p w d) (hdb : d≠b) :
    (0<gapValue (swapAdjacentConfig p a b) w T↔0<gapValue p w T) ∧
      (gapValue (swapAdjacentConfig p a b) w T<0↔gapValue p w T<0) := by
  have h := gapDominant_swap_and_leading p w hzero a b d hab hrank hd
  have hlead : tailCoefficient (swapAdjacentConfig p a b) w d=tailCoefficient p w d := by
    simpa only [if_neg hdb] using h.2
  have ha := stable_sign_iff_of_common_dominant (stableGap_to_stableEvaluation hs)
    (stableGap_to_stableEvaluation (p := swapAdjacentConfig p a b) hs') hd h.1 hlead
  simpa only [gapValue,weighted_gapPoint_eq_sum,powerSum] using ha

/-- At the dominant swapped gap, the strict actual activation bit is complemented. -/
theorem stableGap_swap_positive_iff_not_positive {m : ℕ} (p : RawConfig m)
    (w : Option (Fin m)→ℝ) (hzero : (∑ x,w x)=0)
    (a b : Fin m) (hab : a.val+1=b.val) (hrank : neighborRanksHigher p a b)
    (T : ℝ) (hs : StableGap p w T) (hs' : StableGap (swapAdjacentConfig p a b) w T)
    (hd : GapDominant p w b) :
    0<gapValue (swapAdjacentConfig p a b) w T↔¬0<gapValue p w T := by
  have h := gapDominant_swap_and_leading p w hzero a b b hab hrank hd
  have hflip : tailCoefficient (swapAdjacentConfig p a b) w b= -tailCoefficient p w b := by
    simpa only [if_pos rfl] using h.2
  have haway : ∀ i : Fin m,i≠b→
      tailCoefficient (swapAdjacentConfig p a b) w i=tailCoefficient p w i :=
    fun i hi => tailCoefficient_swap_other_gap p w hzero a b hab i hi
  have ha := stable_positive_iff_not_positive_of_single_sign_flip
    (stableGap_to_stableEvaluation hs) (stableGap_to_stableEvaluation (p := swapAdjacentConfig p a b) hs') hd hflip haway
  simpa only [gapValue,weighted_gapPoint_eq_sum,powerSum] using ha

/-- The same sign law for actual original-coordinate linear forms. -/
theorem actualGapPoint_swap_sign_iff_of_ne {N m : ℕ} (e : Fin m ↪ Fin N)
    (p : RawConfig m) (w : Point N) (hzero : (∑ i,w i)=0)
    (a b d : Fin m) (hab : a.val+1=b.val) (hrank : neighborRanksHigher p a b)
    (T : ℝ) (hs : StableGap p (collapsedRow e w) T)
    (hs' : StableGap (swapAdjacentConfig p a b) (collapsedRow e w) T)
    (hd : GapDominant p (collapsedRow e w) d) (hdb : d≠b) :
    (0<lin w (actualGapPoint e (swapAdjacentConfig p a b) T)↔0<lin w (actualGapPoint e p T)) ∧
      (lin w (actualGapPoint e (swapAdjacentConfig p a b) T)<0↔lin w (actualGapPoint e p T)<0) := by
  have h := stableGap_swap_sign_iff_of_ne p (collapsedRow e w) (collapsedRow_zero_sum e w hzero)
    a b d hab hrank T hs hs' hd hdb
  simpa only [gapValue,lin_actualGapPoint_eq_weighted] using h

/-- A complete actual activation law: it flips exactly at its own dominant gap,
and is fixed under every other adjacent higher-neighbor swap. -/
theorem actualGapPoint_swap_activation {N m : ℕ} (e : Fin m ↪ Fin N)
    (p : RawConfig m) (w : Point N) (hzero : (∑ i,w i)=0)
    (a b d : Fin m) (hab : a.val+1=b.val) (hrank : neighborRanksHigher p a b)
    (T : ℝ) (hs : StableGap p (collapsedRow e w) T)
    (hs' : StableGap (swapAdjacentConfig p a b) (collapsedRow e w) T)
    (hd : GapDominant p (collapsedRow e w) d) :
    (0<lin w (actualGapPoint e (swapAdjacentConfig p a b) T)) ↔
      if d=b then ¬(0<lin w (actualGapPoint e p T)) else 0<lin w (actualGapPoint e p T) := by
  classical
  by_cases hdb : d=b
  · subst d
    rw [if_pos rfl]
    have h := stableGap_swap_positive_iff_not_positive p (collapsedRow e w)
      (collapsedRow_zero_sum e w hzero) a b hab hrank T hs hs' hd
    simpa only [gapValue,lin_actualGapPoint_eq_weighted] using h
  · rw [if_neg hdb]
    exact (actualGapPoint_swap_sign_iff_of_ne e p w hzero a b d hab hrank T hs hs' hd hdb).1
end MaxCaterpillar.Frontier.RandomRestriction.DominantGap
