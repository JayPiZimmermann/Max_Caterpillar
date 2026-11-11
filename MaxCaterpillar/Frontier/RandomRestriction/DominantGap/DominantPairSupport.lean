import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.PrefixSwapDominance
import Mathlib.Data.Finset.Card

/-! # A two-supported dominant row is the actual swapped endpoint pair -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.DominantGap
open BigOperators Cartesian

/-- Higher neighboring ranks force the two original endpoint weights to be
exactly the dominant prefix coefficient and its negative. -/
theorem dominant_gap_endpoint_coefficients {N m : ℕ} (e : Fin m ↪ Fin N)
    (p : RawConfig m) (A : Point N) (hzero : (∑ i,A i)=0)
    (a b : Fin m) (hab : a.val+1=b.val) (hrank : neighborRanksHigher p a b)
    (hd : GapDominant p (collapsedRow e A) b) :
    A (e (p.1 a))=tailCoefficient p (collapsedRow e A) b ∧
      A (e (p.1 b)) = -tailCoefficient p (collapsedRow e A) b := by
  let w := collapsedRow e A
  have hz : (∑ x,w x)=0 := collapsedRow_zero_sum e A hzero
  obtain ⟨hl,hr⟩ := neighborPrefixes_zero_of_dominant_not_above p w hz a b b hrank hd
    (fun h => Nat.lt_irrefl _ h)
  have ha := prefixCoeff_succ p w a
  have hb := prefixCoeff_succ p w b
  rw [hab,hl,zero_add] at ha
  rw [hr] at hb
  have hc : tailCoefficient p w b=prefixCoeff p w b.val := tailCoefficient_eq_prefixCoeff p w hz b
  change w (some (p.1 a))=tailCoefficient p w b ∧
    w (some (p.1 b)) = -tailCoefficient p w b
  constructor <;> linarith only [ha,hb,hc]

/-- A zero-sum original row supported on at most two coordinates and dominant
at a strict local-minimum gap is precisely that actual adjacent coordinate pair. -/
theorem dominant_gap_two_support_eq_pair {N m : ℕ} (e : Fin m ↪ Fin N)
    (p : RawConfig m) (A : Point N) (hzero : (∑ i,A i)=0)
    (hcard : (NormalizedNetwork.rowSupport A).card≤2)
    (a b : Fin m) (hab : a.val+1=b.val) (hrank : neighborRanksHigher p a b)
    (hd : GapDominant p (collapsedRow e A) b) :
    NormalizedNetwork.rowSupport A={e (p.1 a),e (p.1 b)} := by
  classical
  obtain ⟨hA,hB⟩ := dominant_gap_endpoint_coefficients e p A hzero a b hab hrank hd
  have hca : A (e (p.1 a))≠0 := by rw [hA]; exact hd.1
  have hcb : A (e (p.1 b))≠0 := by rw [hB]; exact neg_ne_zero.mpr hd.1
  have habne : a≠b := by
    intro he
    have hv := congrArg Fin.val he
    linarith only [hab,hv]
  have hne : e (p.1 a)≠e (p.1 b) := fun h => habne (p.1.injective (e.injective h))
  have hsub : ({e (p.1 a),e (p.1 b)} : Finset (Fin N))⊆NormalizedNetwork.rowSupport A := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact (NormalizedNetwork.mem_rowSupport A _).mpr hca
    · exact (NormalizedNetwork.mem_rowSupport A _).mpr hcb
  have hp : ({e (p.1 a),e (p.1 b)} : Finset (Fin N)).card=2 := Finset.card_doubleton hne
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hp]; exact hcard)).symm
end MaxCaterpillar.Frontier.RandomRestriction.DominantGap
