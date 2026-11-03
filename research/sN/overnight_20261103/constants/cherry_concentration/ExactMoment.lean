import MaxCaterpillar.Frontier.RandomRestriction.GoodEventCherriesProbability
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Selected

/-! Exact first moment of selected path adjacencies in the literal uniform
rank-permutation model. No independent-selection hypothesis is used. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace MaxCaterpillar.OvernightConstants.CherryConcentration
open BigOperators Frontier.RandomRestriction Frontier.RandomRestriction.GoodEvent
variable {m K : ℕ}

lemma allGapAdjacencies_card (hm : 0 < m) :
    (allGapAdjacencies (m:=m)).card = m-1 := by
  classical
  have hsub : m-1+1=m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm)
  have hc : (Finset.univ : Finset (Fin (m-1))).card =
      (allGapAdjacencies (m:=m)).card := by
    apply Finset.card_congr
      (fun (i : Fin (m-1)) _ => ((⟨i.val, by have hi:=i.isLt; linarith only [hi,hsub]⟩,
        ⟨i.val+1, by have hi:=i.isLt; linarith only [hi,hsub]⟩) : Fin m × Fin m))
    · intro i hi
      exact (mem_allGapAdjacencies _ _).mpr rfl
    · intro i j _ _ he
      apply Fin.ext
      exact congrArg (fun p : Fin m × Fin m => p.1.val) he
    · intro p hp
      have hp' := (mem_allGapAdjacencies p.1 p.2).mp hp
      refine ⟨⟨p.1.val, by have hh:=p.2.isLt; linarith only [hh,hp',hsub]⟩,Finset.mem_univ _,?_⟩
      apply Prod.ext
      · exact Fin.ext rfl
      · exact Fin.ext hp'
  simpa only [Finset.card_univ,Fintype.card_fin] using hc.symm

lemma rank_containment_weight_pair (hm : 2 ≤ m) (hKm : K ≤ m)
    (a b : Fin m) (hab : a ≠ b) :
    containmentWeight
      (fun _ : Equiv.Perm (Fin m) => 1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ))
      (fun ρ => smallRankGaps ρ K) {a,b} =
      (K:ℝ)*((K:ℝ)-1)/((m:ℝ)*((m:ℝ)-1)) := by
  classical
  have hcard : ({a,b} : Finset (Fin m)).card = 2 := by simp [hab]
  have hh := GrowingMatching.containment_card_mul_descFactorial hKm ({a,b} : Finset (Fin m))
  rw [hcard] at hh
  have hhR : ((containmentEvent K ({a,b} : Finset (Fin m))).card:ℝ) *
      (m.descFactorial 2:ℝ) =
      (K.descFactorial 2:ℝ) * Fintype.card (Equiv.Perm (Fin m)) := by exact_mod_cast hh
  rw [Nat.cast_descFactorial_two,Nat.cast_descFactorial_two] at hhR
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hmp : (0:ℝ)<m := by linarith
  have hm1 : (0:ℝ)<(m:ℝ)-1 := by linarith
  have hP : (0:ℝ)<Fintype.card (Equiv.Perm (Fin m)) := by
    exact_mod_cast Fintype.card_pos
  unfold containmentWeight
  rw [←Finset.mul_sum,Finset.sum_boole]
  change (1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ)) *
      ((containmentEvent K ({a,b} : Finset (Fin m))).card:ℝ) = _
  apply (eq_div_iff (mul_pos hmp hm1).ne').mpr
  field_simp [hP.ne']
  nlinarith only [hhR]

/-- Exact expected adjacency count for a uniform K-subset selected by ranks. -/
theorem rankAverage_selectedGapAdjacencies_eq (hm : 2 ≤ m) (hKm : K ≤ m) :
    rankAverage K (fun Γ : Finset (Fin m) => ((selectedGapAdjacencies Γ).card:ℝ)) =
      (K:ℝ)*((K:ℝ)-1)/(m:ℝ) := by
  classical
  have hmpos : 0<m := lt_of_lt_of_le (by decide : 0<2) hm
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hmp : (0:ℝ)<m := by linarith
  have hm1 : (0:ℝ)<(m:ℝ)-1 := by linarith
  change (∑ ρ : Equiv.Perm (Fin m),
    (1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ)) *
      ((selectedGapAdjacencies (smallRankGaps ρ K)).card:ℝ)) = _
  rw [weighted_selectedGapAdjacencies_count_eq]
  have hsum : (∑ e in allGapAdjacencies (m:=m), containmentWeight
      (fun _ : Equiv.Perm (Fin m) => 1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ))
      (fun ρ => smallRankGaps ρ K) {e.1,e.2}) =
      ∑ _e in allGapAdjacencies (m:=m),
        (K:ℝ)*((K:ℝ)-1)/((m:ℝ)*((m:ℝ)-1)) := by
    apply Finset.sum_congr rfl
    intro e he
    apply rank_containment_weight_pair hm hKm
    intro h
    have hadj := (mem_allGapAdjacencies e.1 e.2).mp he
    have hval := congrArg Fin.val h
    linarith only [hadj,hval]
  rw [hsum,Finset.sum_const,nsmul_eq_mul,allGapAdjacencies_card hmpos]
  rw [Nat.cast_sub ((by decide : 1≤2).trans hm)]
  push_cast
  field_simp [hmp.ne',hm1.ne']
  <;> ring

#print axioms rank_containment_weight_pair
#print axioms rankAverage_selectedGapAdjacencies_eq
end MaxCaterpillar.OvernightConstants.CherryConcentration
