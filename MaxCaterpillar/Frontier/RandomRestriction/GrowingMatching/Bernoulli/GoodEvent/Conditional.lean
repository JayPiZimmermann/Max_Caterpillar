import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.Union
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.Expectations
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.RateMonotonicity

/-! # Actual bad-event probability after downward Bernoulli conditioning

The event probabilities below are literal permutation-cardinality ratios.
Only fixed original-label singleton and pair indicators use Harris domination.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
open BigOperators
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
variable {n : ℕ}

/-- The three explicit rates after accounting for unordered support roles. -/
noncomputable def badSupportRate (p : ℝ) (m K : ℕ) : ℝ :=
  (K:ℝ)^2/((1-(K:ℝ)/(m:ℝ))*(m.descFactorial 4:ℝ))+
  p*(K:ℝ)^2/((m:ℝ)*(1-(K:ℝ)/(m:ℝ))*(m.descFactorial 3:ℝ))+
  p^2*(K:ℝ)/(2*(m.descFactorial 2:ℝ))

lemma badSupportRate_eq_roleRates (p : ℝ) (m K : ℕ) :
    badSupportRate p m K=caseARate m K/4+p*caseBRate m K/2+p^2*caseCRate m K/4 := by
  unfold badSupportRate caseARate caseBRate caseCRate
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem conditional_caseAMean_le {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hpos : 0<mass p D)
    (T : Finset (Fin n)) (R : ACRole T) (m0 K : ℕ)
    (h0 : 4≤m0) (hK : K<m0)
    (htail : ∀ S∈D,m0≤Sampling.tailCount S) :
    condMean p D (fun S=>caseAMean T S K R)≤caseARate m0 K := by
  apply condMean_le_const hp0 hp1 D hpos
  intro S hS
  exact (caseAMean_le T S K R (h0.trans (htail S hS))
    (lt_of_lt_of_le hK (htail S hS))).trans
      (caseARate_le_of_tail_lower_bound h0 (htail S hS) hK)

theorem conditional_caseBMean_le {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (T : Finset (Fin n)) (R : BRole T) (m0 K : ℕ)
    (h0 : 4≤m0) (hK : K<m0)
    (htail : ∀ S∈D,m0≤Sampling.tailCount S) :
    condMean p D (fun S=>caseBMean T S K R)≤caseBRate m0 K*p := by
  classical
  calc
    _ ≤ condMean p D (fun S=>caseBRate m0 K*(if R.selected∈S then (1:ℝ) else 0)) := by
      apply condMean_mono_on hp0 hp1 D hpos
      intro S hS
      exact (caseBMean_le T S K R (h0.trans (htail S hS))
        (lt_of_lt_of_le hK (htail S hS))).trans
          (mul_le_mul_of_nonneg_right
            (caseBRate_le_of_tail_lower_bound h0 (htail S hS) hK) (by split_ifs <;> norm_num))
    _ = caseBRate m0 K*condMean p D (fun S=>if R.selected∈S then (1:ℝ) else 0) :=
      condMean_const_mul p D _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (condMean_mem_le hp0 hp1 D hD hpos R.selected)
      (caseBRate_nonneg h0 hK)

theorem conditional_caseCMean_le {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (T : Finset (Fin n)) (R : ACRole T) (m0 K : ℕ)
    (h0 : 4≤m0) (hK : K<m0)
    (htail : ∀ S∈D,m0≤Sampling.tailCount S) :
    condMean p D (fun S=>caseCMean T S K R)≤caseCRate m0 K*p^2 := by
  classical
  calc
    _ ≤ condMean p D (fun S=>caseCRate m0 K*(if R.other⊆S then (1:ℝ) else 0)) := by
      apply condMean_mono_on hp0 hp1 D hpos
      intro S hS
      exact (caseCMean_le T S K R (h0.trans (htail S hS))
        (lt_of_lt_of_le hK (htail S hS))).trans
          (mul_le_mul_of_nonneg_right
            (caseCRate_le_of_tail_lower_bound h0 (htail S hS)) (by split_ifs <;> norm_num))
    _ = caseCRate m0 K*condMean p D (fun S=>if R.other⊆S then (1:ℝ) else 0) :=
      condMean_const_mul p D _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (condMean_pair_subset_le hp0 hp1 D hD hpos R.other R.other_card)
      (caseCRate_nonneg _ _)

/-- A genuine support's literal bad-event fraction, under any downward conditioning. -/
theorem conditional_supportBadFraction_le {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (T : Finset (Fin n)) (m0 K : ℕ)
    (h0 : 4≤m0) (hK : K<m0)
    (htail : ∀ S∈D,m0≤Sampling.tailCount S) :
    condMean p D (fun S=>supportBadFraction T S K)≤
      (T.card.descFactorial 4:ℝ)*badSupportRate p m0 K := by
  classical
  have hA : (Fintype.card (ACRole T):ℝ)*4=(T.card.descFactorial 4:ℝ) := by
    exact_mod_cast card_acRole_mul_four T
  have hB : (Fintype.card (BRole T):ℝ)*2=(T.card.descFactorial 4:ℝ) := by
    exact_mod_cast card_bRole_mul_two T
  calc
    _ ≤ condMean p D (fun S=>(∑ R : ACRole T,caseAMean T S K R)+
        (∑ R : BRole T,caseBMean T S K R)+(∑ R : ACRole T,caseCMean T S K R)) :=
      condMean_mono_on hp0 hp1 D hpos (fun S _=>supportBadFraction_le_roleMeans T S K)
    _ = (∑ R : ACRole T,condMean p D (fun S=>caseAMean T S K R))+
        (∑ R : BRole T,condMean p D (fun S=>caseBMean T S K R))+
        (∑ R : ACRole T,condMean p D (fun S=>caseCMean T S K R)) := by
      rw [condMean_add,condMean_add,condMean_sum,condMean_sum,condMean_sum]
    _ ≤ (∑ _R : ACRole T,caseARate m0 K)+
        (∑ _R : BRole T,caseBRate m0 K*p)+
        (∑ _R : ACRole T,caseCRate m0 K*p^2) := by
      apply add_le_add
      · exact add_le_add
          (Finset.sum_le_sum (fun R _=>conditional_caseAMean_le hp0 hp1 D hpos T R m0 K h0 hK htail))
          (Finset.sum_le_sum (fun R _=>conditional_caseBMean_le hp0 hp1 D hD hpos T R m0 K h0 hK htail))
      · exact Finset.sum_le_sum (fun R _=>conditional_caseCMean_le hp0 hp1 D hD hpos T R m0 K h0 hK htail)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [badSupportRate_eq_roleRates]
      have ha : (Fintype.card (ACRole T):ℝ)=(T.card.descFactorial 4:ℝ)/4 := by linarith only [hA]
      have hb : (Fintype.card (BRole T):ℝ)=(T.card.descFactorial 4:ℝ)/2 := by linarith only [hB]
      rw [ha,hb]
      ring

/-- The original finite family, with all overlap handled by a literal union bound. -/
theorem conditional_familyBadFraction_le {κ : Type*} [Fintype κ]
    {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (supports : κ→Finset (Fin n)) (m0 K : ℕ)
    (h0 : 4≤m0) (hK : K<m0)
    (htail : ∀ S∈D,m0≤Sampling.tailCount S) :
    condMean p D (fun S=>familyBadFraction supports S K)≤
      (∑ j,( (supports j).card.descFactorial 4:ℝ))*badSupportRate p m0 K := by
  calc
    _ ≤ condMean p D (fun S=>∑ j,supportBadFraction (supports j) S K) :=
      condMean_mono_on hp0 hp1 D hpos (fun S _=>familyBadFraction_le_sum supports S K)
    _ = ∑ j,condMean p D (fun S=>supportBadFraction (supports j) S K) := condMean_sum p D _
    _ ≤ ∑ j,((supports j).card.descFactorial 4:ℝ)*badSupportRate p m0 K :=
      Finset.sum_le_sum (fun j _=>conditional_supportBadFraction_le hp0 hp1 D hD hpos
        (supports j) m0 K h0 hK htail)
    _ = _ := by rw [Finset.sum_mul]

#print axioms conditional_caseAMean_le
#print axioms conditional_caseBMean_le
#print axioms conditional_caseCMean_le
#print axioms conditional_supportBadFraction_le
#print axioms conditional_familyBadFraction_le
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
