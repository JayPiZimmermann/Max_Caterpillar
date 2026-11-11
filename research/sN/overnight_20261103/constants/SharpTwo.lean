import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.ConditionalBound
import MaxCaterpillar.Frontier.RandomRestriction.CoinRankSizeBiasConstants

/-! A sharp two-matching envelope. The generic exponential-series bound loses
the factor 2 exp(-2); the rational factor 2/7 retains most of that gain.
This research leaf changes no existing production declaration. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace MaxCaterpillar.Overnight.Constants
open BigOperators Frontier.RandomRestriction
open GrowingMatching Configurations DominantGap
attribute [local instance] Classical.propDecidable

theorem exp_two_ge_seven : (7 : ℝ) ≤ Real.exp 2 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

theorem square_exp_envelope (c η : ℝ) (hc : 0 < c) (hη : 0 ≤ η) :
    η^2 * Real.exp (-(c*η)) / 2 ≤ (2/7 : ℝ) * (c^2)⁻¹ := by
  have h := square_mul_exp_neg_le (c*η) (mul_nonneg hc.le hη)
  have he : Real.exp (-2 : ℝ) ≤ 1/7 := by
    rw [Real.exp_neg]
    simpa only [one_div] using inv_le_inv_of_le (by norm_num : (0:ℝ)<7) exp_two_ge_seven
  have hh : (c*η)^2 * Real.exp (-(c*η)) ≤ 4/7 := by
    linarith only [h,he]
  apply (mul_le_mul_right (pow_pos hc 2)).mp
  calc
    (η^2 * Real.exp (-(c*η)) / 2) * c^2 =
        ((c*η)^2 * Real.exp (-(c*η))) / 2 := by ring
    _ ≤ (4/7:ℝ)/2 := div_le_div_of_le (by norm_num) hh
    _ = ((2/7:ℝ)*(c^2)⁻¹)*c^2 := by
      rw [mul_assoc, inv_mul_cancel (pow_ne_zero 2 hc.ne')]
      norm_num

theorem shifted_square_envelope (P A c η d : ℝ)
    (hc : 0 < c) (hη : 0 ≤ η) (hA : 0 ≤ A)
    (hP : P ≤ A*η^2/2*Real.exp (-(c*(η-d)))) :
    P ≤ (2/7:ℝ)*A*(c^2)⁻¹*Real.exp (c*d) := by
  calc
    P ≤ A*η^2/2*Real.exp (-(c*(η-d))) := hP
    _ = (A*Real.exp (c*d))*(η^2*Real.exp (-(c*η))/2) := by
      rw [show -(c*(η-d)) = -(c*η)+c*d by ring, Real.exp_add]
      ring
    _ ≤ (A*Real.exp (c*d))*((2/7:ℝ)*(c^2)⁻¹) :=
      mul_le_mul_of_nonneg_left (square_exp_envelope c η hc hη)
        (mul_nonneg hA (Real.exp_pos _).le)
    _ = _ := by ring

variable {m n k h₁ h₂ : ℕ}

local instance totalNeZero [NeZero k] : NeZero (m+k) :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne k)) (Nat.le_add_left k m))⟩

/-- Exact uniform selected-tail average, with arbitrary real deletion shift. -/
theorem selectedTailMean_le_two (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Equiv.Perm (Fin n) → SimpleGraph (Fin m))
    [hH : ∀ σ, DecidableRel (H σ).Adj] (k K : ℕ) (d : ℝ)
    (hkn : k ≤ n) (hm : 2 ≤ m) (hK : 0 < (K:ℝ))
    (hE : ∀ σ, (G.edgeFinset.card:ℝ)-d ≤ ((H σ).edgeFinset.card:ℝ)) :
    selectedTailMean G H k 2 K ≤
      (2/7:ℝ)*((k.descFactorial 4:ℝ)/(n.descFactorial 4:ℝ))*
        ((tailRate m K)^2)⁻¹*Real.exp (tailRate m K*d) := by
  classical
  let η : ℝ := G.edgeFinset.card
  let A : ℝ := (k.descFactorial 4:ℝ)/(n.descFactorial 4:ℝ)
  let c := tailRate m K
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith only [hmR]
  have hm1 : (0:ℝ) < (m:ℝ)-1 := by linarith only [hmR]
  have hc : 0 < c := by
    exact div_pos (mul_pos (by norm_num) hK)
      (mul_pos (mul_pos (by norm_num) hm0) hm1)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hη : 0 ≤ η := Nat.cast_nonneg _
  have htail : ∀ σ, meanOver (fun ρ : Equiv.Perm (Fin m) =>
      if ρ ∉ GoodEvent.badIsolatedEvent m K then lowRankMatchingMean (H σ) ρ K else 0) ≤
      Real.exp (-(c*(η-d))) := by
    intro σ
    rw [←meanOver_const (Ω:=Equiv.Perm (Fin m)) (Real.exp (-(c*(η-d))))]
    apply meanOver_mono
    intro ρ
    by_cases hρ : ρ ∉ GoodEvent.badIsolatedEvent m K
    · rw [if_pos hρ]
      exact lowRankMatchingMean_le_shifted (H σ) ρ K η d hm hK hρ (hE σ)
    · rw [if_neg hρ]
      exact (Real.exp_pos _).le
  have hraw : selectedTailMean G H k 2 K ≤
      A*η^2/2*Real.exp (-(c*(η-d))) := by
    have hsel := selectedEvent_fraction_le G hkn (q:=2)
    have hstep : selectedTailMean G H k 2 K ≤
        meanOver (fun σ : Equiv.Perm (Fin n) =>
          if σ ∈ selectedEvent G k 2 then Real.exp (-(c*(η-d))) else 0) := by
      apply meanOver_mono
      intro σ
      by_cases hs : σ ∈ selectedEvent G k 2
      · simp only [if_pos hs]
        exact htail σ
      · simp only [if_neg hs]
        exact le_refl _
    have heq : meanOver (fun σ : Equiv.Perm (Fin n) =>
        if σ ∈ selectedEvent G k 2 then Real.exp (-(c*(η-d))) else 0) =
        ((selectedEvent G k 2).card:ℝ)/(Fintype.card (Equiv.Perm (Fin n)):ℝ)*
          Real.exp (-(c*(η-d))) := by
      unfold meanOver
      rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
      simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
      ring
    rw [heq] at hstep
    have hh := mul_le_mul_of_nonneg_right hsel (Real.exp_pos (-(c*(η-d)))).le
    apply hstep.trans
    calc
      _ ≤ (G.edgeFinset.card:ℝ)^2/(2:ℕ).factorial *
          ((k.descFactorial (2*2):ℝ)/(n.descFactorial (2*2):ℝ))*
            Real.exp (-(c*(η-d))) := hh
      _ = _ := by
        dsimp only [A,η]
        simp only [show (2:ℕ).factorial=2 by decide, show 2*2=4 from rfl,
          Nat.cast_ofNat]
        ring
  exact shifted_square_envelope _ A c η d hc hη hA hraw

/-- The improved envelope bounds the original actual neuron event. -/
theorem actualNeuron_fraction_le_two
    (net : NormalizedNetwork (m+k) h₁ h₂) (hn : net.TranslationNormalized)
    (K : ℕ) (T : ℝ) (r : Fin h₂) (hscale : CommonGapScale net T)
    (hm : 2 ≤ m) (hK : 0 < (K:ℝ)) :
    ((actualNeuronEvent net hn 2 K T r).card:ℝ)/Fintype.card (Configuration k m) ≤
      (2/7:ℝ)*((k.descFactorial 4:ℝ)/((m+k).descFactorial 4:ℝ))*
        ((tailRate m K)^2)⁻¹*Real.exp (tailRate m K*((k:ℝ)*((m:ℝ)+(k:ℝ)-1))) := by
  apply (actualNeuron_fraction_le_selectedTailMean net hn 2 K T r hscale).trans
  apply selectedTailMean_le_two _ _ k K ((k:ℝ)*((m:ℝ)+(k:ℝ)-1))
    (Nat.le_add_left k m) hm hK
  intro σ
  apply Configurations.baseTail_edge_card_lower_bound
  exact le_trans (by decide : 1 ≤ 2) (hm.trans (Nat.le_add_right m k))

/-- The finite actual-network transfer for two disjoint edges, with the
only structural hypothesis displayed explicitly. -/
theorem conditional_finite_transfer_two [NeZero k]
    (H : LocalMatchingObstruction k 2)
    (net : NormalizedNetwork (m+k) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x, net.eval x = Maximum (m+k) x)
    (K : ℕ) (hm : 2 ≤ m) (htotal : 4 ≤ m+k) (hK : 4 ≤ K) (hKm : K < m) :
    1-8*(K:ℝ)/(m:ℝ)-
      (BadFirst.largeSupportCount (firstSupports net):ℝ)*(k.descFactorial 3:ℝ)/((m+k).descFactorial 3:ℝ)-
      (∑ j, ((firstSupports net j).card.descFactorial 4:ℝ))/((m+k).descFactorial 4:ℝ)*
        ((K:ℝ)^2*(1+(k:ℝ)/(m:ℝ))/(1-(K:ℝ)/(m:ℝ))+
          (k.descFactorial 2:ℝ)*(K:ℝ)/2) ≤
      (h₂:ℝ)*(2/7:ℝ)*((k.descFactorial 4:ℝ)/((m+k).descFactorial 4:ℝ))*
        ((tailRate m K)^2)⁻¹*Real.exp (tailRate m K*((k:ℝ)*((m:ℝ)+(k:ℝ)-1))) := by
  classical
  obtain ⟨T,_hT,hscale⟩ := exists_common_gap_threshold net
  have hs := hscale T le_rfl
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hKpos : (0:ℝ) < K := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4) hK
  have hh := finite_union_fraction_bound
    (BadFirst.configurationBadFirstEvent k m (firstSupports net)) (shortRankEvent k m K)
    (feedingBadConfigurationsThree k (firstSupports net) K) (actualNeuronEvent net hn 2 K T)
    _ _ _ _ (actual_event_cover H (by decide : 0 < 2) net hn hnet K T hs)
    (BadFirst.configurationBadFirstEvent_fraction_le k m ((by decide : 3 ≤ 4).trans htotal) (firstSupports net))
    (shortRankEvent_fraction_le k K hmpos hKm.le hK)
    ((le_of_eq (feedingBadConfigurationsThree_fraction k (firstSupports net) K)).trans
      (GoodEvent.feedingBadFraction_le k (firstSupports net) K hmpos hKm htotal))
    (fun r => actualNeuron_fraction_le_two net hn K T r hs hm hKpos)
  simp only [Fintype.card_fin] at hh
  convert hh using 1 <;> ring

#check @conditional_finite_transfer_two
#print axioms square_exp_envelope
#print axioms selectedTailMean_le_two
#print axioms actualNeuron_fraction_le_two
#print axioms conditional_finite_transfer_two
end MaxCaterpillar.Overnight.Constants
