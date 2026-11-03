import research.sN.overnight_20261103.constants.SharpTwo
import research.sN.overnight_20261103.constants.cherry_concentration.Theta

/-! The actual matching moment at the stronger 7K/10 isolated-gap threshold.
The only new constant comes from a proved count of the original slot layout.
All means are literal uniform finite permutation means. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace MaxCaterpillar.Overnight.Constants.Theta
open BigOperators Frontier.RandomRestriction
open GrowingMatching GoodEvent PerNeuron
open OvernightConstants.CherryConcentration
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

noncomputable def highTailRate (m K : ℕ) : ℝ :=
  49*(K:ℝ)/(120*(m:ℝ)*((m:ℝ)-1))

theorem high_good_implies_old_good (ρ : Equiv.Perm (Fin m)) (K : ℕ)
    (hQ : ρ∉highBadIsolatedEvent m K) : ρ∉badIsolatedEvent m K := by
  have hhigh := not_lt.mp (fun h => hQ ((mem_highBadIsolatedEvent ρ).mpr h))
  intro hbad
  have hlow := (mem_badIsolatedEvent ρ).mp hbad
  have hK : (0:ℝ)≤K := Nat.cast_nonneg _
  linarith only [hhigh,hlow,hK]

/-- A greater number of literal isolated slots strengthens the rate from
7/24 to49/120. The graph and deletion shift are arbitrary. -/
theorem high_lowRankMatchingMean_le_shifted (H : SimpleGraph (Fin m))
    [DecidableRel H.Adj] (ρ : Equiv.Perm (Fin m)) (K : ℕ) (η d : ℝ)
    (hm : 2≤m) (hK : 0<(K:ℝ)) (hQ : ρ∉highBadIsolatedEvent m K)
    (hE : η-d≤(H.edgeFinset.card:ℝ)) :
    lowRankMatchingMean H ρ K ≤ Real.exp (-(highTailRate m K*(η-d))) := by
  classical
  let slot := rankIsolatedSlots ρ K
  have hJ : (7/10:ℝ)*(K:ℝ)≤(Fintype.card (↥(rankIsolatedGaps ρ K)):ℝ) := by
    have hh := not_lt.mp (fun h => hQ ((mem_highBadIsolatedEvent ρ).mpr h))
    simpa only [Fintype.card_coe,rankIsolatedGaps] using hh
  have hJpos : 0<Fintype.card (↥(rankIsolatedGaps ρ K)) := by
    have hh : (0:ℝ)<Fintype.card (↥(rankIsolatedGaps ρ K)) :=
      lt_of_lt_of_le (mul_pos (by norm_num) hK) hJ
    exact_mod_cast hh
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith only [hmR]
  have hm1 : (0:ℝ)<(m:ℝ)-1 := by linarith only [hmR]
  have hD : 0<(m:ℝ)*((m:ℝ)-1) := mul_pos hm0 hm1
  have hc : 0<highTailRate m K := by
    exact div_pos (mul_pos (by norm_num) hK)
      (mul_pos (mul_pos (by norm_num) hm0) hm1)
  have ht : (0:ℝ)≤H.edgeFinset.card := Nat.cast_nonneg _
  have hh := MatchingSizeBias.matching_half_moment_le_all_graphs H
    (enumeratedSlot slot) (enumeratedSlot slot).injective hJpos
  have hnative : lowRankMatchingMean H ρ K ≤
      Real.exp (-(7/12:ℝ)*(Fintype.card (↥(rankIsolatedGaps ρ K)):ℝ)*
        (H.edgeFinset.card:ℝ)/((m:ℝ)*((m:ℝ)-1))) := by
    simpa only [enumerated_matchingCount_eq] using hh
  apply hnative.trans
  apply Real.exp_le_exp.mpr
  have hcoef : -(7/12:ℝ)*(Fintype.card (↥(rankIsolatedGaps ρ K)):ℝ)*
      (H.edgeFinset.card:ℝ) ≤ -(49/120:ℝ)*(K:ℝ)*(H.edgeFinset.card:ℝ) := by
    nlinarith only [hJ,ht]
  have hd := div_le_div_of_le hD.le hcoef
  calc
    _ ≤ -(highTailRate m K)*(H.edgeFinset.card:ℝ) := by
      convert hd using 1 <;> dsimp only [highTailRate] <;>
        field_simp [hm0.ne',hm1.ne'] <;> ring <;> simp
    _ ≤ -(highTailRate m K)*(η-d) :=
      mul_le_mul_of_nonpos_left hE (neg_nonpos.mpr hc.le)
    _ = _ := by ring

noncomputable def highSelectedTailMean (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Equiv.Perm (Fin n)→SimpleGraph (Fin m)) (k K : ℕ) : ℝ := by
  classical
  exact meanOver (fun σ : Equiv.Perm (Fin n) =>
    if σ∈selectedEvent G k 2 then
      meanOver (fun ρ : Equiv.Perm (Fin m) =>
        if ρ∉highBadIsolatedEvent m K then lowRankMatchingMean (H σ) ρ K else 0)
    else 0)

/-- Joint selected/tail cost at the stronger threshold, using the exact
two-matching envelope already verified in SharpTwo. -/
theorem highSelectedTailMean_le_two (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Equiv.Perm (Fin n)→SimpleGraph (Fin m))
    [hH : ∀ σ,DecidableRel (H σ).Adj] (k K : ℕ) (d : ℝ)
    (hkn : k≤n) (hm : 2≤m) (hK : 0<(K:ℝ))
    (hE : ∀ σ,(G.edgeFinset.card:ℝ)-d≤((H σ).edgeFinset.card:ℝ)) :
    highSelectedTailMean G H k K ≤
      (2/7:ℝ)*((k.descFactorial 4:ℝ)/(n.descFactorial 4:ℝ))*
        ((highTailRate m K)^2)⁻¹*Real.exp (highTailRate m K*d) := by
  classical
  let η : ℝ := G.edgeFinset.card
  let A : ℝ := (k.descFactorial 4:ℝ)/(n.descFactorial 4:ℝ)
  let c := highTailRate m K
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith only [hmR]
  have hm1 : (0:ℝ)<(m:ℝ)-1 := by linarith only [hmR]
  have hc : 0<c := by
    exact div_pos (mul_pos (by norm_num) hK)
      (mul_pos (mul_pos (by norm_num) hm0) hm1)
  have hA : 0≤A := by dsimp only [A]; positivity
  have hη : 0≤η := Nat.cast_nonneg _
  have htail : ∀ σ, meanOver (fun ρ : Equiv.Perm (Fin m) =>
      if ρ∉highBadIsolatedEvent m K then lowRankMatchingMean (H σ) ρ K else 0) ≤
      Real.exp (-(c*(η-d))) := by
    intro σ
    rw [←meanOver_const (Ω:=Equiv.Perm (Fin m)) (Real.exp (-(c*(η-d))))]
    apply meanOver_mono
    intro ρ
    by_cases hρ : ρ∉highBadIsolatedEvent m K
    · rw [if_pos hρ]
      exact high_lowRankMatchingMean_le_shifted (H σ) ρ K η d hm hK hρ (hE σ)
    · rw [if_neg hρ]
      exact (Real.exp_pos _).le
  have hraw : highSelectedTailMean G H k K ≤
      A*η^2/2*Real.exp (-(c*(η-d))) := by
    have hsel := selectedEvent_fraction_le G hkn (q:=2)
    have hstep : highSelectedTailMean G H k K ≤
        meanOver (fun σ : Equiv.Perm (Fin n) =>
          if σ∈selectedEvent G k 2 then Real.exp (-(c*(η-d))) else 0) := by
      apply meanOver_mono
      intro σ
      by_cases hs : σ∈selectedEvent G k 2
      · simp only [if_pos hs]
        exact htail σ
      · simp only [if_neg hs]
        exact le_refl _
    have heq : meanOver (fun σ : Equiv.Perm (Fin n) =>
        if σ∈selectedEvent G k 2 then Real.exp (-(c*(η-d))) else 0) =
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
        simp only [show (2:ℕ).factorial=2 by decide,show 2*2=4 from rfl,Nat.cast_ofNat]
        ring
  exact shifted_square_envelope _ A c η d hc hη hA hraw

#check @highSelectedTailMean_le_two
#print axioms high_good_implies_old_good
#print axioms high_lowRankMatchingMean_le_shifted
#print axioms highSelectedTailMean_le_two
end MaxCaterpillar.Overnight.Constants.Theta
