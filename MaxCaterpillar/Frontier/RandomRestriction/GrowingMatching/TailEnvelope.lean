import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Selected
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.ExpSeries
import MaxCaterpillar.Frontier.RandomRestriction.PerNeuronMatching
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventCherriesProbability
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventCherriesPairs

/-! # Actual selected-matching and uniform-tail moment envelope

The finite means below are literal permutation means. The only deletion input
is an ordinary edge-cardinality lower bound, not a probability conclusion.
The general-arity configuration model discharges it for actual induced tails.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
open BigOperators GoodEvent PerNeuron
variable {m n k q K : ℕ}

noncomputable def meanOver {Ω : Type*} [Fintype Ω] (f : Ω→ℝ) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ ω,f ω

theorem meanOver_mono {Ω : Type*} [Fintype Ω] (f g : Ω→ℝ)
    (h : ∀ω,f ω≤g ω) : meanOver f≤meanOver g := by
  apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ω _ => h ω))
  positivity

theorem meanOver_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    meanOver (fun _ : Ω=>c)=c := by
  unfold meanOver
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←mul_assoc,
    inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),one_mul]

noncomputable def lowRankMatchingMean (H : SimpleGraph (Fin m))
    (ρ : Equiv.Perm (Fin m)) (K : ℕ) : ℝ :=
  meanOver (fun τ : Equiv.Perm (Fin m) =>
    (1/2:ℝ)^nativeMatchingCount H (rankIsolatedSlots ρ K) τ)

noncomputable def tailRate (m K : ℕ) : ℝ :=
  7*(K:ℝ)/(24*(m:ℝ)*((m:ℝ)-1))

/-- The actual partial matching moment at every admissible rank permutation.
No empty-graph exception or assumed uniform-tail law is needed. -/
theorem lowRankMatchingMean_le_shifted (H : SimpleGraph (Fin m))
    [DecidableRel H.Adj] (ρ : Equiv.Perm (Fin m)) (K : ℕ) (η d : ℝ)
    (hm : 2≤m) (hK : 0<(K:ℝ)) (hQ : ρ∉badIsolatedEvent m K)
    (hE : η-d≤(H.edgeFinset.card:ℝ)) :
    lowRankMatchingMean H ρ K ≤ Real.exp (-(tailRate m K*(η-d))) := by
  classical
  let slot := rankIsolatedSlots ρ K
  have hJ : (K:ℝ)/2≤(Fintype.card (↥(rankIsolatedGaps ρ K)):ℝ) := by
    have hh := not_lt.mp (fun h => hQ ((mem_badIsolatedEvent ρ).mpr h))
    simpa only [Fintype.card_coe,rankIsolatedGaps] using hh
  have hJpos : 0<Fintype.card (↥(rankIsolatedGaps ρ K)) := by
    have hh : (0:ℝ)<Fintype.card (↥(rankIsolatedGaps ρ K)) :=
      lt_of_lt_of_le (half_pos hK) hJ
    exact_mod_cast hh
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith only [hmR]
  have hm1 : (0:ℝ)<(m:ℝ)-1 := by linarith only [hmR]
  have hD : 0<(m:ℝ)*((m:ℝ)-1) := mul_pos hm0 hm1
  have hc : 0<tailRate m K := by
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
      (H.edgeFinset.card:ℝ) ≤ -(7/24:ℝ)*(K:ℝ)*(H.edgeFinset.card:ℝ) := by
    nlinarith only [hJ,ht]
  have hd := div_le_div_of_le hD.le hcoef
  calc
    _ ≤ -(tailRate m K)*(H.edgeFinset.card:ℝ) := by
      convert hd using 1 <;> dsimp only [tailRate] <;>
        field_simp [hm0.ne',hm1.ne'] <;> ring <;> simp
    _ ≤ -(tailRate m K)*(η-d) :=
      mul_le_mul_of_nonpos_left hE (neg_nonpos.mpr hc.le)
    _ = _ := by ring

/-- The literal selected-matching event averaged jointly with its actual
complement-tail moment and actual isolated-rank event. -/
noncomputable def selectedTailMean (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Equiv.Perm (Fin n)→SimpleGraph (Fin m)) (k q K : ℕ) : ℝ := by
  classical
  exact meanOver (fun σ : Equiv.Perm (Fin n) =>
    if σ∈selectedEvent G k q then
      meanOver (fun ρ : Equiv.Perm (Fin m) =>
        if ρ∉badIsolatedEvent m K then lowRankMatchingMean (H σ) ρ K else 0)
    else 0)

/-- A graph-theoretic edge-deletion input implies a genuine finite averaged
moment bound. The factorial in selected matching counting cancels against
one exponential-series term. -/
theorem selectedTailMean_le (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Equiv.Perm (Fin n)→SimpleGraph (Fin m))
    [hH : ∀σ,DecidableRel (H σ).Adj] (k q K : ℕ) (d : ℝ)
    (hkn : k≤n) (hm : 2≤m) (hK : 0<(K:ℝ))
    (hE : ∀σ,(G.edgeFinset.card:ℝ)-d≤((H σ).edgeFinset.card:ℝ)) :
    selectedTailMean G H k q K ≤
      ((k.descFactorial (2*q):ℝ)/(n.descFactorial (2*q):ℝ))*
        ((tailRate m K)^q)⁻¹*Real.exp (tailRate m K*d) := by
  classical
  let η : ℝ := G.edgeFinset.card
  let A : ℝ := (k.descFactorial (2*q):ℝ)/(n.descFactorial (2*q):ℝ)
  let c := tailRate m K
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith only [hmR]
  have hm1 : (0:ℝ)<(m:ℝ)-1 := by linarith only [hmR]
  have hc : 0<c := by
    exact div_pos (mul_pos (by norm_num) hK)
      (mul_pos (mul_pos (by norm_num) hm0) hm1)
  have hA : 0≤A := by dsimp only [A]; positivity
  have hη : 0≤η := Nat.cast_nonneg _
  have htail : ∀σ, meanOver (fun ρ : Equiv.Perm (Fin m) =>
      if ρ∉badIsolatedEvent m K then lowRankMatchingMean (H σ) ρ K else 0) ≤
      Real.exp (-(c*(η-d))) := by
    intro σ
    rw [←meanOver_const (Ω:=Equiv.Perm (Fin m)) (Real.exp (-(c*(η-d))))]
    apply meanOver_mono
    intro ρ
    by_cases hρ : ρ∉badIsolatedEvent m K
    · rw [if_pos hρ]
      exact lowRankMatchingMean_le_shifted (H σ) ρ K η d hm hK hρ (hE σ)
    · rw [if_neg hρ]
      exact (Real.exp_pos _).le
  have hraw : selectedTailMean G H k q K ≤
      A*η^q/(q.factorial:ℝ)*Real.exp (-(c*(η-d))) := by
    have hsel := selectedEvent_fraction_le G hkn (q:=q)
    have hstep : selectedTailMean G H k q K ≤
        meanOver (fun σ : Equiv.Perm (Fin n) =>
          if σ∈selectedEvent G k q then Real.exp (-(c*(η-d))) else 0) := by
      apply meanOver_mono
      intro σ
      by_cases hs : σ∈selectedEvent G k q
      · simp only [if_pos hs]
        exact htail σ
      · simp only [if_neg hs]
        exact le_refl _
    have heq : meanOver (fun σ : Equiv.Perm (Fin n) =>
        if σ∈selectedEvent G k q then Real.exp (-(c*(η-d))) else 0) =
        ((selectedEvent G k q).card:ℝ)/(Fintype.card (Equiv.Perm (Fin n)):ℝ)*
          Real.exp (-(c*(η-d))) := by
      unfold meanOver
      rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
      simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
      ring
    rw [heq] at hstep
    have hh := mul_le_mul_of_nonneg_right hsel (Real.exp_pos (-(c*(η-d)))).le
    apply hstep.trans
    convert hh using 1 <;> dsimp only [η,A] <;> ring
  exact le_shifted_exp_envelope _ A c η d q hc hη hA hraw

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
