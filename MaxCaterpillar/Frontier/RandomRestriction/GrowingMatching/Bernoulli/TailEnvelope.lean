import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Matching
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.SamplingGeometry
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.Expectations
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.TailEnvelope
import MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction.Deletion

/-! # Actual variable-tail matching envelope after downward conditioning

The tail rate is weakened while its edge count is nonnegative. Only then is
the actual selected-vertex deletion estimate inserted. The increasing selected
matching event is dominated by its unconditioned Bernoulli count, so no
conditioning-rarity factor appears.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
open BigOperators
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
  (badIsolatedEvent rankIsolatedSlots rankIsolatedGaps)
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

noncomputable def ambientRate (n K : ℕ) : ℝ := 7*(K:ℝ)/(24*(n:ℝ)^2)

/-- The actual complement graph loses at most one full degree per selected
label, in the same original graph used by selected-matching counting. -/
theorem tail_edge_lower_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (hn : 1≤n) :
    (G.edgeFinset.card:ℝ)-(S.card:ℝ)*((n:ℝ)-1) ≤
      ((G.comap (Sampling.tail S)).edgeFinset.card:ℝ) := by
  have hh := GraphRestriction.edge_card_le_comap_add G S (Sampling.tail S)
    (Sampling.tail_range S)
  have hc : (G.edgeFinset.card:ℝ)≤
      ((G.comap (Sampling.tail S)).edgeFinset.card:ℝ)+(S.card:ℝ)*((n-1:ℕ):ℝ) := by
    exact_mod_cast hh
  rw [Nat.cast_sub hn,Nat.cast_one] at hc
  linarith only [hc]

/-- A uniform ambient rate is used BEFORE substituting the possibly negative
edge-deletion lower bound. This preserves the direction of both estimates. -/
theorem subset_tail_mean_le_shifted (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (K b : ℕ) (ρ : Equiv.Perm (Fin (Sampling.tailCount S)))
    (hn : 0<n) (hm : 2≤Sampling.tailCount S) (hK : 0<(K:ℝ))
    (hS : S.card≤b) (hQ : ρ∉badIsolatedEvent (Sampling.tailCount S) K) :
    lowRankMatchingMean (G.comap (Sampling.tail S)) ρ K ≤
      Real.exp (-(ambientRate n K*((G.edgeFinset.card:ℝ)-(b:ℝ)*((n:ℝ)-1)))) := by
  classical
  let m:=Sampling.tailCount S
  let H:=G.comap (Sampling.tail S)
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith only [hmR]
  have hm1 : (0:ℝ)<(m:ℝ)-1 := by linarith only [hmR]
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hmn : m≤n := by
    calc
      m≤m+Sampling.selectedCount S := Nat.le_add_right _ _
      _=n := Sampling.card_total S
  have hmnR : (m:ℝ)≤n := by exact_mod_cast hmn
  have hsq : (m:ℝ)^2≤(n:ℝ)^2 := by
    have hmul := mul_nonneg (sub_nonneg.mpr hmnR) (add_nonneg hnR.le hm0.le)
    nlinarith only [hmul]
  have hden : (m:ℝ)*((m:ℝ)-1)≤(n:ℝ)^2 := by nlinarith only [hsq,hm0]
  have hr : ambientRate n K≤tailRate m K := by
    unfold ambientRate tailRate
    apply div_le_div_of_le_left (by positivity)
      (show (0:ℝ)<24*(m:ℝ)*((m:ℝ)-1) by positivity)
    nlinarith only [hden]
  have hc : 0≤ambientRate n K := by unfold ambientRate;positivity
  have ht : (0:ℝ)≤H.edgeFinset.card := Nat.cast_nonneg _
  have hh := lowRankMatchingMean_le_shifted H ρ K (H.edgeFinset.card:ℝ) 0 hm hK hQ (by simp)
  have he : (G.edgeFinset.card:ℝ)-(b:ℝ)*((n:ℝ)-1)≤(H.edgeFinset.card:ℝ) := by
    have h0 := tail_edge_lower_bound G S (Nat.succ_le_iff.mpr hn)
    have hcard : (S.card:ℝ)≤b := by exact_mod_cast hS
    have hn1 : (0:ℝ)≤(n:ℝ)-1 := by
      have hh : (1:ℝ)≤n := by exact_mod_cast (Nat.succ_le_iff.mpr hn : 1≤n)
      linarith only [hh]
    have hb := mul_le_mul_of_nonneg_right hcard hn1
    dsimp only [H]
    linarith only [h0,hb]
  calc
    _ ≤ Real.exp (-(tailRate m K*(H.edgeFinset.card:ℝ))) := by simpa only [sub_zero] using hh
    _ ≤ Real.exp (-(ambientRate n K*(H.edgeFinset.card:ℝ))) := by
      apply Real.exp_le_exp.mpr
      have hmul:=mul_le_mul_of_nonneg_right hr ht
      linarith only [hmul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hmul:=mul_le_mul_of_nonneg_left he hc
      linarith only [hmul]

noncomputable def selectedTailMean (p : ℝ) (D : Finset (Finset (Fin n)))
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q K : ℕ) : ℝ :=
  condMean p D (fun S=>if S∈matchingSets G q then
    meanOver (fun ρ : Equiv.Perm (Fin (Sampling.tailCount S))=>
      if ρ∉badIsolatedEvent (Sampling.tailCount S) K then
        lowRankMatchingMean (G.comap (Sampling.tail S)) ρ K else 0)
    else 0)

/-- A genuine conditioned selected-set/tail moment estimate. The sole event
hypotheses describe an actual downward event and an ordinary size cap. -/
theorem selectedTailMean_le (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q K b : ℕ) (hn : 0<n) (hK : 0<(K:ℝ))
    (hm : ∀S∈D,2≤Sampling.tailCount S) (hcap : ∀S∈D,S.card≤b) :
    selectedTailMean p D G q K ≤
      (p^2/ambientRate n K)^q*Real.exp (ambientRate n K*((b:ℝ)*((n:ℝ)-1))) := by
  classical
  let η : ℝ:=G.edgeFinset.card
  let c:=ambientRate n K
  let d:ℝ:=(b:ℝ)*((n:ℝ)-1)
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hc : 0<c := by dsimp only [c,ambientRate];positivity
  have hbound : ∀S∈D,meanOver (fun ρ : Equiv.Perm (Fin (Sampling.tailCount S))=>
      if ρ∉badIsolatedEvent (Sampling.tailCount S) K then
        lowRankMatchingMean (G.comap (Sampling.tail S)) ρ K else 0) ≤Real.exp (-(c*(η-d))) := by
    intro S hS
    rw [←meanOver_const (Ω:=Equiv.Perm (Fin (Sampling.tailCount S))) (Real.exp (-(c*(η-d))))]
    apply meanOver_mono
    intro ρ
    by_cases hρ : ρ∉badIsolatedEvent (Sampling.tailCount S) K
    · rw [if_pos hρ]
      exact subset_tail_mean_le_shifted G S K b ρ hn (hm S hS) hK (hcap S hS) hρ
    · rw [if_neg hρ]
      exact (Real.exp_pos _).le
  have hstep : selectedTailMean p D G q K ≤
      Real.exp (-(c*(η-d)))*
        condMean p D (fun S=>if S∈matchingSets G q then (1:ℝ) else 0) := by
    rw [←condMean_const_mul]
    apply condMean_mono_on hp0 hp1 D hpos
    intro S hS
    by_cases hsel : S∈matchingSets G q
    · simp only [if_pos hsel,mul_one]
      exact hbound S hS
    · simp only [if_neg hsel,mul_zero,le_refl]
  have hraw : selectedTailMean p D G q K ≤
      p^(2*q)*η^q/(q.factorial:ℝ)*Real.exp (-(c*(η-d))) := by
    have hs:=condMean_matchingSets_le hp0 hp1 D hD hpos G q
    have ht:=mul_le_mul_of_nonneg_left hs (Real.exp_pos (-(c*(η-d)))).le
    apply hstep.trans
    convert ht using 1 <;> dsimp only [η] <;> ring
  have hfinal:=le_shifted_exp_envelope _ (p^(2*q)) c η d q hc (Nat.cast_nonneg _)
    (pow_nonneg hp0 _) hraw
  convert hfinal using 1 <;> dsimp only [c,d] <;> rw [div_pow,←pow_mul] <;> ring

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
