import MaxCaterpillar.Frontier.RandomRestriction.FeedingCore
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.ConditionalBound

/-! Bernoulli counting charged only to original second-hidden neurons.
Output-only first neurons are absorbed as pure-linear outer slots. Their
positive-order matching events are empty, so they cost nothing in the union. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.FeedingBernoulli
open BigOperators
open Frontier.RandomRestriction
open GrowingMatching Bernoulli
open FeedingCore
attribute [local instance] Classical.propDecidable
variable {n k₀ q h₁ h₂ : ℕ}

theorem auxiliary_event_empty (net : NormalizedNetwork n h₁ h₂)
    (hn : net.TranslationNormalized) (hq : 0<q) (K : ℕ) (T : ℝ)
    (j : Fin h₁) (S : Finset (Fin n)) :
    actualNeuronEvent (absorb net) (absorb_normalized net hn) q K T (auxiliary j) S=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro a ha
  have hm := ((mem_actualNeuronEvent (absorb net) (absorb_normalized net hn)
    q K T (auxiliary j) S a).mp ha).2.2.2
  obtain ⟨B,hB,_⟩ := (mem_matchingSets _ q S).mp hm
  obtain ⟨hsub,hcard,_⟩ := (mem_matchings _ B).mp hB
  obtain ⟨e,he⟩ := Finset.card_pos.mp (hcard.symm ▸ hq)
  have hedge := hsub he
  induction e using Sym2.ind with
  | h u v =>
    have hadj : (braidInteractionGraph (absorb net) (absorb_normalized net hn)
      (auxiliary j)).Adj u v :=
      (SimpleGraph.mem_edgeSet _).mp (SimpleGraph.mem_edgeFinset.mp hedge)
    exact hadj.2 (absorb_auxiliary_edgeWeight net j u v)

theorem auxiliary_fraction_zero (net : NormalizedNetwork n h₁ h₂)
    (hn : net.TranslationNormalized) (hq : 0<q) (K : ℕ) (T : ℝ)
    (j : Fin h₁) (S : Finset (Fin n)) :
    actualNeuronFraction (absorb net) (absorb_normalized net hn) q K T (auxiliary j) S=0 := by
  simp only [actualNeuronFraction,auxiliary_event_empty net hn hq,Finset.card_empty,
    Nat.cast_zero,zero_div]

theorem auxiliary_mean_zero (p : ℝ) (D : Finset (Finset (Fin n)))
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (hq : 0<q) (K : ℕ) (T : ℝ) (j : Fin h₁) :
    actualNeuronMean p D (absorb net) (absorb_normalized net hn) q K T (auxiliary j)=0 := by
  unfold actualNeuronMean
  have he : actualNeuronFraction (absorb net) (absorb_normalized net hn)
      q K T (auxiliary j)=(fun _=>0) := by
    funext S
    exact auxiliary_fraction_zero net hn hq K T j S
  rw [he]
  simp [condMean]

theorem sum_actual_means_eq_original (p : ℝ) (D : Finset (Finset (Fin n)))
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (hq : 0<q) (K : ℕ) (T : ℝ) :
    (∑ r,actualNeuronMean p D (absorb net) (absorb_normalized net hn) q K T r)=
    ∑ r : Fin h₂,actualNeuronMean p D (absorb net) (absorb_normalized net hn)
      q K T (original r) := by
  calc
    _=∑ s : Fin h₂ ⊕ Fin h₁,
      actualNeuronMean p D (absorb net) (absorb_normalized net hn) q K T
        (outerEquiv h₂ h₁ s) :=
      (Fintype.sum_equiv (outerEquiv h₂ h₁) _ _ (fun _ => rfl)).symm
    _=_ := by
      rw [Fintype.sum_sum_type]
      change (∑ r : Fin h₂,_) + (∑ j : Fin h₁,
        actualNeuronMean p D (absorb net) (absorb_normalized net hn) q K T (auxiliary j))=_
      simp only [auxiliary_mean_zero p D net hn hq,Finset.sum_const_zero,add_zero]
      rfl

theorem conditional_union_bound [NeZero n] [NeZero k₀]
    (H : LocalMatchingObstruction k₀ q) (hq : 0<q)
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum n x)
    (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (b m₀ K : ℕ) (hm₀ : 4≤m₀) (hK : 4≤K) (hKm₀ : K<m₀)
    (htail : ∀ S∈D,m₀≤Sampling.tailCount S) (hcap : ∀ S∈D,S.card≤b)
    (hno : ∀ S∈D,∀ j,3≤(firstSupports (core net) j).card →
      ¬firstSupports (core net) j⊆S) :
    1-condMean p D (fun S=>if S.card<k₀ then 1 else 0)-8*(K : ℝ)/(m₀ : ℝ)-
      (∑ j,((firstSupports (core net) j).card.descFactorial 4 : ℝ))*
        GoodEvent.badSupportRate p m₀ K ≤
      (h₂ : ℝ)*(p^2/ambientRate n K)^q*
        Real.exp (ambientRate n K*((b : ℝ)*((n : ℝ)-1))) := by
  classical
  let model := absorb net
  have hnorm := absorb_normalized net hn
  have hmax : ∀ x,model.eval x=Maximum n x := by
    intro x
    rw [show model=absorb net from rfl,absorb_eval,hnet]
  obtain ⟨T,_hT,hscale⟩ := Sampling.exists_common_gap_threshold model
  have hs := hscale T le_rfl
  have hh := condMean_mono_on hp0 hp1 D hpos
    (fun S hS=>one_le_actual_failure_sum H hq model hnorm hmax K T hs S (hno S hS))
  rw [condMean_const D hpos 1] at hh
  simp only [condMean_add,condMean_sum] at hh
  have hshort : condMean p D (fun S=>shortRankFraction S K)≤8*(K : ℝ)/(m₀ : ℝ) := by
    apply condMean_le_const hp0 hp1 D hpos
    intro S hS
    exact shortRankFraction_le S K m₀ ((by decide : 0<4).trans_le hm₀) hK hKm₀ (htail S hS)
  have hgood := GoodEvent.conditional_familyBadFraction_le hp0 hp1 D hD hpos
    (firstSupports model) m₀ K hm₀ hKm₀ htail
  have hKpos : (0 : ℝ)<K := by exact_mod_cast lt_of_lt_of_le (by decide : 0<4) hK
  have hE : (∑ r,actualNeuronMean p D model hnorm q K T r)≤
      (h₂ : ℝ)*((p^2/ambientRate n K)^q*
        Real.exp (ambientRate n K*((b : ℝ)*((n : ℝ)-1)))) := by
    rw [show (∑ r,actualNeuronMean p D model hnorm q K T r)=
      ∑ r : Fin h₂,actualNeuronMean p D model hnorm q K T (original r) from
      sum_actual_means_eq_original p D net hn hq K T]
    calc
      _≤∑ r : Fin h₂,(p^2/ambientRate n K)^q*
          Real.exp (ambientRate n K*((b : ℝ)*((n : ℝ)-1))) := by
        apply Finset.sum_le_sum
        intro r _
        exact actualNeuronMean_le p hp0 hp1 D hD hpos model hnorm q K T (original r) hs b
          (Nat.pos_of_ne_zero (NeZero.ne n)) hKpos
          (fun S hS=>(by decide : 2≤4).trans (hm₀.trans (htail S hS))) hcap
      _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  change (1 : ℝ)≤condMean p D (fun S=>if S.card<k₀ then 1 else 0)+
    condMean p D (fun S=>shortRankFraction S K)+
    condMean p D (fun S=>GoodEvent.familyBadFraction (firstSupports model) S K)+
    ∑ r,actualNeuronMean p D model hnorm q K T r at hh
  have hsupports : firstSupports model=firstSupports (core net) := rfl
  rw [hsupports] at hh hgood
  nlinarith only [hh,hshort,hgood,hE]

#check @conditional_union_bound
#print axioms auxiliary_event_empty
#print axioms conditional_union_bound
end MaxCaterpillar.ExponentialPush.FeedingBernoulli
