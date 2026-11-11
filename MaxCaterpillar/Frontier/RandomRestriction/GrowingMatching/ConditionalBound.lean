import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventModel
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Structural
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BadFirstConfigurations
import MaxCaterpillar.Frontier.RandomRestriction.CountingUnion

/-! # The actual finite growing-matching transfer, conditional only on H(k,q)

The structural hypothesis concerns actual finite MAX_k networks. No generic
point, event cover, survival estimate or probability bound is a premise of
the final transfer theorem. Growing levels of H remain explicit assumptions.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
open BigOperators Configurations DominantGap
attribute [local instance] Classical.propDecidable
variable {k m q h₁ h₂ : ℕ}

local instance totalNeZero [NeZero k] : NeZero (m+k) :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne k)) (Nat.le_add_left k m))⟩

noncomputable def shortRankEvent (k m K : ℕ) : Finset (Configuration k m) :=
  pullbackEvent ((Finset.univ : Finset (FullPerm k m)) ×ˢ (GoodEvent.badIsolatedEvent m K))

@[simp] lemma mem_shortRankEvent (k m K : ℕ) (ω : Configuration k m) :
    ω∈shortRankEvent k m K ↔ ω.2.2∈GoodEvent.badIsolatedEvent m K := by
  classical
  simp only [shortRankEvent,mem_pullbackEvent,Finset.mem_product,Finset.mem_univ,true_and,
    effectiveConfiguration]

lemma shortRankEvent_fraction (k m K : ℕ) :
    ((shortRankEvent k m K).card : ℝ)/Fintype.card (Configuration k m)=
      ((GoodEvent.badIsolatedEvent m K).card : ℝ)/Fintype.card (RankPerm m) := by
  rw [shortRankEvent,pullbackEvent_fraction,Finset.card_product,Finset.card_univ,
    Fintype.card_prod,Nat.cast_mul,Nat.cast_mul]
  apply mul_div_mul_left
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card (FullPerm k m)≠0)

lemma shortRankEvent_fraction_le (k K : ℕ) (hm : 0<m) (hKm : K≤m) (hK : 4≤K) :
    ((shortRankEvent k m K).card : ℝ)/Fintype.card (Configuration k m)≤8*(K : ℝ)/(m : ℝ) := by
  rw [shortRankEvent_fraction]
  exact GoodEvent.badIsolatedEvent_fraction_le hm hKm hK

theorem actual_event_cover [NeZero k]
    (H : LocalMatchingObstruction k q) (hq : 0<q)
    (net : NormalizedNetwork (m+k) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum (m+k) x)
    (K : ℕ) (T : ℝ) (hscale : CommonGapScale net T) :
    (Finset.univ : Finset (Configuration k m))⊆
      BadFirst.configurationBadFirstEvent k m (firstSupports net) ∪ shortRankEvent k m K ∪
      feedingBadConfigurationsThree k (firstSupports net) K ∪
      Finset.univ.biUnion (actualNeuronEvent net hn q K T) := by
  classical
  intro ω _
  by_cases h₁ : ω∈BadFirst.configurationBadFirstEvent k m (firstSupports net)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h₁))
  by_cases h₂ : ω∈shortRankEvent k m K
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h₂))
  by_cases h₃ : ω∈feedingBadConfigurationsThree k (firstSupports net) K
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ h₃)
  have hno : ∀ j,3≤(NormalizedNetwork.rowSupport (net.A j)).card →
      ¬NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image (selectedEmbedding ω.1) := by
    intro j hj hs
    rw [selectedEmbedding_image] at hs
    exact h₁ ((BadFirst.mem_configurationBadFirstEvent k m (firstSupports net) ω).mpr ⟨j,hj,hs⟩)
  have hcomp : Finset.univ.image (baseTail ω.1)=
      (Finset.univ : Finset (Fin (m+k))) \ Finset.univ.image (selectedEmbedding ω.1) := by
    rw [selectedEmbedding_image]
    exact baseTail_image_complement_selectedLabels ω.1
  obtain ⟨r,hzero,hselected⟩ := selected_event_witness_of_generic_embedding H hq net hn hnet
    (selectedEmbedding ω.1) (baseTail ω.1) ω.2 T hcomp
    (hscale.2 ω.1 ω.2.1 ω.2.2) ω.1 (selectedEmbedding_image ω.1) hno
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨r,Finset.mem_univ _,(mem_actualNeuronEvent net hn q K T r ω).mpr ?_⟩
  exact ⟨fun h => h₂ ((mem_shortRankEvent k m K ω).mpr h),
    good_implies_actualClean net hn K r ω.1 ω.2.1 ω.2.2 h₃,hzero,
    (mem_selectedEvent (braidInteractionGraph net hn r) ω.1).mpr hselected⟩

lemma finite_union_fraction_bound {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] [Fintype ι]
    (B₁ B₂ B₃ : Finset Ω) (E : ι→Finset Ω) (b₁ b₂ b₃ C : ℝ)
    (hcover : Finset.univ⊆B₁∪B₂∪B₃∪Finset.univ.biUnion E)
    (hB₁ : (B₁.card : ℝ)/Fintype.card Ω≤b₁)
    (hB₂ : (B₂.card : ℝ)/Fintype.card Ω≤b₂)
    (hB₃ : (B₃.card : ℝ)/Fintype.card Ω≤b₃)
    (hE : ∀ i,((E i).card : ℝ)/Fintype.card Ω≤C) :
    1-b₁-b₂-b₃≤(Fintype.card ι : ℝ)*C := by
  classical
  have hp : (0 : ℝ)<Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card Ω : ℝ)≤(B₁.card : ℝ)+(B₂.card : ℝ)+(B₃.card : ℝ)+
      ∑ i,((E i).card : ℝ) := by
    exact_mod_cast CountingUnion.card_le_bad_add_event_sum B₁ B₂ B₃ E hcover
  have hh : (1 : ℝ)≤(B₁.card : ℝ)/Fintype.card Ω+(B₂.card : ℝ)/Fintype.card Ω+
      (B₃.card : ℝ)/Fintype.card Ω+∑ i,((E i).card : ℝ)/Fintype.card Ω := by
    calc
      _ = (Fintype.card Ω : ℝ)/Fintype.card Ω := (div_self hp.ne').symm
      _ ≤ ((B₁.card : ℝ)+(B₂.card : ℝ)+(B₃.card : ℝ)+∑ i,((E i).card : ℝ))/Fintype.card Ω :=
        div_le_div_of_le hp.le hc
      _ = _ := by rw [add_div,add_div,add_div,Finset.sum_div]
  have hs : (∑ i,((E i).card : ℝ)/Fintype.card Ω)≤(Fintype.card ι : ℝ)*C := by
    calc
      _ ≤ ∑ i : ι,C := Finset.sum_le_sum (fun i _=>hE i)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  linarith only [hh,hB₁,hB₂,hB₃,hs]

/-- The finite actual-model inequality (T). The only unproved ingredient is
the displayed local structural hypothesis H(k,q). All event/rank/survival
and probability conclusions are derived from the actual network arrays. -/
theorem conditional_finite_transfer [NeZero k]
    (H : LocalMatchingObstruction k q) (hq : 0<q)
    (net : NormalizedNetwork (m+k) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum (m+k) x)
    (K : ℕ) (hm : 2≤m) (htotal : 4≤m+k) (hK : 4≤K) (hKm : K<m) :
    1-8*(K : ℝ)/(m : ℝ)-
      (BadFirst.largeSupportCount (firstSupports net) : ℝ)*(k.descFactorial 3 : ℝ)/((m+k).descFactorial 3 : ℝ)-
      (∑ j,((firstSupports net j).card.descFactorial 4 : ℝ))/((m+k).descFactorial 4 : ℝ)*
        ((K : ℝ)^2*(1+(k : ℝ)/(m : ℝ))/(1-(K : ℝ)/(m : ℝ))+
          (k.descFactorial 2 : ℝ)*(K : ℝ)/2) ≤
      (h₂ : ℝ)*((k.descFactorial (2*q) : ℝ)/((m+k).descFactorial (2*q) : ℝ))*
        ((tailRate m K)^q)⁻¹*Real.exp (tailRate m K*((k : ℝ)*((m : ℝ)+(k : ℝ)-1))) := by
  classical
  obtain ⟨T,_hT,hscale⟩ := exists_common_gap_threshold net
  have hs := hscale T le_rfl
  have hmpos : 0<m := lt_of_lt_of_le (by decide : 0<2) hm
  have hKpos : (0 : ℝ)<K := by exact_mod_cast lt_of_lt_of_le (by decide : 0<4) hK
  have hh := finite_union_fraction_bound
    (BadFirst.configurationBadFirstEvent k m (firstSupports net)) (shortRankEvent k m K)
    (feedingBadConfigurationsThree k (firstSupports net) K) (actualNeuronEvent net hn q K T)
    _ _ _ _ (actual_event_cover H hq net hn hnet K T hs)
    (BadFirst.configurationBadFirstEvent_fraction_le k m ((by decide : 3≤4).trans htotal) (firstSupports net))
    (shortRankEvent_fraction_le k K hmpos hKm.le hK)
    ((le_of_eq (feedingBadConfigurationsThree_fraction k (firstSupports net) K)).trans
      (GoodEvent.feedingBadFraction_le k (firstSupports net) K hmpos hKm htotal))
    (fun r => actualNeuron_fraction_le net hn q K T r hs hm hKpos)
  simp only [Fintype.card_fin] at hh
  convert hh using 1 <;> ring

#print axioms actual_event_cover
#print axioms conditional_finite_transfer
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
