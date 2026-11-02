import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.ActualModel
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.Conditional
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.Semantics
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.SupportBounds
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Monotone
import MaxCaterpillar.Frontier.RandomRestriction.CountingUnion

/-! # Actual Bernoulli conditional transfer under the local structural H

Every selected set, raw tail/rank fiber and conditional weight is literal.
The common generic scale and all exceptional-event estimates are derived.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
open BigOperators DominantGap
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent (badIsolatedEvent)
attribute [local instance] Classical.propDecidable
variable {n k₀ q h₁ h₂ : ℕ}

noncomputable def shortRankEvent (S : Finset (Fin n)) (K : ℕ) :
    Finset (Sampling.RawConfig S) :=
  (Finset.univ : Finset (Equiv.Perm (Fin (Sampling.tailCount S)))) ×ˢ
    badIsolatedEvent (Sampling.tailCount S) K

@[simp] lemma mem_shortRankEvent (S : Finset (Fin n)) (K : ℕ) (a : Sampling.RawConfig S) :
    a∈shortRankEvent S K ↔ a.2∈badIsolatedEvent (Sampling.tailCount S) K := by
  simp only [shortRankEvent,Finset.mem_product,Finset.mem_univ,true_and]

noncomputable def shortRankFraction (S : Finset (Fin n)) (K : ℕ) : ℝ :=
  ((shortRankEvent S K).card : ℝ)/Fintype.card (Sampling.RawConfig S)

lemma shortRankFraction_eq (S : Finset (Fin n)) (K : ℕ) :
    shortRankFraction S K=((badIsolatedEvent (Sampling.tailCount S) K).card : ℝ)/
      Fintype.card (Equiv.Perm (Fin (Sampling.tailCount S))) := by
  unfold shortRankFraction shortRankEvent
  rw [Finset.card_product,Finset.card_univ]
  change ((Fintype.card (Equiv.Perm (Fin (Sampling.tailCount S)))*
      (badIsolatedEvent (Sampling.tailCount S) K).card : ℕ) : ℝ)/
      Fintype.card (Equiv.Perm (Fin (Sampling.tailCount S)) × Equiv.Perm (Fin (Sampling.tailCount S)))=_
  rw [Fintype.card_prod,Nat.cast_mul,Nat.cast_mul]
  apply mul_div_mul_left
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin (Sampling.tailCount S)))≠0)

lemma shortRankFraction_le (S : Finset (Fin n)) (K m₀ : ℕ)
    (hm₀ : 0<m₀) (hK : 4≤K) (hKm₀ : K<m₀) (htail : m₀≤Sampling.tailCount S) :
    shortRankFraction S K≤8*(K : ℝ)/(m₀ : ℝ) := by
  rw [shortRankFraction_eq]
  have hm : 0<Sampling.tailCount S := lt_of_lt_of_le hm₀ htail
  apply (MaxCaterpillar.Frontier.RandomRestriction.GoodEvent.badIsolatedEvent_fraction_le
    hm (hKm₀.le.trans htail) hK).trans
  apply div_le_div_of_le_left (by positivity)
  · exact_mod_cast hm₀
  · exact_mod_cast htail

lemma raw_cover_fraction {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] [Fintype ι] (B₁ B₂ : Finset Ω) (E : ι→Finset Ω)
    (hcover : Finset.univ⊆B₁∪B₂∪Finset.univ.biUnion E) :
    (1 : ℝ)≤(B₁.card : ℝ)/Fintype.card Ω+(B₂.card : ℝ)/Fintype.card Ω+
      ∑ i,((E i).card : ℝ)/Fintype.card Ω := by
  classical
  have hp : (0 : ℝ)<Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card Ω : ℝ)≤(B₁.card : ℝ)+(B₂.card : ℝ)+∑ i,((E i).card : ℝ) := by
    have he := CountingUnion.card_le_bad_add_event_sum B₁ B₂ ∅ E (by simpa only [Finset.union_empty] using hcover)
    simpa only [Finset.card_empty,add_zero,Nat.cast_add,Nat.cast_sum] using (show
      (Fintype.card Ω : ℝ)≤((B₁.card+B₂.card+(∅ : Finset Ω).card+∑ i,(E i).card : ℕ) : ℝ) from by exact_mod_cast he)
  calc
    _ = (Fintype.card Ω : ℝ)/Fintype.card Ω := (div_self hp.ne').symm
    _ ≤ ((B₁.card : ℝ)+(B₂.card : ℝ)+∑ i,((E i).card : ℝ))/Fintype.card Ω :=
      div_le_div_of_le hp.le hc
    _ = _ := by rw [add_div,add_div,Finset.sum_div]

theorem actual_raw_event_cover [NeZero n] [NeZero k₀]
    (H : LocalMatchingObstruction k₀ q) (hq : 0<q)
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum n x) (K : ℕ) (T : ℝ)
    (hscale : Sampling.CommonGapScale net T) (S : Finset (Fin n)) (hsize : k₀≤S.card)
    (hno : ∀ j,3≤(firstSupports net j).card → ¬firstSupports net j⊆S) :
    (Finset.univ : Finset (Sampling.RawConfig S))⊆shortRankEvent S K∪
      GoodEvent.familyBadConfigurations (firstSupports net) S K∪
      Finset.univ.biUnion (fun r=>actualNeuronEvent net hn q K T r S) := by
  classical
  letI : NeZero S.card := ⟨Nat.ne_of_gt
    (lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne k₀)) hsize)⟩
  have HS := localMatchingObstruction_mono_arity H hsize hq
  intro a _
  by_cases hQ : a∈shortRankEvent S K
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hQ)
  by_cases hG : a∈GoodEvent.familyBadConfigurations (firstSupports net) S K
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hG)
  have hcomp : Finset.univ.image (Sampling.tail S)=
      (Finset.univ : Finset (Fin n)) \ Finset.univ.image (Sampling.keep S) := by
    rw [Sampling.tail_image,Sampling.keep_image]
  have hno' : ∀ j,3≤(NormalizedNetwork.rowSupport (net.A j)).card →
      ¬NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image (Sampling.keep S) := by
    intro j hj
    rw [Sampling.keep_image]
    exact hno j hj
  obtain ⟨r,hzero,hmatch⟩ := structural_witness_of_generic_embedding HS hq net hn hnet
    (Sampling.keep S) (Sampling.tail S) a T hcomp (hscale.2 S a) hno'
  rw [Sampling.keep_image] at hmatch
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨r,Finset.mem_univ _,(mem_actualNeuronEvent net hn q K T r S a).mpr ?_⟩
  exact ⟨fun hh=>hQ ((mem_shortRankEvent S K a).mpr hh),
    GoodEvent.good_implies_actualClean net hn S K r a.1 a.2 hG,hzero,
    (mem_matchingSets (braidInteractionGraph net hn r) q S).mpr hmatch⟩

theorem one_le_actual_failure_sum [NeZero n] [NeZero k₀]
    (H : LocalMatchingObstruction k₀ q) (hq : 0<q)
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum n x) (K : ℕ) (T : ℝ)
    (hscale : Sampling.CommonGapScale net T) (S : Finset (Fin n))
    (hno : ∀ j,3≤(firstSupports net j).card → ¬firstSupports net j⊆S) :
    (1 : ℝ)≤(if S.card<k₀ then 1 else 0)+shortRankFraction S K+
      GoodEvent.familyBadFraction (firstSupports net) S K+
      ∑ r,actualNeuronFraction net hn q K T r S := by
  classical
  by_cases hs : S.card<k₀
  · rw [if_pos hs]
    have h₁ : 0≤shortRankFraction S K := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h₂ : 0≤GoodEvent.familyBadFraction (firstSupports net) S K :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h₃ : 0≤∑ r,actualNeuronFraction net hn q K T r S :=
      Finset.sum_nonneg (fun _ _=>div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    linarith only [h₁,h₂,h₃]
  · rw [if_neg hs,zero_add]
    exact raw_cover_fraction (shortRankEvent S K)
      (GoodEvent.familyBadConfigurations (firstSupports net) S K)
      (fun r=>actualNeuronEvent net hn q K T r S)
      (actual_raw_event_cover H hq net hn hnet K T hscale S (le_of_not_gt hs) hno)

/-- Finite conditional union on an actual downward selected-set event. Its
support-avoidance and tail-size hypotheses are deterministic set properties.
No generic scale or event probability estimate is assumed. -/
theorem conditional_union_bound [NeZero n] [NeZero k₀]
    (H : LocalMatchingObstruction k₀ q) (hq : 0<q)
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum n x)
    (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (b m₀ K : ℕ) (hm₀ : 4≤m₀) (hK : 4≤K) (hKm₀ : K<m₀)
    (htail : ∀ S∈D,m₀≤Sampling.tailCount S) (hcap : ∀ S∈D,S.card≤b)
    (hno : ∀ S∈D,∀ j,3≤(firstSupports net j).card → ¬firstSupports net j⊆S) :
    1-condMean p D (fun S=>if S.card<k₀ then 1 else 0)-8*(K : ℝ)/(m₀ : ℝ)-
      (∑ j,((firstSupports net j).card.descFactorial 4 : ℝ))*GoodEvent.badSupportRate p m₀ K ≤
      (h₂ : ℝ)*(p^2/ambientRate n K)^q*
        Real.exp (ambientRate n K*((b : ℝ)*((n : ℝ)-1))) := by
  classical
  obtain ⟨T,_hT,hscale⟩ := Sampling.exists_common_gap_threshold net
  have hs := hscale T le_rfl
  have hh := condMean_mono_on hp0 hp1 D hpos
    (fun S hS=>one_le_actual_failure_sum H hq net hn hnet K T hs S (hno S hS))
  rw [condMean_const D hpos 1] at hh
  simp only [condMean_add,condMean_sum] at hh
  have hshort : condMean p D (fun S=>shortRankFraction S K)≤8*(K : ℝ)/(m₀ : ℝ) := by
    apply condMean_le_const hp0 hp1 D hpos
    intro S hS
    exact shortRankFraction_le S K m₀ ((by decide : 0<4).trans_le hm₀) hK hKm₀ (htail S hS)
  have hgood := GoodEvent.conditional_familyBadFraction_le hp0 hp1 D hD hpos
    (firstSupports net) m₀ K hm₀ hKm₀ htail
  have hKpos : (0 : ℝ)<K := by exact_mod_cast lt_of_lt_of_le (by decide : 0<4) hK
  have hE : (∑ r,actualNeuronMean p D net hn q K T r)≤
      (h₂ : ℝ)*((p^2/ambientRate n K)^q*Real.exp (ambientRate n K*((b : ℝ)*((n : ℝ)-1)))) := by
    calc
      _ ≤ ∑ r : Fin h₂,(p^2/ambientRate n K)^q*
          Real.exp (ambientRate n K*((b : ℝ)*((n : ℝ)-1))) := by
        apply Finset.sum_le_sum
        intro r _
        exact actualNeuronMean_le p hp0 hp1 D hD hpos net hn q K T r hs b
          (Nat.pos_of_ne_zero (NeZero.ne n)) hKpos
          (fun S hS=>(by decide : 2≤4).trans (hm₀.trans (htail S hS))) hcap
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  change (1 : ℝ)≤condMean p D (fun S=>if S.card<k₀ then 1 else 0)+
    condMean p D (fun S=>shortRankFraction S K)+
    condMean p D (fun S=>GoodEvent.familyBadFraction (firstSupports net) S K)+
    ∑ r,actualNeuronMean p D net hn q K T r at hh
  nlinarith only [hh,hshort,hgood,hE]

/-- Canonical Bernoulli conditioning with no internal nonbraid support and
the literal floor size cap. Its mass, downward closure, common generic scale
and all failure probabilities are derived. The positive scalar denominator
is discharged by the later explicit parameter theorem. -/
theorem finite_conditional_bound [NeZero n] [NeZero k₀]
    (H : LocalMatchingObstruction k₀ q) (hq : 0<q)
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum n x)
    (p : ℝ) (hp0 : 0≤p) (hpHalf : p≤1/2) (K : ℕ)
    (hk₀ : (k₀ : ℝ)≤3*((n : ℝ)*p)/5)
    (hden : 0<Real.exp (-2*(largeSupports (firstSupports net)).card*p^3)-Real.exp (-((n : ℝ)*p)/3))
    (hm₀ : 4≤n-⌊2*((n : ℝ)*p)⌋₊) (hK : 4≤K) (hKm₀ : K<n-⌊2*((n : ℝ)*p)⌋₊) :
    1-Real.exp (-3*((n : ℝ)*p)/40)/
        (Real.exp (-2*(largeSupports (firstSupports net)).card*p^3)-Real.exp (-((n : ℝ)*p)/3))-
      8*(K : ℝ)/(n-⌊2*((n : ℝ)*p)⌋₊ : ℕ)-
      (∑ j,((firstSupports net j).card.descFactorial 4 : ℝ))*
        GoodEvent.badSupportRate p (n-⌊2*((n : ℝ)*p)⌋₊) K ≤
      (h₂ : ℝ)*(p^2/ambientRate n K)^q*
        Real.exp (ambientRate n K*((⌊2*((n : ℝ)*p)⌋₊ : ℝ)*((n : ℝ)-1))) := by
  classical
  let b : ℕ := ⌊2*((n : ℝ)*p)⌋₊
  let D := admissibleSets (firstSupports net) b
  have hp1 : p<1 := by linarith only [hpHalf]
  have hpos := mass_admissibleSets_pos hp0 hp1 (firstSupports net) b
  have htail : ∀ S∈D,n-b≤Sampling.tailCount S := by
    intro S hS
    have hc := ((mem_admissibleSets (firstSupports net) b S).mp hS).2
    change n-b≤((Finset.univ : Finset (Fin n)) \ S).card
    rw [DominantGap.complement_card]
    exact Nat.sub_le_sub_left hc n
  have hh := conditional_union_bound H hq net hn hnet p hp0 hp1.le D
    (isLowerSet_admissibleSets (firstSupports net) b) hpos b (n-b) K hm₀ hK hKm₀ htail
    (fun S hS=>((mem_admissibleSets (firstSupports net) b S).mp hS).2)
    (fun S hS=>((mem_admissibleSets (firstSupports net) b S).mp hS).1)
  have hsmall := condMean_admissibleSets_card_lt_le hp0 hpHalf (firstSupports net) k₀ hk₀ hden
  change condMean p D (fun S=>if S.card<k₀ then 1 else 0)≤_ at hsmall
  dsimp only [b] at hh
  linarith only [hh,hsmall]

#print axioms actual_raw_event_cover
#print axioms conditional_union_bound
#print axioms finite_conditional_bound

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
