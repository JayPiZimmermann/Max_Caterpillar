import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.ActualModel

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Check
open BigOperators DominantGap
attribute [local instance] Classical.propDecidable

/-- Exact conditional original-network mean at the original variable-arity
point, with the ambient rate expanded independently of its definition. -/
example {n h₁ h₂ : ℕ} (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (net : NormalizedNetwork n h₁ h₂)
    (hnorm : net.TranslationNormalized) (q K : ℕ) (T : ℝ) (r : Fin h₂)
    (hscale : 0<T ∧∀S : Finset (Fin n),∀a : Sampling.RawConfig S,
      GenericNetworkPoint net (Sampling.tail S) a T)
    (b : ℕ) (hn : 0<n) (hK : 0<(K:ℝ))
    (hm : ∀S∈D,2≤Sampling.tailCount S) (hcap : ∀S∈D,S.card≤b) :
    condMean p D (fun S=>
      ((actualNeuronEvent net hnorm q K T r S).card:ℝ)/Fintype.card (Sampling.RawConfig S)) ≤
      (p^2/(7*(K:ℝ)/(24*(n:ℝ)^2)))^q*
        Real.exp ((7*(K:ℝ)/(24*(n:ℝ)^2))*((b:ℝ)*((n:ℝ)-1))) :=
  actualNeuronMean_le p hp0 hp1 D hD hpos net hnorm q K T r hscale b hn hK hm hcap

/-- Literal event meaning: actual original inner vanishing and a genuine
q-edge matching on the selected ORIGINAL labels. -/
example {n h₁ h₂ : ℕ} (net : NormalizedNetwork n h₁ h₂)
    (hn : net.TranslationNormalized) (q K : ℕ) (T : ℝ) (r : Fin h₂)
    (S : Finset (Fin n)) (a : Sampling.RawConfig S) :
    a∈actualNeuronEvent net hn q K T r S ↔
      a.2∉MaxCaterpillar.Frontier.RandomRestriction.GoodEvent.badIsolatedEvent
        (Sampling.tailCount S) K ∧
      ActualClean net (Sampling.tail S) r a.2 K a.1 ∧
      net.inner r (actualGapPoint (Sampling.tail S) a T)=0 ∧
      ∃B∈matchings (braidInteractionGraph net hn r) q,matchingVertices B⊆S := by
  rw [mem_actualNeuronEvent]
  simp only [Sampling.actualPoint,mem_matchingSets]

/-- No conditioning-rarity factor occurs in the actual selected-matching
bound: downward conditioning reduces this increasing graph event. -/
example {n : ℕ} (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ) :
    condMean p D (fun S=>if S∈matchingSets G q then (1:ℝ) else 0) ≤
      (G.edgeFinset.card:ℝ)^q/(q.factorial:ℝ)*p^(2*q) :=
  condMean_matchingSets_le hp0 hp1 D hD hpos G q

/-- The q=0 endpoint genuinely selects every S, not an empty event. -/
example {n : ℕ} (p : ℝ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    mass p (matchingSets G 0)=1 := by
  have hzero : (∅ : Finset (Sym2 (Fin n)))∈matchings G 0 := by
    simp only [mem_matchings,Finset.empty_subset,Finset.card_empty,true_and]
    intro e he
    exact (Finset.not_mem_empty _ he).elim
  have hv : matchingVertices (∅ : Finset (Sym2 (Fin n)))=∅ := by
    simp [matchingVertices,GraphRestriction.pairVertices]
  have he : matchingSets G 0=Finset.univ := by
    ext S
    simp only [mem_matchingSets,Finset.mem_univ,iff_true]
    exact ⟨∅,hzero,by rw [hv];exact Finset.empty_subset _⟩
  rw [he,mass_univ]

#check @matchingSets
#check @actualNeuronEvent
#check @actualNeuronFraction
#check @actualNeuronMean
#check @actualNeuronMean_le
#print axioms mem_matchingSets
#print axioms matchingSets_upper
#print axioms mass_matchingSets_le_matchings
#print axioms mass_matchingSets_le
#print axioms condMean_matchingSets_le
#print axioms tail_edge_lower_bound
#print axioms subset_tail_mean_le_shifted
#print axioms selectedTailMean_le
#print axioms mem_actualNeuronEvent
#print axioms actualNeuronFraction_le_tailMean
#print axioms actualNeuronMean_le
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Check
