import MaxCaterpillar.Frontier.RandomRestriction.FeedingCore

/-! The five-input obstruction needs braid support only for feeding rows.
Arbitrary output-only first neurons are absorbed into empty-graph outer slots. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.FeedingCore
open BigOperators NormalizedNetwork MaxCaterpillar.Frontier.StarCertificate
variable {h₁ h₂ : ℕ}

lemma quadraticGraph_eq_braidGraph (net : NormalizedNetwork 5 h₁ h₂)
    (hn : net.TranslationNormalized) (pairs : ∀ j,BraidModel.BraidPair (net.A j))
    (k : Fin h₂) :
    quadraticInteractionGraph (BraidModel.innerQuadratic net pairs k)=braidInteractionGraph net hn k := by
  apply SimpleGraph.ext
  funext a b
  apply propext
  by_cases hab : a=b
  · subst b
    simp only [SimpleGraph.irrefl,iff_self]
  · change (a≠b ∧ effectiveInteraction (BraidModel.innerQuadratic net pairs k) a b≠0) ↔
      (a≠b ∧ braidEdgeWeight net.A (net.W k) a b≠0)
    rw [BraidModel.inner_interaction_eq_braidEdgeWeight net pairs k a b hab]

/-- Actual normalized MAX5 networks may contain arbitrarily many nonbraid
output-only first neurons. Some original outer neuron still has two disjoint
interaction edges; auxiliary absorbed output slots are explicitly excluded. -/
theorem exists_original_matching_of_feeding_braid
    (net : NormalizedNetwork 5 h₁ h₂) (hn : net.TranslationNormalized)
    (hs : ∀ j,net.Feeding j → (rowSupport (net.A j)).card≤2)
    (hmax : ∀ x,net.eval x=Maximum 5 x) :
    ∃ k : Fin h₂,HasTwoDisjointEdgesOn (braidInteractionGraph net hn k) Finset.univ := by
  classical
  have hnorm := absorb_normalized net hn
  have hsupport := absorb_support_le_two net hs
  have htarget : ∀ x,(absorb net).eval x=Maximum 5 x :=
    fun x => (absorb_eval net x).trans (hmax x)
  obtain ⟨s,hs⟩ := StructuralWitness.exists_inner_not_pairwiseIntersecting_of_coefficients
    starAnova_all_real (absorb net) hnorm hsupport htarget
  have htwo : HasTwoDisjointEdgesOn (braidInteractionGraph (absorb net) hnorm s) Finset.univ := by
    rw [←quadraticGraph_eq_braidGraph (absorb net) hnorm
      (BraidModel.rowPairs (absorb net) hnorm hsupport) s]
    exact (hasTwoDisjointEdgesOn_univ_iff _).mpr hs
  obtain ⟨tag,rfl⟩ := (outerEquiv h₂ h₁).surjective s
  rcases tag with k|j
  · refine ⟨k,?_⟩
    have hg : braidInteractionGraph (absorb net) hnorm (original k)=braidInteractionGraph net hn k := by
      apply SimpleGraph.ext
      funext a b
      apply propext
      change (a≠b ∧ braidEdgeWeight (absorb net).A ((absorb net).W (original k)) a b≠0) ↔ _
      rw [absorb_original_edgeWeight]
      rfl
    exact hg ▸ htwo
  · obtain ⟨a,b,c,d,_ha,_hb,_hc,_hd,hab,_hcd,_hac,_had,_hbc,_hbd⟩ := htwo
    change a≠b ∧ braidEdgeWeight (absorb net).A ((absorb net).W (auxiliary j)) a b≠0 at hab
    exact False.elim (hab.2 (absorb_auxiliary_edgeWeight net j a b))

#print axioms exists_original_matching_of_feeding_braid

section Localization
variable {N m h₁ h₂ : ℕ}

lemma local_feeding_support_le_two (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (f : Fin 5 ↪ Fin N)
    (hfirst : ∀ j,lin (net.A j) q=0 ↔ rowSupport (net.A j)⊆Finset.univ.image f)
    (hno : ∀ j,net.Feeding j → 3≤(rowSupport (net.A j)).card →
      ¬rowSupport (net.A j)⊆Finset.univ.image f) :
    ∀ j,(net.localize q f).Feeding j → (rowSupport ((net.localize q f).A j)).card≤2 := by
  classical
  intro j hj
  have horiginal := net.localize_feeding_original q f j hj
  rw [localize_first_row]
  by_cases hs : rowSupport (net.A j)⊆Finset.univ.image f
  · rw [if_pos ((hfirst j).mpr hs),card_rowSupport_restrict f (net.A j) hs]
    exact Nat.le_of_lt_succ (lt_of_not_ge (fun hlarge => hno j horiginal hlarge hs))
  · rw [if_neg (fun hz => hs ((hfirst j).mp hz)),rowSupport_zero,Finset.card_empty]
    exact Nat.zero_le _

theorem exists_original_outer_at_localization_feeding
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (q : Point N) (f : Fin 5 ↪ Fin N)
    (hfirst : ∀ j,lin (net.A j) q=0 ↔ rowSupport (net.A j)⊆Finset.univ.image f)
    (hlocnorm : (net.localize q f).TranslationNormalized)
    (hlocmax : ∀ x,(net.localize q f).eval x=Maximum 5 x)
    (hno : ∀ j,net.Feeding j → 3≤(rowSupport (net.A j)).card →
      ¬rowSupport (net.A j)⊆Finset.univ.image f) :
    ∃ k : Fin h₂,net.inner k q=0 ∧
      HasTwoDisjointEdgesOn (braidInteractionGraph net hn k) (Finset.univ.image f) := by
  classical
  obtain ⟨k,htwo⟩ := exists_original_matching_of_feeding_braid (net.localize q f)
    hlocnorm (local_feeding_support_le_two net q f hfirst hno) hlocmax
  have hk : net.inner k q=0 := by
    by_contra hne
    have hdead := StructuralWitness.localize_dead_outer net q f k hne
    obtain ⟨a,b,c,d,_ha,_hb,_hc,_hd,hab,_hcd,_hac,_had,_hbc,_hbd⟩ := htwo
    have hz : braidEdgeWeight (net.localize q f).A ((net.localize q f).W k) a b=0 := by
      simp only [braidEdgeWeight,hdead.2.1,zero_mul,Finset.sum_const_zero,neg_zero]
    exact hab.2 hz
  refine ⟨k,hk,?_⟩
  have hg : braidInteractionGraph (net.localize q f) hlocnorm k=
      (braidInteractionGraph net hn k).comap f := by
    apply SimpleGraph.ext
    funext a b
    apply propext
    change (a≠b ∧ braidEdgeWeight (net.localize q f).A ((net.localize q f).W k) a b≠0) ↔
      (f a≠f b ∧ braidEdgeWeight net.A (net.W k) (f a) (f b)≠0)
    rw [BraidModel.localize_braidEdgeWeight_eq_ambient net q f hfirst k hk a b]
    constructor
    · exact fun h => ⟨f.injective.ne h.1,h.2⟩
    · exact fun h => ⟨fun he => h.1 (congrArg f he),h.2⟩
  rw [hg] at htwo
  exact (hasTwoDisjointEdgesOn_comap_iff (braidInteractionGraph net hn k) f Finset.univ).mp htwo

open DominantGap Cartesian

/-- The actual original-coordinate witness at the same generic point used by
the counting experiment, with large-support exclusion only for feeding rows. -/
theorem structural_witness_of_generic_embedding_feeding [NeZero N]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x)
    (f : Fin 5 ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T)
    (hno : ∀ j,net.Feeding j → 3≤(rowSupport (net.A j)).card →
      ¬rowSupport (net.A j)⊆Finset.univ.image f) :
    ∃ k : Fin h₂,net.inner k (actualGapPoint e p T)=0 ∧
      HasTwoDisjointEdgesOn (braidInteractionGraph net hn k) (Finset.univ.image f) :=
  exists_original_outer_at_localization_feeding net hn (actualGapPoint e p T) f
    (embedded_first_zero_iff_support net f e p T hcomp h)
    (embeddedLocalizedModel_translation_normalized net hn hnet f e p T hcomp h)
    (embeddedLocalizedModel_computes_max net hnet f e p T hcomp h) hno

#print axioms exists_original_outer_at_localization_feeding
#print axioms structural_witness_of_generic_embedding_feeding
end Localization
end MaxCaterpillar.Frontier.RandomRestriction.FeedingCore
