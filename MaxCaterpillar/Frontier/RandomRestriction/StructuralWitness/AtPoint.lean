import MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness.Braid
import MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness.Graph
import MaxCaterpillar.Frontier.RandomRestriction.BraidModelLocalized

/-! From the actual local Max5 obstruction back to an original outer index and
its exact ambient signed interaction graph. No graph equality is assumed. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness
open BigOperators NormalizedNetwork MaxCaterpillar.Frontier.StarCertificate
variable {N h₁ h₂ : ℕ}

lemma localize_dead_outer (net : NormalizedNetwork N h₁ h₂) (q : Point N)
    (f : Fin 5 ↪ Fin N) (k : Fin h₂) (hk : net.inner k q≠0) :
    (net.localize q f).U k=0 ∧ (∀ j,(net.localize q f).W k j=0) ∧
      (net.localize q f).d k=0 := by
  classical
  refine ⟨?_,?_,?_⟩
  · change (if net.inner k q=0 then (net.localFirst q f).U k else 0)=0
    exact if_neg hk
  · intro j
    change (if net.inner k q=0 then _ else 0)=0
    exact if_neg hk
  · change (if net.inner k q=0 then net.d k else 0)=0
    exact if_neg hk

lemma local_support_le_two (net : NormalizedNetwork N h₁ h₂) (q : Point N)
    (f : Fin 5 ↪ Fin N)
    (hfirst : ∀ j,lin (net.A j) q=0 ↔ rowSupport (net.A j)⊆Finset.univ.image f)
    (hno : ∀ j,3≤(rowSupport (net.A j)).card → ¬rowSupport (net.A j)⊆Finset.univ.image f) :
    ∀ j,(rowSupport ((net.localize q f).A j)).card≤2 := by
  classical
  intro j
  rw [localize_first_row]
  by_cases hj : rowSupport (net.A j)⊆Finset.univ.image f
  · rw [if_pos ((hfirst j).mpr hj),card_rowSupport_restrict f (net.A j) hj]
    exact Nat.le_of_lt_succ (lt_of_not_ge (fun hlarge => hno j hlarge hj))
  · rw [if_neg (fun hz => hj ((hfirst j).mp hz)),rowSupport_zero,Finset.card_empty]
    exact Nat.zero_le _

/-- Helper at a specified actual point. The structured-point theorem supplies
every displayed localization hypothesis from its proved dominant-gap threshold. -/
theorem exists_original_outer_at_localization
    (hcoeff : ClosedStarCoefficientIdentity)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (q : Point N) (f : Fin 5 ↪ Fin N)
    (hfirst : ∀ j,lin (net.A j) q=0 ↔ rowSupport (net.A j)⊆Finset.univ.image f)
    (hlocnorm : (net.localize q f).TranslationNormalized)
    (hlocmax : ∀ x,(net.localize q f).eval x=Maximum 5 x)
    (hno : ∀ j,3≤(rowSupport (net.A j)).card → ¬rowSupport (net.A j)⊆Finset.univ.image f) :
    ∃ k : Fin h₂,net.inner k q=0 ∧
      HasTwoDisjointEdgesOn (braidInteractionGraph net hn k) (Finset.univ.image f) := by
  classical
  let model := net.localize q f
  have hs : ∀ j,(rowSupport (model.A j)).card≤2 := local_support_le_two net q f hfirst hno
  let pairs := BraidModel.rowPairs model hlocnorm hs
  obtain ⟨k,hnot⟩ := exists_inner_not_pairwiseIntersecting_of_coefficients
    hcoeff model hlocnorm hs hlocmax
  let G := quadraticInteractionGraph (BraidModel.innerQuadratic model pairs k)
  have htwo : HasTwoDisjointEdgesOn G Finset.univ :=
    (hasTwoDisjointEdgesOn_univ_iff G).mpr hnot
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hab,hcd,hac,had,hbc,hbd⟩ := htwo
  obtain ⟨j,hwj,_,_⟩ := BraidModel.inner_interaction_support model pairs k a b hab.2
  have hk : net.inner k q=0 := by
    by_contra hnz
    apply hwj
    change (if net.inner k q=0 then _ else 0)=0
    exact if_neg hnz
  refine ⟨k,hk,?_⟩
  have hgraph : G=(braidInteractionGraph net hn k).comap f := by
    apply SimpleGraph.ext
    funext u v
    exact propext (BraidModel.localize_interaction_graph_iff net q f hfirst k hk pairs u v)
  apply (hasTwoDisjointEdgesOn_comap_iff (braidInteractionGraph net hn k) f Finset.univ).mp
  rw [←hgraph]
  exact ⟨a,b,c,d,ha,hb,hc,hd,hab,hcd,hac,had,hbc,hbd⟩

#print axioms local_support_le_two
#print axioms exists_original_outer_at_localization
end MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness
