import research.sN.overnight_20261103.cycle_bridge.Equivalence
import MaxCaterpillar.Frontier.RandomRestriction.BraidModelInteraction
import MaxCaterpillar.Frontier.StarCertificate.SmallMatchingGraphStarFormula
import MaxCaterpillar.Frontier.StarCertificate.StarObstruction

/-! The actual H(5,2) obstruction from the star certificate and generic
cycle deletion. No triangle certificate, triangle normal form, or triangle
interleaving theorem enters this proof or its import closure.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.CycleBridge
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
open ForestMatching GrowingMatching
open MaxCaterpillar.Frontier.StarCertificate
attribute [local instance] Classical.propDecidable

theorem starContained_of_cover_one (G : SimpleGraph (Fin 5))
    (C : Finset (Fin 5)) (hC : IsVertexCover G C) (hcard : C.card ≤ 1) :
    StarContained G := by
  classical
  by_cases hc : C.Nonempty
  · obtain ⟨c,hc⟩ := hc
    refine ⟨c,?_⟩
    intro a b hab
    rcases hC a b hab with ha | hb
    · exact Or.inl ((Finset.card_le_one.mp hcard) a ha c hc)
    · exact Or.inr ((Finset.card_le_one.mp hcard) b hb c hc)
  · refine ⟨0,?_⟩
    intro a b hab
    rcases hC a b hab with ha | hb
    · exact False.elim (hc ⟨a,ha⟩)
    · exact False.elim (hc ⟨b,hb⟩)

/-- Every actual cover-one normalized braid network fails MAX_5. The only
coefficient certificate used is the already verified all-real star theorem. -/
theorem no_cover_one_maximum_five : ¬ CoverRepresentable 5 1 (Maximum 5) := by
  classical
  rintro ⟨h₁,h₂,net,hn,hs,hmax,hcover⟩
  let pairs := BraidModel.rowPairs net hn hs
  apply BraidModel.not_exact_maximum_of_permutation_certificate net hn hs ?_ hmax
  intro k
  obtain ⟨C,hC,hcard⟩ := hcover k
  obtain ⟨c,hstar⟩ := starContained_of_cover_one (braidInteractionGraph net hn k) C hC hcard
  have hquad : ∀ a b,
      (quadraticInteractionGraph (BraidModel.innerQuadratic net pairs k)).Adj a b →
      a=c ∨ b=c := by
    intro a b hab
    apply hstar a b
    refine ⟨hab.1,?_⟩
    rw [←BraidModel.inner_interaction_eq_braidEdgeWeight net pairs k a b hab.1]
    exact hab.2
  have heq : BraidModel.innerSetFunction net k =
      booleanQuadratic 0 (BraidModel.innerLinear net pairs k)
        (BraidModel.innerQuadratic net pairs k) :=
    funext (BraidModel.inner_boolean_quadratic net pairs k)
  have hrepr := booleanQuadratic_eq_starAt_of_interaction_star 0
    (BraidModel.innerLinear net pairs k) (BraidModel.innerQuadratic net pairs k) c hquad
    (by rw [←heq]; exact BraidModel.innerSetFunction_empty net k)
    (by rw [←heq]; exact BraidModel.innerSetFunction_full net hn k)
  rw [heq,hrepr]
  exact starAt_permutation_sum_eq_zero _ _ _

/-- A second proof of H(5,2), using the same-arity matching/cover equivalence
and only the star coefficient certificate. No width-preservation is claimed
for the intermediate cycle expansion. -/
theorem localMatchingObstruction_five_two_via_cycle_deletion :
    LocalMatchingObstruction 5 2 :=
  (localMatchingObstruction_iff_no_cover_representation 5 1).mpr
    no_cover_one_maximum_five

#check @no_cover_one_maximum_five
#check @localMatchingObstruction_five_two_via_cycle_deletion
#print axioms no_cover_one_maximum_five
#print axioms localMatchingObstruction_five_two_via_cycle_deletion
end MaxCaterpillar.ExponentialPush.CycleBridge
