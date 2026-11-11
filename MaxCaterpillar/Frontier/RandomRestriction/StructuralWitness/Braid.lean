import MaxCaterpillar.Frontier.RandomRestriction.BraidModel
import MaxCaterpillar.Frontier.StarCertificate.TriangleRelabel

/-! Actual normalized Max5 braid models force an inner interaction matching.
The sole certificate premise is the explicitly displayed real closed-star
coefficient identity. All Boolean and chamber bridges are derived from the
actual network arrays, without assumed normal forms or genericity. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness
open BigOperators MaxCaterpillar.Frontier.StarCertificate

/-- The remaining finite closed-star coefficient identity, kept explicit until
its independent certificate theorem is supplied. -/
def ClosedStarCoefficientIdentity : Prop :=
  ∀ (p : Fin 4 → ℝ) (t : Fin 80),
    evalForm (starAnovaCoefficients (actualSigns subsetForms p) t) p=0

variable {h₁ h₂ : ℕ}

/-- Every exact normalized actual five-input braid model has an original outer
index whose actual quadratic interaction graph has two disjoint edges. -/
theorem exists_inner_not_pairwiseIntersecting_of_coefficients
    (hcoeff : ClosedStarCoefficientIdentity)
    (model : NormalizedNetwork 5 h₁ h₂)
    (hn : model.TranslationNormalized)
    (hs : ∀ j,(NormalizedNetwork.rowSupport (model.A j)).card≤2)
    (hmax : ∀ x,model.eval x=Maximum 5 x) :
    ∃ k : Fin h₂,¬PairwiseIntersectingEdges
      (quadraticInteractionGraph (BraidModel.innerQuadratic model (BraidModel.rowPairs model hn hs) k)) := by
  classical
  let pairs := BraidModel.rowPairs model hn hs
  by_contra hnexist
  have hall : ∀ k,PairwiseIntersectingEdges
      (quadraticInteractionGraph (BraidModel.innerQuadratic model pairs k)) := by
    intro k
    by_contra hk
    exact hnexist ⟨k,hk⟩
  apply BraidModel.not_exact_maximum_of_permutation_certificate model hn hs ?_ hmax
  intro k
  have heq : BraidModel.innerSetFunction model k=
      booleanQuadratic 0 (BraidModel.innerLinear model pairs k)
        (BraidModel.innerQuadratic model pairs k) :=
    funext (BraidModel.inner_boolean_quadratic model pairs k)
  have hc := TriangleRelabel.small_matching_starXi_of_coefficients hcoeff 0
    (BraidModel.innerLinear model pairs k) (BraidModel.innerQuadratic model pairs k) (hall k)
    (by rw [← heq]; exact BraidModel.innerSetFunction_empty model k)
    (by rw [← heq]; exact BraidModel.innerSetFunction_full model hn k)
  simpa only [← heq] using hc

#print axioms exists_inner_not_pairwiseIntersecting_of_coefficients
end MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness
