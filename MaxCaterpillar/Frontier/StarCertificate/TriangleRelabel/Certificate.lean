import MaxCaterpillar.Frontier.StarCertificate.TriangleRelabel.Representation
import MaxCaterpillar.Frontier.StarCertificate.TriangleInterleavingsStars
import MaxCaterpillar.Frontier.StarCertificate.SmallMatchingGraphStarFormula

/-! # Transfer the actual native certificate through the structural triangle bridge

Relabeling invariance is applied to the actual 120 permutation chains. The
native triangle theorem then uses its proved six-by-twenty interleaving
identity. The source polynomial has arbitrary real ordered coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.StarCertificate.TriangleRelabel
open BigOperators TriangleInterleavings

/-- An arbitrary all-orderings functional that vanishes on every actual native
star also vanishes on every normalized actual interaction triangle. -/
theorem triangle_permutation_sum_zero_of_stars (Xi : (Fin 4 → ℝ) → ℝ)
    (hstar : ∀ (c : Fin 5) (v v' : Fin 5 → ℝ),
      (∑ pi : Equiv.Perm (Fin 5),Xi (permutationFunctionChain (starAtSetFunction c v v') pi))=0)
    (a : ℝ) (b : Fin 5 → ℝ) (d : Fin 5 → Fin 5 → ℝ)
    (htriangle : TriangleContained (quadraticInteractionGraph d))
    (hEmpty : booleanQuadratic a b d ∅=0)
    (hFull : booleanQuadratic a b d Finset.univ=0) :
    (∑ pi : Equiv.Perm (Fin 5),Xi (permutationFunctionChain (booleanQuadratic a b d) pi))=0 := by
  obtain ⟨e,A,B,C,x,y,z,u,v,hrep,htotal⟩ :=
    booleanQuadratic_triangle_relabel a b d htriangle hEmpty hFull
  rw [← permutation_relabel_sum (booleanQuadratic a b d) e.symm Xi,hrep]
  exact native_triangle_sum_zero_of_stars Xi hstar A B C x y z u v htotal

/-- The unrestricted actual small-matching model has no remaining triangle
normal-form premise. Its graph obstruction chooses the star or triangle branch. -/
theorem small_matching_permutation_sum_zero_of_stars (Xi : (Fin 4 → ℝ) → ℝ)
    (hstar : ∀ (c : Fin 5) (v v' : Fin 5 → ℝ),
      (∑ pi : Equiv.Perm (Fin 5),Xi (permutationFunctionChain (starAtSetFunction c v v') pi))=0)
    (a : ℝ) (b : Fin 5 → ℝ) (d : Fin 5 → Fin 5 → ℝ)
    (H : PairwiseIntersectingEdges (quadraticInteractionGraph d))
    (hEmpty : booleanQuadratic a b d ∅=0)
    (hFull : booleanQuadratic a b d Finset.univ=0) :
    (∑ pi : Equiv.Perm (Fin 5),Xi (permutationFunctionChain (booleanQuadratic a b d) pi))=0 := by
  rcases booleanQuadratic_native_star_or_triangle a b d H hEmpty hFull with
    ⟨c,hG⟩ | htriangle
  · rw [hG]
    exact hstar _ _ _
  · exact triangle_permutation_sum_zero_of_stars Xi hstar a b d htriangle hEmpty hFull

/-- The explicit finite coefficient certificate now covers every actual
normalized real quadratic satisfying the small-matching graph condition. -/
theorem small_matching_starXi_of_coefficients
    (hcoeff : ∀ (p : Fin 4 → ℝ) (t : Fin 80),
      evalForm (starAnovaCoefficients (actualSigns subsetForms p) t) p=0)
    (a : ℝ) (b : Fin 5 → ℝ) (d : Fin 5 → Fin 5 → ℝ)
    (H : PairwiseIntersectingEdges (quadraticInteractionGraph d))
    (hEmpty : booleanQuadratic a b d ∅=0)
    (hFull : booleanQuadratic a b d Finset.univ=0) :
    (∑ pi : Equiv.Perm (Fin 5),starXi (permutationFunctionChain (booleanQuadratic a b d) pi))=0 :=
  small_matching_permutation_sum_zero_of_stars starXi
    (starAt_permutation_sum_of_coefficients hcoeff) a b d H hEmpty hFull

end MaxCaterpillar.Frontier.StarCertificate.TriangleRelabel
