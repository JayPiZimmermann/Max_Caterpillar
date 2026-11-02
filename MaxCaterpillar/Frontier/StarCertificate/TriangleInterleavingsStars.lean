import MaxCaterpillar.Frontier.StarCertificate.TriangleInterleavingsNative
import MaxCaterpillar.Frontier.StarCertificate.StarCenters

/-!
# From actual star vanishing to actual triangle vanishing

Every zero-edge native triangle is identified with a primitive arbitrary-centre
star, using the total-zero relation. The six-order/interleaving theorem then
extends the star identity to all triangles, with no regularity assumption on Xi.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace MaxCaterpillar.Frontier.StarCertificate.TriangleInterleavings
open BigOperators

private lemma vec5_three (a b c d e : ℝ) :
    (![a,b,c,d,e] : Fin 5 → ℝ) 3=d := rfl

private lemma vec5_four (a b c d e : ℝ) :
    (![a,b,c,d,e] : Fin 5 → ℝ) 4=e := rfl

/-- A triangle without its 12 edge is literally a star centred at 0. -/
theorem native_zero12_eq_star (A B C x y u v : ℝ)
    (htotal : A+B+C+x+y+u+v=0) :
    nativeTriangle ![A,B,C,x,y,0,u,v] =
      starAtSetFunction 0 ![0,B,C,u,v] ![0,B+x,C+y,u,v] := by
  funext S
  rw [nativeTriangle_formula]
  unfold starAtSetFunction
  simp only [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin 5)),
    Fin.sum_univ_five]
  by_cases h0 : (0 : Fin 5) ∈ S <;>
  by_cases h1 : (1 : Fin 5) ∈ S <;>
  by_cases h2 : (2 : Fin 5) ∈ S <;>
  by_cases h3 : (3 : Fin 5) ∈ S <;>
  by_cases h4 : (4 : Fin 5) ∈ S <;>
  simp [coordinate,vec5_three,vec5_four,h0,h1,h2,h3,h4] <;>
  linarith only [htotal]

/-- A triangle without its 02 edge is literally a star centred at 1. -/
theorem native_zero02_eq_star (A B C x z u v : ℝ)
    (htotal : A+B+C+x+z+u+v=0) :
    nativeTriangle ![A,B,C,x,0,z,u,v] =
      starAtSetFunction 1 ![A,0,C,u,v] ![A+x,0,C+z,u,v] := by
  funext S
  rw [nativeTriangle_formula]
  unfold starAtSetFunction
  simp only [Finset.sum_erase_eq_sub (Finset.mem_univ (1 : Fin 5)),
    Fin.sum_univ_five]
  by_cases h0 : (0 : Fin 5) ∈ S <;>
  by_cases h1 : (1 : Fin 5) ∈ S <;>
  by_cases h2 : (2 : Fin 5) ∈ S <;>
  by_cases h3 : (3 : Fin 5) ∈ S <;>
  by_cases h4 : (4 : Fin 5) ∈ S <;>
  simp [coordinate,vec5_three,vec5_four,h0,h1,h2,h3,h4] <;>
  linarith only [htotal]

/-- A triangle without its 01 edge is literally a star centred at 2. -/
theorem native_zero01_eq_star (A B C y z u v : ℝ)
    (htotal : A+B+C+y+z+u+v=0) :
    nativeTriangle ![A,B,C,0,y,z,u,v] =
      starAtSetFunction 2 ![A,B,0,u,v] ![A+y,B+z,0,u,v] := by
  funext S
  rw [nativeTriangle_formula]
  unfold starAtSetFunction
  simp only [Finset.sum_erase_eq_sub (Finset.mem_univ (2 : Fin 5)),
    Fin.sum_univ_five]
  by_cases h0 : (0 : Fin 5) ∈ S <;>
  by_cases h1 : (1 : Fin 5) ∈ S <;>
  by_cases h2 : (2 : Fin 5) ∈ S <;>
  by_cases h3 : (3 : Fin 5) ∈ S <;>
  by_cases h4 : (4 : Fin 5) ∈ S <;>
  simp [coordinate,vec5_three,vec5_four,h0,h1,h2,h3,h4] <;>
  linarith only [htotal]

/-- All-real star vanishing implies triangle vanishing for the actual native
quadratic and every permutation chain. Xi can be an arbitrary function. -/
theorem native_triangle_sum_zero_of_stars
    (Xi : (Fin 4 → ℝ) → ℝ)
    (hstar : ∀ (c : Fin 5) (a b : Fin 5 → ℝ),
      (∑ pi : Equiv.Perm (Fin 5),Xi (permutationFunctionChain
        (starAtSetFunction c a b) pi))=0)
    (A B C x y z u v : ℝ) (htotal : A+B+C+x+y+z+u+v=0) :
    (∑ pi : Equiv.Perm (Fin 5),Xi (permutationFunctionChain
      (nativeTriangle ![A,B,C,x,y,z,u,v]) pi))=0 := by
  apply native_triangle_sum_zero_of_zero_edge Xi u v ?_ A B C x y z htotal
  intro a b c d e f ht hz
  rcases hz with hd | he | hf
  · subst d
    rw [native_zero01_eq_star a b c e f u v (by linarith only [ht])]
    exact hstar _ _ _
  · subst e
    rw [native_zero02_eq_star a b c d f u v (by linarith only [ht])]
    exact hstar _ _ _
  · subst f
    rw [native_zero12_eq_star a b c d e u v (by linarith only [ht])]
    exact hstar _ _ _

/-- The coefficient-certificate interface now covers primitive triangles too.
The universal finite certificate hypothesis is explicit until its checker is
attached by the closed star theorem. No extra analytic hypothesis occurs. -/
theorem native_triangle_starXi_of_coefficients
    (hcoeff : ∀ (p : Fin 4 → ℝ) (t : Fin 80),
      evalForm (starAnovaCoefficients (actualSigns subsetForms p) t) p=0)
    (A B C x y z u v : ℝ) (htotal : A+B+C+x+y+z+u+v=0) :
    (∑ pi : Equiv.Perm (Fin 5),starXi (permutationFunctionChain
      (nativeTriangle ![A,B,C,x,y,z,u,v]) pi))=0 :=
  native_triangle_sum_zero_of_stars starXi
    (starAt_permutation_sum_of_coefficients hcoeff) A B C x y z u v htotal

#check @native_triangle_sum_zero_of_stars
#print axioms native_zero12_eq_star
#print axioms native_zero02_eq_star
#print axioms native_zero01_eq_star
#print axioms native_triangle_sum_zero_of_stars
#print axioms native_triangle_starXi_of_coefficients
end MaxCaterpillar.Frontier.StarCertificate.TriangleInterleavings
