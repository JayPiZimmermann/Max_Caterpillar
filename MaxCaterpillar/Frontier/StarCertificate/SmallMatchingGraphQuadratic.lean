import MaxCaterpillar.Frontier.StarCertificate.SmallMatchingGraph
import MaxCaterpillar.Frontier.StarCertificate.SmallMatchingGraphAlgebra
import MaxCaterpillar.Frontier.StarCertificate.MobiusQuadratic

/-! # Actual interaction graphs of unrestricted real quadratic set functions

Diagonal entries are absorbed into the linear coefficient, and opposite
ordered entries are added. No symmetry, zero-diagonal, rationality, or
noncancellation assumption is imposed on the original matrix.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

noncomputable def effectiveLinear (b : Fin 5 → ℝ) (d : Fin 5 → Fin 5 → ℝ)
    (i : Fin 5) : ℝ := b i+d i i
noncomputable def effectiveInteraction (d : Fin 5 → Fin 5 → ℝ) (i j : Fin 5) : ℝ :=
  d i j+d j i

/-- Edges are exactly the nonzero actual off-diagonal interaction coefficients. -/
noncomputable def quadraticInteractionGraph (d : Fin 5 → Fin 5 → ℝ) : SimpleGraph (Fin 5) where
  Adj i j := i≠j ∧ effectiveInteraction d i j≠0
  symm := by
    intro i j h
    refine ⟨h.1.symm,?_⟩
    simpa only [effectiveInteraction,add_comm] using h.2
  loopless := by intro i h; exact h.1 rfl

/-- Absence of a noncentral graph edge forces its actual coefficient to vanish. -/
theorem effectiveInteraction_zero_away_from_star
    (d : Fin 5 → Fin 5 → ℝ) (c : Fin 5)
    (hstar : ∀ i j,(quadraticInteractionGraph d).Adj i j → i=c ∨ j=c)
    (i j : Fin 5) (hi : i≠c) (hj : j≠c) (hij : i≠j) :
    effectiveInteraction d i j=0 := by
  by_contra hn
  rcases hstar i j ⟨hij,hn⟩ with h | h
  · exact hi h
  · exact hj h

lemma booleanCoordinate_square (i : Fin 5) (B : Finset (Fin 5)) :
    booleanCoordinate i B*booleanCoordinate i B=booleanCoordinate i B := by
  classical
  by_cases hi : i∈B <;> simp [booleanCoordinate,hi]

/-- The complete ordered real quadratic matrix reduces to actual center
interactions when its nonzero support graph is contained in a star. -/
theorem booleanQuadratic_star_split (a : ℝ) (b : Fin 5 → ℝ)
    (d : Fin 5 → Fin 5 → ℝ) (c : Fin 5)
    (hstar : ∀ i j,(quadraticInteractionGraph d).Adj i j → i=c ∨ j=c)
    (B : Finset (Fin 5)) :
    booleanQuadratic a b d B = a+effectiveLinear b d c*booleanCoordinate c B+
      (∑ i in (Finset.univ : Finset (Fin 5)).erase c,
        effectiveLinear b d i*booleanCoordinate i B)+
      booleanCoordinate c B*(∑ i in (Finset.univ : Finset (Fin 5)).erase c,
        effectiveInteraction d c i*booleanCoordinate i B) := by
  classical
  let S : Finset (Fin 5) := Finset.univ.erase c
  have hcancel : ∀ i,i≠c → ∀ j,j≠c → i≠j → d i j+d j i=0 := by
    intro i hi j hj hij
    exact effectiveInteraction_zero_away_from_star d c hstar i j hi hj hij
  have hmatrix := quadratic_matrix_star_split d (fun i => booleanCoordinate i B) c hcancel
  simp_rw [booleanCoordinate_square] at hmatrix
  have hlin := sum_eq_center_add (fun i => b i*booleanCoordinate i B) c
  have hdiag : (∑ i in S,b i*booleanCoordinate i B)+
      (∑ i in S,d i i*booleanCoordinate i B)=
      ∑ i in S,effectiveLinear b d i*booleanCoordinate i B := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold effectiveLinear
    ring
  unfold booleanQuadratic
  rw [hmatrix,hlin]
  change a+(b c*booleanCoordinate c B+(∑ i in S,b i*booleanCoordinate i B))+
    (d c c*booleanCoordinate c B+(∑ i in S,d i i*booleanCoordinate i B)+
      booleanCoordinate c B*(∑ i in S,effectiveInteraction d c i*booleanCoordinate i B))=_
  calc
    _ = a+(b c+d c c)*booleanCoordinate c B+
      ((∑ i in S,b i*booleanCoordinate i B)+(∑ i in S,d i i*booleanCoordinate i B))+
      booleanCoordinate c B*(∑ i in S,effectiveInteraction d c i*booleanCoordinate i B) := by ring
    _ = _ := by rw [hdiag]; rfl

#print axioms effectiveInteraction_zero_away_from_star
#print axioms booleanQuadratic_star_split
end MaxCaterpillar.Frontier.StarCertificate
