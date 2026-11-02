import MaxCaterpillar.Frontier.StarCertificate.SmallMatchingGraphQuadratic
import MaxCaterpillar.Frontier.StarCertificate.StarCenters

/-! # The actual native star formula for a quadratic interaction star

The constant and center slope are consequences of the empty/full evaluations.
All original matrix entries remain arbitrary real numbers, including asymmetric
entries, diagonal terms, and cancellations between opposite entries.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

/-- The full-set constraint determines the actual effective center slope. -/
theorem booleanQuadratic_effective_center (a : ℝ) (b : Fin 5 → ℝ)
    (d : Fin 5 → Fin 5 → ℝ) (c : Fin 5)
    (hstar : ∀ i j,(quadraticInteractionGraph d).Adj i j → i=c ∨ j=c)
    (hEmpty : booleanQuadratic a b d ∅=0)
    (hFull : booleanQuadratic a b d Finset.univ=0) :
    effectiveLinear b d c =
      -(∑ i in (Finset.univ : Finset (Fin 5)).erase c,
        (effectiveLinear b d i+effectiveInteraction d c i)) := by
  classical
  have ha : a=0 := by simpa [booleanQuadratic,booleanCoordinate] using hEmpty
  have he := booleanQuadratic_star_split a b d c hstar Finset.univ
  rw [hFull,ha] at he
  simp only [booleanCoordinate,Finset.mem_univ,if_true,mul_one,one_mul,zero_add] at he
  rw [Finset.sum_add_distrib]
  linarith only [he]

/-- A star in the actual interaction graph gives the literal erased-center
native star formula, with slopes extracted from the unrestricted real matrix. -/
theorem booleanQuadratic_eq_starAt_of_interaction_star
    (a : ℝ) (b : Fin 5 → ℝ) (d : Fin 5 → Fin 5 → ℝ) (c : Fin 5)
    (hstar : ∀ i j,(quadraticInteractionGraph d).Adj i j → i=c ∨ j=c)
    (hEmpty : booleanQuadratic a b d ∅=0)
    (hFull : booleanQuadratic a b d Finset.univ=0) :
    booleanQuadratic a b d =
      starAtSetFunction c (effectiveLinear b d)
        (fun i => effectiveLinear b d i+effectiveInteraction d c i) := by
  classical
  have ha : a=0 := by simpa [booleanQuadratic,booleanCoordinate] using hEmpty
  have hcenter := booleanQuadratic_effective_center a b d c hstar hEmpty hFull
  funext B
  rw [ha]
  have he := booleanQuadratic_star_split a b d c hstar B
  rw [ha] at he
  by_cases hc : c∈B
  · have hcoord : booleanCoordinate c B=1 := by simp [booleanCoordinate,hc]
    simp only [hcoord,mul_one,one_mul,zero_add] at he
    have hselected :
        (∑ i in (Finset.univ : Finset (Fin 5)).erase c,
          effectiveLinear b d i*booleanCoordinate i B)+
        (∑ i in (Finset.univ : Finset (Fin 5)).erase c,
          effectiveInteraction d c i*booleanCoordinate i B)=
        ∑ i in (Finset.univ : Finset (Fin 5)).erase c,
          if i∈B then effectiveLinear b d i+effectiveInteraction d c i else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i∈B <;> simp [booleanCoordinate,hi]
    have hpartition :
        (∑ i in (Finset.univ : Finset (Fin 5)).erase c,
          if i∈B then effectiveLinear b d i+effectiveInteraction d c i else 0)+
        (∑ i in (Finset.univ : Finset (Fin 5)).erase c,
          if i∉B then effectiveLinear b d i+effectiveInteraction d c i else 0)=
        ∑ i in (Finset.univ : Finset (Fin 5)).erase c,
          (effectiveLinear b d i+effectiveInteraction d c i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i∈B <;> simp [hi]
    rw [starAtSetFunction,if_pos hc]
    linarith only [he,hcenter,hselected,hpartition]
  · have hcoord : booleanCoordinate c B=0 := by simp [booleanCoordinate,hc]
    simp only [hcoord,mul_zero,zero_mul,zero_add,add_zero] at he
    rw [starAtSetFunction,if_neg hc,he]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i∈B <;> simp [booleanCoordinate,hi]

/-- The generic matching obstruction yields either this explicit native star
or an actual interaction graph supported on three vertices. -/
theorem booleanQuadratic_native_star_or_triangle
    (a : ℝ) (b : Fin 5 → ℝ) (d : Fin 5 → Fin 5 → ℝ)
    (H : PairwiseIntersectingEdges (quadraticInteractionGraph d))
    (hEmpty : booleanQuadratic a b d ∅=0)
    (hFull : booleanQuadratic a b d Finset.univ=0) :
    (∃ c,booleanQuadratic a b d =
      starAtSetFunction c (effectiveLinear b d)
        (fun i => effectiveLinear b d i+effectiveInteraction d c i)) ∨
      TriangleContained (quadraticInteractionGraph d) := by
  rcases pairwiseIntersectingEdges_star_or_triangle (quadraticInteractionGraph d) H with
    ⟨c,hstar⟩ | htriangle
  · exact Or.inl ⟨c,booleanQuadratic_eq_starAt_of_interaction_star a b d c
      hstar hEmpty hFull⟩
  · exact Or.inr htriangle

end MaxCaterpillar.Frontier.StarCertificate
