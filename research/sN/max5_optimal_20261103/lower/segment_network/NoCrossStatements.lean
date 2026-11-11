import research.sN.max5_optimal_20261103.lower.segment_network.NoCross
set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.SegmentNetwork
open BigOperators Frontier TripleContact

/-- Exact expected type for the scalar bridge. -/
example : ∀ (p q : ℝ), (p=0 ∨ q=0 ∨ p+q=0) →
    2*rowCurve p q (1/2)=rowCurve p q 0+rowCurve p q 1-midpointWeight p q :=
  @row_no_cross_midpoint_identity

/-- Exact expected type for the actual-core bridge, including all rows. -/
example : ∀ {m : ℕ} (A : Fin m → Point 5) (c : Fin m → ℝ),
    (∀ j, A j 3=0 ∨ A j 4=0 ∨ A j 3+A j 4=0) →
    2*core A c (contactPoint (1/2))=
      core A c (-unitVec (4 : Fin 5))+core A c (-unitVec (3 : Fin 5))-
        ∑ j, c j*midpointWeight (A j 3) (A j 4) :=
  @core_no_cross_midpoint_identity

/-- Exact expected type of the stronger nonzero-mass obstruction. -/
example : ∀ {m mR : ℕ}
    (A : Fin m → Point 5) (c d : Fin m → ℝ)
    (aR : Point 5) (bR : ℝ) (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ),
    (∀ j, A j 3=0 ∨ A j 4=0 ∨ A j 3+A j 4=0) →
    (∑ j, c j*midpointWeight (A j 3) (A j 4))≠0 →
    (∑ j, d j*midpointWeight (A j 3) (A j 4))≠0 →
    core A c (-unitVec (3 : Fin 5))=0 → core A c (-unitVec (4 : Fin 5))=0 →
    core A d (-unitVec (3 : Fin 5))=0 → core A d (-unitVec (4 : Fin 5))=0 →
    (∀ x, shallow aR bR AR βR cR x+
      relu (core A c x)+relu (core A d x)=Maximum 5 x) → False :=
  @no_cross_nonzero_midpoint_masses

/-- Exact expected type of the requested unit-mass obstruction. -/
example : ∀ {m mR : ℕ}
    (A : Fin m → Point 5) (c d : Fin m → ℝ)
    (aR : Point 5) (bR : ℝ) (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ),
    (∀ j, A j 3=0 ∨ A j 4=0 ∨ A j 3+A j 4=0) →
    (∑ j, c j*midpointWeight (A j 3) (A j 4))=1 →
    (∑ j, d j*midpointWeight (A j 3) (A j 4))=1 →
    core A c (-unitVec (3 : Fin 5))=0 → core A c (-unitVec (4 : Fin 5))=0 →
    core A d (-unitVec (3 : Fin 5))=0 → core A d (-unitVec (4 : Fin 5))=0 →
    (∀ x, shallow aR bR AR βR cR x+
      relu (core A c x)+relu (core A d x)=Maximum 5 x) → False :=
  @no_cross_unit_midpoint_masses

/-- Literal array-and-max consumer with arbitrary affine shallow remainder. -/
example {m mR : ℕ}
    (A : Fin m → Fin 5 → ℝ) (c d : Fin m → ℝ)
    (aR : Fin 5 → ℝ) (bR : ℝ) (AR : Fin mR → Fin 5 → ℝ) (βR cR : Fin mR → ℝ)
    (hrows : ∀ j, A j 3=0 ∨ A j 4=0 ∨ A j 3+A j 4=0)
    (hcMass : (∑ j, c j*(if A j 3+A j 4=0 then |A j 3| else 0))=1)
    (hdMass : (∑ j, d j*(if A j 3+A j 4=0 then |A j 3| else 0))=1)
    (hc3 : (∑ j, c j*max 0 (-A j 3))=0)
    (hc4 : (∑ j, c j*max 0 (-A j 4))=0)
    (hd3 : (∑ j, d j*max 0 (-A j 3))=0)
    (hd4 : (∑ j, d j*max 0 (-A j 4))=0)
    (heq : ∀ x : Fin 5 → ℝ,
      (∑ i, aR i*x i)+bR+(∑ j, cR j*max 0 ((∑ i, AR j i*x i)+βR j))+
      max 0 (∑ j, c j*max 0 (∑ i, A j i*x i))+
      max 0 (∑ j, d j*max 0 (∑ i, A j i*x i))=Maximum 5 x) : False := by
  apply no_cross_unit_midpoint_masses A c d aR bR AR βR cR hrows hcMass hdMass
  · simpa only [core,lin_neg_right,lin_unitVec,relu] using hc3
  · simpa only [core,lin_neg_right,lin_unitVec,relu] using hc4
  · simpa only [core,lin_neg_right,lin_unitVec,relu] using hd3
  · simpa only [core,lin_neg_right,lin_unitVec,relu] using hd4
  · simpa only [shallow,core,lin,relu] using heq

/-- The row, endpoint, and unit-mass assumptions themselves are satisfiable.
Using this same coefficient array for both cores gives both sets of hypotheses.
The exact-Max5 identity is the incompatible extra condition. -/
example : ∃ (A : Fin 2 → Point 5) (c : Fin 2 → ℝ),
    (∀ j, A j 3=0 ∨ A j 4=0 ∨ A j 3+A j 4=0) ∧
    (∑ j, c j*midpointWeight (A j 3) (A j 4))=1 ∧
    core A c (-unitVec (3 : Fin 5))=0 ∧
    core A c (-unitVec (4 : Fin 5))=0 := by
  have h34 : (3 : Fin 5)≠4 := by decide
  have h43 : (4 : Fin 5)≠3 := by decide
  refine ⟨![unitVec 3-unitVec 4,-unitVec 4],![1,-1],?_,?_,?_,?_⟩
  · intro j
    fin_cases j <;> norm_num [unitVec,h34,h43]
  · norm_num [Fin.sum_univ_two,midpointWeight,unitVec,h34,h43]
  · norm_num [core,lin,relu,unitVec,Fin.sum_univ_succ,h34,h43]
  · norm_num [core,lin,relu,unitVec,Fin.sum_univ_succ,h34,h43]

#check @row_no_cross_midpoint_identity
#print axioms row_no_cross_midpoint_identity
#check @core_no_cross_midpoint_identity
#print axioms core_no_cross_midpoint_identity
#check @no_cross_nonzero_midpoint_masses
#print axioms no_cross_nonzero_midpoint_masses
#check @no_cross_unit_midpoint_masses
#print axioms no_cross_unit_midpoint_masses
end MaxCaterpillar.Max5Optimal.SegmentNetwork
