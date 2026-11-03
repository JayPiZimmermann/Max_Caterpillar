import research.sN.max5_optimal_20261103.lower.segment_network.SegmentNetwork
set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.SegmentNetwork
open BigOperators Frontier TripleContact

/-- Exact expected public type. -/
example : ∀ {m mR : ℕ}
    (A : Fin m → Point 5) (c d : Fin m → ℝ) (k : Fin m)
    (aR : Point 5) (bR : ℝ) (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ),
    (∀ j, j≠k → A j 3=0 ∨ A j 4=0 ∨ A j 3+A j 4=0) →
    midpointMass A c k=1 → midpointMass A d k=1 →
    core A c (-unitVec (3 : Fin 5))=0 → core A c (-unitVec (4 : Fin 5))=0 →
    core A d (-unitVec (3 : Fin 5))=0 → core A d (-unitVec (4 : Fin 5))=0 →
    (∀ x, shallow aR bR AR βR cR x+
      relu (core A c x)+relu (core A d x)=Maximum 5 x) → A k 3+A k 4=0 :=
  @exceptional_row_balanced

/-- Literal array-and-max consumer, including the affine shallow remainder. -/
example {m mR : ℕ}
    (A : Fin m → Fin 5 → ℝ) (c d : Fin m → ℝ) (k : Fin m)
    (aR : Fin 5 → ℝ) (bR : ℝ) (AR : Fin mR → Fin 5 → ℝ) (βR cR : Fin mR → ℝ)
    (hrows : ∀ j, j≠k → A j 3=0 ∨ A j 4=0 ∨ A j 3+A j 4=0)
    (hcMass : (∑ j in Finset.univ.erase k,
      c j*(if A j 3+A j 4=0 then |A j 3| else 0))=1)
    (hdMass : (∑ j in Finset.univ.erase k,
      d j*(if A j 3+A j 4=0 then |A j 3| else 0))=1)
    (hc3 : (∑ j, c j*max 0 (-A j 3))=0)
    (hc4 : (∑ j, c j*max 0 (-A j 4))=0)
    (hd3 : (∑ j, d j*max 0 (-A j 3))=0)
    (hd4 : (∑ j, d j*max 0 (-A j 4))=0)
    (heq : ∀ x : Fin 5 → ℝ,
      (∑ i, aR i*x i)+bR+(∑ j, cR j*max 0 ((∑ i, AR j i*x i)+βR j))+
      max 0 (∑ j, c j*max 0 (∑ i, A j i*x i))+
      max 0 (∑ j, d j*max 0 (∑ i, A j i*x i))=Maximum 5 x) :
    A k 3+A k 4=0 := by
  apply exceptional_row_balanced A c d k aR bR AR βR cR hrows hcMass hdMass
  · simpa only [core,lin_neg_right,lin_unitVec,relu] using hc3
  · simpa only [core,lin_neg_right,lin_unitVec,relu] using hc4
  · simpa only [core,lin_neg_right,lin_unitVec,relu] using hd3
  · simpa only [core,lin_neg_right,lin_unitVec,relu] using hd4
  · simpa only [shallow,core,lin,relu] using heq

#check @exceptional_row_balanced
#print axioms exceptional_row_balanced
#check @no_three_coordinate_exception
#print axioms no_three_coordinate_exception
end MaxCaterpillar.Max5Optimal.SegmentNetwork
