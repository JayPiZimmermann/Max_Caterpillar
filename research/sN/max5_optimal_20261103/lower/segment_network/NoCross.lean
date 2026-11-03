import research.sN.max5_optimal_20261103.lower.segment_network.SegmentNetwork

/-! The no-cross obstruction for actual homogeneous shallow cores. Every
physical row satisfies the displayed endpoint-coordinate condition, and the
midpoint sums include all rows with their signed coefficients. This is a
conditional analytic bridge, not a classification of row supports. -/
set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.SegmentNetwork
open BigOperators Frontier TripleContact

/-- The midpoint defect retains the exact normalization of `relu (2*t-1)`. -/
lemma row_no_cross_midpoint_identity (p q : ℝ)
    (h : p=0 ∨ q=0 ∨ p+q=0) :
    2*rowCurve p q (1/2)=rowCurve p q 0+rowCurve p q 1-midpointWeight p q := by
  obtain ⟨u,v,huv⟩ := row_curve_decomposition p q h
  have h0 := huv 0 (by norm_num) (by norm_num)
  have h1 := huv 1 (by norm_num) (by norm_num)
  have hm := huv (1/2) (by norm_num) (by norm_num)
  norm_num [relu] at h0 h1 hm
  linarith only [h0,h1,hm]

/-- Sum the midpoint defects of every physical row, preserving signs,
repeated rows, zero rows, and cancellation. -/
lemma core_no_cross_midpoint_identity {m : ℕ}
    (A : Fin m → Point 5) (c : Fin m → ℝ)
    (hrows : ∀ j, A j 3=0 ∨ A j 4=0 ∨ A j 3+A j 4=0) :
    2*core A c (contactPoint (1/2))=
      core A c (-unitVec (4 : Fin 5))+core A c (-unitVec (3 : Fin 5))-
        ∑ j, c j*midpointWeight (A j 3) (A j 4) := by
  have h0 : contactPoint 0= -unitVec (4 : Fin 5) := by simp [contactPoint]
  have h1 : contactPoint 1= -unitVec (3 : Fin 5) := by simp [contactPoint]
  rw [←h0,←h1]
  calc
    2*core A c (contactPoint (1/2))=
        ∑ j, c j*(2*rowCurve (A j 3) (A j 4) (1/2)) := by
      simp only [core,lin_contactPoint,rowCurve,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _=∑ j, (c j*rowCurve (A j 3) (A j 4) 0+
        c j*rowCurve (A j 3) (A j 4) 1-
        c j*midpointWeight (A j 3) (A j 4)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [row_no_cross_midpoint_identity _ _ (hrows j)]
      ring
    _=_ := by
      simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,
        core,lin_contactPoint,rowCurve]

/-- With zero cores at both contact endpoints, two nonzero signed midpoint
sums contradict exact Max5, even with an arbitrary affine shallow remainder. -/
theorem no_cross_nonzero_midpoint_masses {m mR : ℕ}
    (A : Fin m → Point 5) (c d : Fin m → ℝ)
    (aR : Point 5) (bR : ℝ) (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ)
    (hrows : ∀ j, A j 3=0 ∨ A j 4=0 ∨ A j 3+A j 4=0)
    (hcMass : (∑ j, c j*midpointWeight (A j 3) (A j 4))≠0)
    (hdMass : (∑ j, d j*midpointWeight (A j 3) (A j 4))≠0)
    (hc3 : core A c (-unitVec (3 : Fin 5))=0)
    (hc4 : core A c (-unitVec (4 : Fin 5))=0)
    (hd3 : core A d (-unitVec (3 : Fin 5))=0)
    (hd4 : core A d (-unitVec (4 : Fin 5))=0)
    (heq : ∀ x, shallow aR bR AR βR cR x+
      relu (core A c x)+relu (core A d x)=Maximum 5 x) : False := by
  have hc := core_no_cross_midpoint_identity A c hrows
  have hd := core_no_cross_midpoint_identity A d hrows
  rw [hc3,hc4] at hc
  rw [hd3,hd4] at hd
  have hcMid : core A c (contactPoint (1/2))≠0 := by
    intro hz
    apply hcMass
    linarith only [hc,hz]
  have hdMid : core A d (contactPoint (1/2))≠0 := by
    intro hz
    apply hdMass
    linarith only [hd,hz]
  have heq' : ∀ x, shallow aR bR AR βR cR x+
      relu (shallow 0 0 A 0 c x)+relu (shallow 0 0 A 0 d x)=Maximum 5 x := by
    simpa only [←core_shallow] using heq
  have h := max5_weighted_pair_contact aR 0 0 bR 0 0 AR βR cR A 0 c A 0 d
    heq' 3 4 (by decide) (1/2) (1/2) (by norm_num) (by norm_num)
  have hzero : core A c (contactPoint (1/2))=0 ∨
      core A d (contactPoint (1/2))=0 := by
    norm_num only [←core_shallow,contactPoint,show (1:ℝ)-1/2=1/2 by norm_num]
    simpa only [←core_shallow] using h
  exact hzero.elim hcMid hdMid

/-- Unit midpoint masses are the normalized no-cross sector used by the
analytic support argument. The sum is over all physical first-layer rows. -/
theorem no_cross_unit_midpoint_masses {m mR : ℕ}
    (A : Fin m → Point 5) (c d : Fin m → ℝ)
    (aR : Point 5) (bR : ℝ) (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ)
    (hrows : ∀ j, A j 3=0 ∨ A j 4=0 ∨ A j 3+A j 4=0)
    (hcMass : (∑ j, c j*midpointWeight (A j 3) (A j 4))=1)
    (hdMass : (∑ j, d j*midpointWeight (A j 3) (A j 4))=1)
    (hc3 : core A c (-unitVec (3 : Fin 5))=0)
    (hc4 : core A c (-unitVec (4 : Fin 5))=0)
    (hd3 : core A d (-unitVec (3 : Fin 5))=0)
    (hd4 : core A d (-unitVec (4 : Fin 5))=0)
    (heq : ∀ x, shallow aR bR AR βR cR x+
      relu (core A c x)+relu (core A d x)=Maximum 5 x) : False := by
  exact no_cross_nonzero_midpoint_masses A c d aR bR AR βR cR hrows
    (by rw [hcMass]; norm_num) (by rw [hdMass]; norm_num) hc3 hc4 hd3 hd4 heq

#check @row_no_cross_midpoint_identity
#print axioms row_no_cross_midpoint_identity
#check @core_no_cross_midpoint_identity
#print axioms core_no_cross_midpoint_identity
#check @no_cross_nonzero_midpoint_masses
#print axioms no_cross_nonzero_midpoint_masses
#check @no_cross_unit_midpoint_masses
#print axioms no_cross_unit_midpoint_masses
end MaxCaterpillar.Max5Optimal.SegmentNetwork
