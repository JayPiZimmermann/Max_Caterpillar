import research.sN.max5_optimal_20261103.lower.segment_network.SegmentNetwork

/-! The same actual-network segment obstruction for arbitrary nonzero
signed midpoint curvatures. Scalar normalization changes only the curves
whose zero sets are examined; the exact network identity stays unchanged. -/
set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.SegmentNetwork
open BigOperators Frontier TripleContact SegmentBalance

lemma core_div {m : ℕ} (A : Fin m → Point 5) (c : Fin m → ℝ) (r : ℝ)
    (x : Point 5) : core A (fun j => c j/r) x=core A c x/r := by
  simp only [core,div_mul_eq_mul_div,Finset.sum_div]

lemma midpointMass_div {m : ℕ} (A : Fin m → Point 5) (c : Fin m → ℝ)
    (k : Fin m) (r : ℝ) :
    midpointMass A (fun j => c j/r) k=midpointMass A c k/r := by
  simp only [midpointMass,div_mul_eq_mul_div,Finset.sum_div]

/-- Both signed curvature sums may be arbitrary nonzero real numbers,
including opposite signs. No normalized network identity is assumed. -/
theorem exceptional_row_balanced_of_nonzero_mass {m mR : ℕ}
    (A : Fin m → Point 5) (c d : Fin m → ℝ) (k : Fin m)
    (aR : Point 5) (bR : ℝ) (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ)
    (hrows : ∀ j, j≠k → A j 3=0 ∨ A j 4=0 ∨ A j 3+A j 4=0)
    (hcMass : midpointMass A c k≠0) (hdMass : midpointMass A d k≠0)
    (hc3 : core A c (-unitVec (3 : Fin 5))=0)
    (hc4 : core A c (-unitVec (4 : Fin 5))=0)
    (hd3 : core A d (-unitVec (3 : Fin 5))=0)
    (hd4 : core A d (-unitVec (4 : Fin 5))=0)
    (heq : ∀ x, shallow aR bR AR βR cR x+
      relu (core A c x)+relu (core A d x)=Maximum 5 x) : A k 3+A k 4=0 := by
  let c' := fun j => c j/midpointMass A c k
  let d' := fun j => d j/midpointMass A d k
  have hcMass' : midpointMass A c' k=1 := by
    rw [midpointMass_div]
    exact div_self hcMass
  have hdMass' : midpointMass A d' k=1 := by
    rw [midpointMass_div]
    exact div_self hdMass
  obtain ⟨u,v,hc⟩ := core_segment_decomposition A c' k hrows hcMass'
  obtain ⟨w,z,hd⟩ := core_segment_decomposition A d' k hrows hdMass'
  have hcScale (x : Point 5) : core A c' x=core A c x/midpointMass A c k :=
    core_div A c _ x
  have hdScale (x : Point 5) : core A d' x=core A d x/midpointMass A d k :=
    core_div A d _ x
  have h0 : contactPoint 0= -unitVec (4 : Fin 5) := by simp [contactPoint]
  have h1 : contactPoint 1= -unitVec (3 : Fin 5) := by simp [contactPoint]
  have hf0 : twoHinge u v (c' k) (A k 4-A k 3) (-A k 4) 0=0 := by
    rw [←hc 0 (by norm_num) (by norm_num),h0,hcScale,hc4,zero_div]
  have hf1 : twoHinge u v (c' k) (A k 4-A k 3) (-A k 4) 1=0 := by
    rw [←hc 1 (by norm_num) (by norm_num),h1,hcScale,hc3,zero_div]
  have hg0 : twoHinge w z (d' k) (A k 4-A k 3) (-A k 4) 0=0 := by
    rw [←hd 0 (by norm_num) (by norm_num),h0,hdScale,hd4,zero_div]
  have hg1 : twoHinge w z (d' k) (A k 4-A k 3) (-A k 4) 1=0 := by
    rw [←hd 1 (by norm_num) (by norm_num),h1,hdScale,hd3,zero_div]
  have hzero : ∀ t : ℝ, 0<t → t<1 →
      twoHinge u v (c' k) (A k 4-A k 3) (-A k 4) t=0 ∨
      twoHinge w z (d' k) (A k 4-A k 3) (-A k 4) t=0 := by
    intro t ht0 ht1
    rw [←hc t ht0.le ht1.le,←hd t ht0.le ht1.le,hcScale,hdScale]
    have heq' : ∀ x, shallow aR bR AR βR cR x+
        relu (shallow 0 0 A 0 c x)+relu (shallow 0 0 A 0 d x)=Maximum 5 x := by
      simpa only [←core_shallow] using heq
    have h := max5_weighted_pair_contact aR 0 0 bR 0 0 AR βR cR A 0 c A 0 d
      heq' 3 4 (by decide) t (1-t) ht0 (by linarith only [ht1])
    have horig : core A c (contactPoint t)=0 ∨ core A d (contactPoint t)=0 := by
      simpa only [←core_shallow,contactPoint] using h
    rcases horig with h | h
    · left
      rw [h,zero_div]
    · right
      rw [h,zero_div]
  have hh := crossing_balanced u v (c' k) w z (d' k) (A k 4-A k 3) (-A k 4)
    hf0 hf1 hg0 hg1 hzero
  linarith only [hh]

/-- Guarded version used in necessary arithmetic models: a zero curvature
sum remains an allowed boundary case, rather than being divided away. -/
theorem balance_or_zero_midpoint_mass {m mR : ℕ}
    (A : Fin m → Point 5) (c d : Fin m → ℝ) (k : Fin m)
    (aR : Point 5) (bR : ℝ) (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ)
    (hrows : ∀ j, j≠k → A j 3=0 ∨ A j 4=0 ∨ A j 3+A j 4=0)
    (hc3 : core A c (-unitVec (3 : Fin 5))=0)
    (hc4 : core A c (-unitVec (4 : Fin 5))=0)
    (hd3 : core A d (-unitVec (3 : Fin 5))=0)
    (hd4 : core A d (-unitVec (4 : Fin 5))=0)
    (heq : ∀ x, shallow aR bR AR βR cR x+
      relu (core A c x)+relu (core A d x)=Maximum 5 x) :
    midpointMass A c k=0 ∨ midpointMass A d k=0 ∨ A k 3+A k 4=0 := by
  by_cases hc : midpointMass A c k=0
  · exact Or.inl hc
  by_cases hd : midpointMass A d k=0
  · exact Or.inr (Or.inl hd)
  exact Or.inr (Or.inr (exceptional_row_balanced_of_nonzero_mass A c d k aR bR AR βR cR
    hrows hc hd hc3 hc4 hd3 hd4 heq))

#check @exceptional_row_balanced_of_nonzero_mass
#print axioms exceptional_row_balanced_of_nonzero_mass
#check @balance_or_zero_midpoint_mass
#print axioms balance_or_zero_midpoint_mass
end MaxCaterpillar.Max5Optimal.SegmentNetwork
