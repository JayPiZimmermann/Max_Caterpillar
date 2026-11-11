import research.sN.max5_optimal_20261103.lower.triple_contact.TripleContact
import research.sN.max5_optimal_20261103.lower.width4_geometry.SegmentBalance

/-! The shared-contact segment obstruction for actual homogeneous shallow
cores. Rows have arbitrary orientations and signed coefficients. -/
set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.SegmentNetwork
open BigOperators Frontier TripleContact SegmentBalance

lemma relu_mul_nonnegative {a : ℝ} (ha : 0≤a) (b : ℝ) :
    relu (a*b)=a*relu b := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [←h]
    simp [relu]
  · exact relu_mul_pos h b

noncomputable def midpointWeight (p q : ℝ) : ℝ :=
  if p+q=0 then |p| else 0

noncomputable def rowCurve (p q t : ℝ) : ℝ := relu ((q-p)*t-q)

/-- Any row omitting one endpoint coordinate or balanced between them
is an affine curve plus its exact midpoint hinge coefficient. -/
lemma row_curve_decomposition (p q : ℝ)
    (h : p=0 ∨ q=0 ∨ p+q=0) :
    ∃ u v : ℝ, ∀ t : ℝ, 0≤t → t≤1 →
      rowCurve p q t = u*t+v+midpointWeight p q*relu (2*t-1) := by
  rcases h with hp | hq | hpq
  · subst p
    refine ⟨-relu (-q),relu (-q),fun t ht0 ht1 => ?_⟩
    have hw : midpointWeight 0 q=0 := by simp [midpointWeight]
    rw [hw,zero_mul]
    have hr : rowCurve 0 q t=(1-t)*relu (-q) := by
      unfold rowCurve
      rw [show (q-0)*t-q=(1-t)*(-q) by ring]
      exact relu_mul_nonnegative (by linarith only [ht1]) _
    rw [hr]
    ring
  · subst q
    refine ⟨relu (-p),0,fun t ht0 ht1 => ?_⟩
    have hw : midpointWeight p 0=0 := by
      by_cases hp : p=0 <;> simp [midpointWeight,hp]
    rw [hw,zero_mul]
    have hr : rowCurve p 0 t=t*relu (-p) := by
      unfold rowCurve
      rw [show (0-p)*t-0=t*(-p) by ring]
      exact relu_mul_nonnegative ht0 _
    rw [hr]
    ring
  · have hq : q=-p := by linarith only [hpq]
    subst q
    by_cases hp : 0≤p
    · refine ⟨-2*p,p,fun t ht0 ht1 => ?_⟩
      have hr : rowCurve p (-p) t=p*relu (-(2*t-1)) := by
        unfold rowCurve
        rw [show (-p-p)*t- -p=p*(-(2*t-1)) by ring]
        exact relu_mul_nonnegative hp _
      have hw : midpointWeight p (-p)=p := by simp [midpointWeight,abs_of_nonneg hp]
      rw [hr,hw]
      have hh := relu_sub_relu_neg (2*t-1)
      linear_combination -p*hh
    · have hp' : p≤0 := le_of_lt (lt_of_not_ge hp)
      refine ⟨0,0,fun t ht0 ht1 => ?_⟩
      have hr : rowCurve p (-p) t=(-p)*relu (2*t-1) := by
        unfold rowCurve
        rw [show (-p-p)*t- -p=(-p)*(2*t-1) by ring]
        exact relu_mul_nonnegative (neg_nonneg.mpr hp') _
      have hw : midpointWeight p (-p)= -p := by simp [midpointWeight,abs_of_nonpos hp']
      rw [hr,hw]
      ring

noncomputable def contactPoint (t : ℝ) : Point 5 :=
  -(t • unitVec (3 : Fin 5)) - (1-t) • unitVec (4 : Fin 5)

noncomputable def core {m : ℕ} (A : Fin m → Point 5) (c : Fin m → ℝ)
    (x : Point 5) : ℝ := ∑ j, c j*relu (lin (A j) x)

lemma lin_contactPoint (a : Point 5) (t : ℝ) :
    lin a (contactPoint t)=(a 4-a 3)*t-a 4 := by
  simp only [contactPoint,lin_sub_right,lin_neg_right,lin_smul_right,lin_unitVec]
  ring

lemma core_shallow {m : ℕ} (A : Fin m → Point 5) (c : Fin m → ℝ) :
    core A c=shallow 0 0 A 0 c := by
  funext x
  simp [core,shallow,lin_zero_left]

noncomputable def midpointMass {m : ℕ} (A : Fin m → Point 5)
    (c : Fin m → ℝ) (k : Fin m) : ℝ :=
  ∑ j in Finset.univ.erase k, c j*midpointWeight (A j 3) (A j 4)

/-- Direct evaluation of the actual finite ReLU sum on the segment. -/
lemma core_segment_decomposition {m : ℕ} (A : Fin m → Point 5)
    (c : Fin m → ℝ) (k : Fin m)
    (hrows : ∀ j, j≠k → A j 3=0 ∨ A j 4=0 ∨ A j 3+A j 4=0)
    (hmass : midpointMass A c k=1) :
    ∃ u v : ℝ, ∀ t : ℝ, 0≤t → t≤1 →
      core A c (contactPoint t)=twoHinge u v (c k) (A k 4-A k 3) (-A k 4) t := by
  classical
  have hrow : ∀ j, ∃ u v : ℝ, j≠k → ∀ t : ℝ, 0≤t → t≤1 →
      rowCurve (A j 3) (A j 4) t=
        u*t+v+midpointWeight (A j 3) (A j 4)*relu (2*t-1) := by
    intro j
    by_cases hj : j=k
    · exact ⟨0,0,fun hn => False.elim (hn hj)⟩
    · obtain ⟨u,v,huv⟩ := row_curve_decomposition (A j 3) (A j 4) (hrows j hj)
      exact ⟨u,v,fun _ => huv⟩
  choose u v huv using hrow
  let s := Finset.univ.erase k
  refine ⟨∑ j in s, c j*u j,∑ j in s, c j*v j,fun t ht0 ht1 => ?_⟩
  have he : core A c (contactPoint t)=c k*rowCurve (A k 3) (A k 4) t+
      ∑ j in s, c j*rowCurve (A j 3) (A j 4) t := by
    simp only [core,lin_contactPoint]
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
  rw [he]
  have hs : (∑ j in s, c j*rowCurve (A j 3) (A j 4) t)=
      (∑ j in s, c j*u j)*t+(∑ j in s, c j*v j)+relu (2*t-1) := by
    calc
      _=∑ j in s, ((c j*u j)*t+c j*v j+
          (c j*midpointWeight (A j 3) (A j 4))*relu (2*t-1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [huv j (Finset.ne_of_mem_erase hj) t ht0 ht1]
        ring
      _=(∑ j in s, c j*u j)*t+(∑ j in s, c j*v j)+
          midpointMass A c k*relu (2*t-1) := by
        simp only [Finset.sum_add_distrib,Finset.sum_mul,midpointMass,s]
      _=_ := by rw [hmass,one_mul]
  rw [hs]
  unfold twoHinge rowCurve
  ring

/-- An actual exact-Max5 representation with two homogeneous shallow cores:
if all but one physical first row are affine or balanced on the shared
contact segment, the exceptional row must be balanced too. The two stated
midpoint masses are signed sums, so repetitions and cancellations remain. -/
theorem exceptional_row_balanced {m mR : ℕ}
    (A : Fin m → Point 5) (c d : Fin m → ℝ) (k : Fin m)
    (aR : Point 5) (bR : ℝ) (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ)
    (hrows : ∀ j, j≠k → A j 3=0 ∨ A j 4=0 ∨ A j 3+A j 4=0)
    (hcMass : midpointMass A c k=1) (hdMass : midpointMass A d k=1)
    (hc3 : core A c (-unitVec (3 : Fin 5))=0)
    (hc4 : core A c (-unitVec (4 : Fin 5))=0)
    (hd3 : core A d (-unitVec (3 : Fin 5))=0)
    (hd4 : core A d (-unitVec (4 : Fin 5))=0)
    (heq : ∀ x, shallow aR bR AR βR cR x+
      relu (core A c x)+relu (core A d x)=Maximum 5 x) : A k 3+A k 4=0 := by
  obtain ⟨u,v,hc⟩ := core_segment_decomposition A c k hrows hcMass
  obtain ⟨w,z,hd⟩ := core_segment_decomposition A d k hrows hdMass
  have h0 : contactPoint 0= -unitVec (4 : Fin 5) := by simp [contactPoint]
  have h1 : contactPoint 1= -unitVec (3 : Fin 5) := by simp [contactPoint]
  have hf0 : twoHinge u v (c k) (A k 4-A k 3) (-A k 4) 0=0 := by
    rw [←hc 0 (by norm_num) (by norm_num),h0]
    exact hc4
  have hf1 : twoHinge u v (c k) (A k 4-A k 3) (-A k 4) 1=0 := by
    rw [←hc 1 (by norm_num) (by norm_num),h1]
    exact hc3
  have hg0 : twoHinge w z (d k) (A k 4-A k 3) (-A k 4) 0=0 := by
    rw [←hd 0 (by norm_num) (by norm_num),h0]
    exact hd4
  have hg1 : twoHinge w z (d k) (A k 4-A k 3) (-A k 4) 1=0 := by
    rw [←hd 1 (by norm_num) (by norm_num),h1]
    exact hd3
  have hzero : ∀ t : ℝ, 0<t → t<1 →
      twoHinge u v (c k) (A k 4-A k 3) (-A k 4) t=0 ∨
      twoHinge w z (d k) (A k 4-A k 3) (-A k 4) t=0 := by
    intro t ht0 ht1
    rw [←hc t ht0.le ht1.le,←hd t ht0.le ht1.le]
    have heq' : ∀ x, shallow aR bR AR βR cR x+
        relu (shallow 0 0 A 0 c x)+relu (shallow 0 0 A 0 d x)=Maximum 5 x := by
      simpa only [←core_shallow] using heq
    have h := max5_weighted_pair_contact aR 0 0 bR 0 0 AR βR cR A 0 c A 0 d
      heq' 3 4 (by decide) t (1-t) ht0 (by linarith only [ht1])
    simpa only [←core_shallow,contactPoint] using h
  have hh := crossing_balanced u v (c k) w z (d k) (A k 4-A k 3) (-A k 4)
    hf0 hf1 hg0 hg1 hzero
  linarith only [hh]

lemma sum_three_coordinate_support (a : Point 5) (r : Fin 5)
    (hr3 : r≠3) (hr4 : r≠4)
    (hoff : ∀ i, i≠r → i≠3 → i≠4 → a i=0) :
    (∑ i, a i)=a r+a 3+a 4 := by
  classical
  have hs : (∑ i in ({r,3,4} : Finset (Fin 5)), a i)=∑ i, a i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hn
    have hir : i≠r := fun e => hn (by simp [e])
    have hi3 : i≠3 := fun e => hn (by simp [e])
    have hi4 : i≠4 := fun e => hn (by simp [e])
    exact hoff i hir hi3 hi4
  rw [←hs]
  rw [Finset.sum_insert (by simp [hr3,hr4]),
    Finset.sum_insert (by decide),Finset.sum_singleton]
  ring

/-- Invariant exceptional rows supported on exactly three coordinates
cannot supply the crossing: balance would force the third entry to zero. -/
theorem no_three_coordinate_exception {m mR : ℕ}
    (A : Fin m → Point 5) (c d : Fin m → ℝ) (k : Fin m)
    (aR : Point 5) (bR : ℝ) (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ)
    (hrows : ∀ j, j≠k → A j 3=0 ∨ A j 4=0 ∨ A j 3+A j 4=0)
    (hcMass : midpointMass A c k=1) (hdMass : midpointMass A d k=1)
    (hc3 : core A c (-unitVec (3 : Fin 5))=0)
    (hc4 : core A c (-unitVec (4 : Fin 5))=0)
    (hd3 : core A d (-unitVec (3 : Fin 5))=0)
    (hd4 : core A d (-unitVec (4 : Fin 5))=0)
    (heq : ∀ x, shallow aR bR AR βR cR x+
      relu (core A c x)+relu (core A d x)=Maximum 5 x)
    (r : Fin 5) (hr3 : r≠3) (hr4 : r≠4)
    (hoff : ∀ i, i≠r → i≠3 → i≠4 → A k i=0)
    (hsum : ∑ i, A k i=0) (hnz : A k r≠0) : False := by
  have hbal := exceptional_row_balanced A c d k aR bR AR βR cR
    hrows hcMass hdMass hc3 hc4 hd3 hd4 heq
  rw [sum_three_coordinate_support (A k) r hr3 hr4 hoff] at hsum
  exact hnz (by linarith only [hbal,hsum])

#check @core_segment_decomposition
#print axioms core_segment_decomposition
#check @exceptional_row_balanced
#print axioms exceptional_row_balanced
#check @no_three_coordinate_exception
#print axioms no_three_coordinate_exception
end MaxCaterpillar.Max5Optimal.SegmentNetwork
