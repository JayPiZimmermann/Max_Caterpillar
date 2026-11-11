import research.sN.max5_optimal_20261103.lower.width4_geometry.SegmentScalar

/-! The complete scalar balance lemma for two shared-contact curves.
The actual-network-to-curve bridge is not assumed by this file. -/
set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.SegmentBalance
open Frontier SegmentScalar

noncomputable def twoHinge (u v c A B t : ℝ) : ℝ :=
  u*t+v+relu (2*t-1)+c*relu (A*t+B)

lemma active (u v c A B t : ℝ) (ht : 0≤A*t+B) :
    twoHinge u v c A B t=curve (u+c*A) (v+c*B) t := by
  simp only [twoHinge,curve,relu_of_nonneg ht]
  ring

lemma reflection (u v c A B t : ℝ) :
    twoHinge u v c A B (1-t)=
      twoHinge (-u-2) (u+v+1) c (-A) (A+B) t := by
  have hh := relu_sub_relu_neg (2*t-1)
  simp only [twoHinge]
  rw [show 2*(1-t)-1=-(2*t-1) by ring,
    show A*(1-t)+B=(-A)*t+(A+B) by ring]
  linear_combination -hh

lemma complement (u v c A B t : ℝ) :
    twoHinge u v c A B t=
      twoHinge (u+c*A) (v+c*B) c (-A) (-B) t := by
  have hh := relu_sub_relu_neg (A*t+B)
  simp only [twoHinge]
  rw [show (-A)*t+-B=-(A*t+B) by ring]
  linear_combination c*hh

lemma positive_points (A B : ℝ) (hm : 0<A/2+B) :
    ∃ x y : ℝ, 0<x ∧ x<y ∧ y<1/2 ∧ 0≤A*x+B ∧ 0≤A*y+B := by
  by_cases hA : 0<A
  · have ht : -B/A<(1/2:ℝ) := (div_lt_iff hA).mpr (by linarith only [hm])
    have hz : max (0:ℝ) (-B/A)<1/2 := max_lt_iff.mpr ⟨by norm_num,ht⟩
    obtain ⟨x,hzx,hxm⟩ := exists_between hz
    obtain ⟨y,hxy,hym⟩ := exists_between hxm
    have hx0 : 0<x := lt_of_le_of_lt (le_max_left _ _) hzx
    have htx : -B/A<x := lt_of_le_of_lt (le_max_right _ _) hzx
    have hty : -B/A<y := htx.trans hxy
    have hx : -B<x*A := (div_lt_iff hA).mp htx
    have hy : -B<y*A := (div_lt_iff hA).mp hty
    refine ⟨x,y,hx0,hxy,hym,?_,?_⟩ <;> nlinarith only [hx,hy]
  · have hA0 : A≤0 := le_of_not_gt hA
    refine ⟨1/4,3/8,by norm_num,by norm_num,by norm_num,?_,?_⟩ <;>
      linarith only [hm,hA0]

lemma right_impossible (u v c w z d A B : ℝ)
    (hm : 0<A/2+B) (he : 0≤A+B)
    (hf1 : twoHinge u v c A B 1=0)
    (hg1 : twoHinge w z d A B 1=0)
    (hc : ∀ t : ℝ, 0<t → t<1 →
      twoHinge u v c A B t=0 ∨ twoHinge w z d A B t=0) : False := by
  obtain ⟨x,y,hx0,hxy,hym,hx,hy⟩ := positive_points A B hm
  have hu : 0≤A*(3/4)+B := by linarith only [hm,he]
  have he1 : 0≤A*1+B := by simpa only [mul_one] using he
  have hx1 : x<1 := by linarith only [hxy,hym]
  have hy0 : 0<y := hx0.trans hxy
  have hy1 : y<1 := by linarith only [hym]
  have hfx := hc x hx0 hx1
  have hfy := hc y hy0 hy1
  have hfu := hc (3/4) (by norm_num) (by norm_num)
  rw [active u v c A B 1 he1] at hf1
  rw [active w z d A B 1 he1] at hg1
  rw [active u v c A B x hx,active w z d A B x hx] at hfx
  rw [active u v c A B y hy,active w z d A B y hy] at hfy
  rw [active u v c A B (3/4) hu,active w z d A B (3/4) hu] at hfu
  exact no_three_point_zero_cover _ _ _ _ x y hxy hym hf1 hg1 hfx hfy hfu

lemma positive_midpoint_impossible (u v c w z d A B : ℝ)
    (hm : 0<A/2+B)
    (hf0 : twoHinge u v c A B 0=0) (hf1 : twoHinge u v c A B 1=0)
    (hg0 : twoHinge w z d A B 0=0) (hg1 : twoHinge w z d A B 1=0)
    (hc : ∀ t : ℝ, 0<t → t<1 →
      twoHinge u v c A B t=0 ∨ twoHinge w z d A B t=0) : False := by
  by_cases he : 0≤A+B
  · exact right_impossible u v c w z d A B hm he hf1 hg1 hc
  · have hm' : 0<(-A)/2+(A+B) := by linarith only [hm]
    have he' : 0≤(-A)+(A+B) := by linarith only [hm,le_of_not_ge he]
    have hf : twoHinge (-u-2) (u+v+1) c (-A) (A+B) 1=0 := by
      rw [←reflection u v c A B 1]
      simpa only [sub_self] using hf0
    have hg : twoHinge (-w-2) (w+z+1) d (-A) (A+B) 1=0 := by
      rw [←reflection w z d A B 1]
      simpa only [sub_self] using hg0
    apply right_impossible (-u-2) (u+v+1) c (-w-2) (w+z+1) d (-A) (A+B)
      hm' he' hf hg
    intro t ht0 ht1
    rw [←reflection u v c A B t,←reflection w z d A B t]
    exact hc (1-t) (by linarith only [ht1]) (by linarith only [ht0])

/-- If two shared-endpoint curves have the same unit root hinge and at most
one additional first hinge, zero coverage forces that hinge to vanish at
the midpoint. All coefficients are arbitrary real numbers. -/
theorem crossing_balanced (u v c w z d A B : ℝ)
    (hf0 : twoHinge u v c A B 0=0) (hf1 : twoHinge u v c A B 1=0)
    (hg0 : twoHinge w z d A B 0=0) (hg1 : twoHinge w z d A B 1=0)
    (hc : ∀ t : ℝ, 0<t → t<1 →
      twoHinge u v c A B t=0 ∨ twoHinge w z d A B t=0) : A/2+B=0 := by
  by_contra hm
  rcases lt_or_gt_of_ne hm with hm | hm
  · have hm' : 0<(-A)/2+(-B) := by linarith only [hm]
    have hf0' := hf0
    have hf1' := hf1
    have hg0' := hg0
    have hg1' := hg1
    rw [complement u v c A B 0] at hf0'
    rw [complement u v c A B 1] at hf1'
    rw [complement w z d A B 0] at hg0'
    rw [complement w z d A B 1] at hg1'
    apply positive_midpoint_impossible (u+c*A) (v+c*B) c
      (w+d*A) (z+d*B) d (-A) (-B) hm' hf0' hf1' hg0' hg1'
    intro t ht0 ht1
    rw [←complement u v c A B t,←complement w z d A B t]
    exact hc t ht0 ht1
  · exact positive_midpoint_impossible u v c w z d A B hm hf0 hf1 hg0 hg1 hc

/-- Literal-form consumer keeps the theorem's meaning independent of the
local curve notation. -/
example (u v c w z d A B : ℝ)
    (hf0 : u*0+v+max 0 (2*0-1)+c*max 0 (A*0+B)=0)
    (hf1 : u*1+v+max 0 (2*1-1)+c*max 0 (A*1+B)=0)
    (hg0 : w*0+z+max 0 (2*0-1)+d*max 0 (A*0+B)=0)
    (hg1 : w*1+z+max 0 (2*1-1)+d*max 0 (A*1+B)=0)
    (hc : ∀ t : ℝ, 0<t → t<1 →
      u*t+v+max 0 (2*t-1)+c*max 0 (A*t+B)=0 ∨
      w*t+z+max 0 (2*t-1)+d*max 0 (A*t+B)=0) : A/2+B=0 :=
  crossing_balanced u v c w z d A B hf0 hf1 hg0 hg1 hc

/-- Nonvacuity control: a coincident opposite hinge satisfies every
endpoint and zero-cover hypothesis. -/
theorem balanced_control (t : ℝ) : twoHinge 0 0 (-1) 2 (-1) t=0 := by
  simp only [twoHinge,zero_mul,zero_add,neg_one_mul]
  rw [show 2*t+-1=2*t-1 by ring]
  ring

example : ∃ u v c w z d A B : ℝ,
    twoHinge u v c A B 0=0 ∧ twoHinge u v c A B 1=0 ∧
    twoHinge w z d A B 0=0 ∧ twoHinge w z d A B 1=0 ∧
    (∀ t : ℝ, 0<t → t<1 →
      twoHinge u v c A B t=0 ∨ twoHinge w z d A B t=0) ∧ A≠0 := by
  refine ⟨0,0,-1,0,0,-1,2,-1,balanced_control 0,balanced_control 1,
    balanced_control 0,balanced_control 1,?_,by norm_num⟩
  intro t _ _
  exact Or.inl (balanced_control t)

/-- Coordinate form for the segment -t*e₃-(1-t)*e₄. -/
theorem coordinates_balanced (u v c w z d a3 a4 : ℝ)
    (hf0 : twoHinge u v c (a4-a3) (-a4) 0=0)
    (hf1 : twoHinge u v c (a4-a3) (-a4) 1=0)
    (hg0 : twoHinge w z d (a4-a3) (-a4) 0=0)
    (hg1 : twoHinge w z d (a4-a3) (-a4) 1=0)
    (hc : ∀ t : ℝ, 0<t → t<1 →
      twoHinge u v c (a4-a3) (-a4) t=0 ∨
      twoHinge w z d (a4-a3) (-a4) t=0) : a3+a4=0 := by
  have hh := crossing_balanced u v c w z d (a4-a3) (-a4) hf0 hf1 hg0 hg1 hc
  linarith only [hh]

#check @crossing_balanced
#print axioms crossing_balanced
#print axioms balanced_control
#print axioms coordinates_balanced
end MaxCaterpillar.Max5Optimal.SegmentBalance
