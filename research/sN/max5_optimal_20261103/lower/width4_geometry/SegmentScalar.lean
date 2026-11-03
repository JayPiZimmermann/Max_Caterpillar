import MaxCaterpillar.Frontier.Basic
import Mathlib.Tactic

/-! Scalar finite-point obstruction used in the shared-contact segment
argument. This file does not formalize the actual-network reduction. -/
set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.SegmentScalar
open Frontier

noncomputable def curve (a b t : ℝ) : ℝ := a*t+b+relu (2*t-1)

/-- Two affine-plus-one-hinge curves, each zero at the right endpoint,
cannot cover two points left of the hinge and one point right of it by
their zero sets. Their hinge coefficients are exactly one. -/
theorem no_three_point_zero_cover (a b c d x y : ℝ)
    (hxy : x<y) (hy : y<(1/2:ℝ))
    (hf1 : curve a b 1=0) (hg1 : curve c d 1=0)
    (hx : curve a b x=0 ∨ curve c d x=0)
    (hy0 : curve a b y=0 ∨ curve c d y=0)
    (hu : curve a b (3/4)=0 ∨ curve c d (3/4)=0) : False := by
  have rx : relu (2*x-1)=0 := relu_of_nonpos (by linarith only [hxy,hy])
  have ry : relu (2*y-1)=0 := relu_of_nonpos (by linarith only [hy])
  have ru : relu (2*(3/4:ℝ)-1)=1/2 := by norm_num [relu]
  have aux : ∀ (a b c d : ℝ), a+b+1=0 → c+d+1=0 →
      (a*x+b=0 ∨ c*x+d=0) → (a*y+b=0 ∨ c*y+d=0) →
      a*(3/4)+b+1/2=0 → False := by
    intro a b c d hf hg hx' hy' hu'
    have ha : a=-2 := by linarith only [hf,hu']
    have hb : b=1 := by linarith only [hf,ha]
    have hfx : a*x+b≠0 := by rw [ha,hb]; linarith only [hxy,hy]
    have hfy : a*y+b≠0 := by rw [ha,hb]; linarith only [hy]
    have hcx : c*x+d=0 := hx'.resolve_left hfx
    have hcy : c*y+d=0 := hy'.resolve_left hfy
    have hprod : c*(x-y)=0 := by linear_combination hcx-hcy
    have hc : c=0 := (mul_eq_zero.mp hprod).resolve_right
      (sub_ne_zero.mpr (ne_of_lt hxy))
    have hd : d=0 := by simpa only [hc,zero_mul,zero_add] using hcx
    linarith only [hg,hc,hd]
  norm_num [curve,relu] at hf1 hg1
  simp only [curve,rx,add_zero] at hx
  simp only [curve,ry,add_zero] at hy0
  simp only [curve,ru] at hu
  rcases hu with hu | hu
  · exact aux a b c d hf1 hg1 hx hy0 hu
  · exact aux c d a b hg1 hf1 hx.symm hy0.symm hu

/-- Literal-form consumer: the proof is about actual real ReLU curves. -/
example (a b c d x y : ℝ) (hxy : x<y) (hy : y<(1/2:ℝ))
    (hf1 : a*1+b+max 0 (2*1-1)=0)
    (hg1 : c*1+d+max 0 (2*1-1)=0)
    (hx : a*x+b+max 0 (2*x-1)=0 ∨ c*x+d+max 0 (2*x-1)=0)
    (hy0 : a*y+b+max 0 (2*y-1)=0 ∨ c*y+d+max 0 (2*y-1)=0)
    (hu : a*(3/4)+b+max 0 (2*(3/4)-1)=0 ∨
      c*(3/4)+d+max 0 (2*(3/4)-1)=0) : False :=
  no_three_point_zero_cover a b c d x y hxy hy hf1 hg1 hx hy0 hu

#check @no_three_point_zero_cover
#print axioms no_three_point_zero_cover
end MaxCaterpillar.Max5Optimal.SegmentScalar
