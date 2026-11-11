import MaxCaterpillar.Fiber.PositiveKink

/-! # An eight-sample positive-hinge certificate for the symmetric fork

The three negative generators and five positive generators have equal sums.
Each negative singleton is a fractional selection of the positive generators.
Its complement certifies the corresponding pair. The eight choices of which
negative scores are positive therefore give the hinge inequality directly.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion.Corner
open MaxCaterpillar.Frontier

lemma fractional_relu_le (c x : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    c*x ≤ relu x := by
  calc
    c*x ≤ c*relu x := mul_le_mul_of_nonneg_left (le_max_right 0 x) hc0
    _ ≤ 1*relu x := mul_le_mul_of_nonneg_right hc1 (relu_nonneg x)
    _ = _ := one_mul _

lemma relu_triple_le_of_subset_bounds (x y z B : ℝ)
    (hB : 0 ≤ B) (hx : x ≤ B) (hy : y ≤ B) (hz : z ≤ B)
    (hxy : x+y ≤ B) (hxz : x+z ≤ B) (hyz : y+z ≤ B)
    (hxyz : x+y+z ≤ B) : relu x+relu y+relu z ≤ B := by
  have hrelu (a : ℝ) : relu a=if 0 ≤ a then a else 0 := by
    by_cases ha : 0 ≤ a
    · rw [if_pos ha,relu_of_nonneg ha]
    · rw [if_neg ha,relu_of_nonpos (le_of_lt (lt_of_not_ge ha))]
  rw [hrelu x,hrelu y,hrelu z]
  split_ifs <;> linarith only [hB,hx,hy,hz,hxy,hxz,hyz,hxyz]

/-- A three-generator zonotope is contained in a five-generator zonotope.
The proof checks the singleton vertices and their complements. -/
theorem five_three_hinge_dominance (p0 p1 p2 p3 p4 n0 n1 n2 : ℝ)
    (h0 : n0=p0+(3/5)*p1)
    (h1 : n1=p1+(1/2)*p3)
    (h2 : n2=p0+(1/2)*p2+p3)
    (hSum : p0+p1+p2+p3+p4=n0+n1+n2) :
    relu n0+relu n1+relu n2 ≤ relu p0+relu p1+relu p2+relu p3+relu p4 := by
  let B := relu p0+relu p1+relu p2+relu p3+relu p4
  have hp0 : p0 ≤ relu p0 := le_max_right _ _
  have hp1 : p1 ≤ relu p1 := le_max_right _ _
  have hp2 : p2 ≤ relu p2 := le_max_right _ _
  have hp3 : p3 ≤ relu p3 := le_max_right _ _
  have hp4 : p4 ≤ relu p4 := le_max_right _ _
  have h0n := relu_nonneg p0
  have h1n := relu_nonneg p1
  have h2n := relu_nonneg p2
  have h3n := relu_nonneg p3
  have h4n := relu_nonneg p4
  have hf1 := fractional_relu_le (3/5) p1 (by norm_num) (by norm_num)
  have hf1' := fractional_relu_le (2/5) p1 (by norm_num) (by norm_num)
  have hf2 := fractional_relu_le (1/2) p2 (by norm_num) (by norm_num)
  have hf3 := fractional_relu_le (1/2) p3 (by norm_num) (by norm_num)
  have hB : 0 ≤ B := by dsimp [B]; linarith only [h0n,h1n,h2n,h3n,h4n]
  have hn0 : n0 ≤ B := by
    dsimp [B]
    linarith only [h0,hp0,hf1,h2n,h3n,h4n]
  have hn1 : n1 ≤ B := by
    dsimp [B]
    linarith only [h1,hp1,hf3,h0n,h2n,h4n]
  have hn2 : n2 ≤ B := by
    dsimp [B]
    linarith only [h2,hp0,hf2,hp3,h1n,h4n]
  have hn01 : n0+n1 ≤ B := by
    dsimp [B]
    linarith only [hSum,h2,hp1,hf2,hp4,h0n,h3n]
  have hn02 : n0+n2 ≤ B := by
    dsimp [B]
    linarith only [hSum,h1,hp0,hp2,hf3,hp4,h1n]
  have hn12 : n1+n2 ≤ B := by
    dsimp [B]
    linarith only [hSum,h0,hf1',hp2,hp3,hp4,h0n]
  have hn012 : n0+n1+n2 ≤ B := by
    dsimp [B]
    linarith only [hSum,hp0,hp1,hp2,hp3,hp4]
  exact relu_triple_le_of_subset_bounds n0 n1 n2 B hB hn0 hn1 hn2 hn01 hn02 hn12 hn012

/-- The explicit universal inequality needed by the fork certificate. -/
theorem symmetric_fork_hinge_certificate (a b r s : ℝ) :
    relu (12*b+6*r+6*s)+relu (10*a+20*b+15*r)+relu (24*a+18*r+12*s) ≤
      relu (6*s)+relu (20*b+10*r)+relu (8*a+16*r+12*s)+
        relu (20*a+10*r)+relu (6*a+12*b+3*r) := by
  apply five_three_hinge_dominance <;> ring

#print axioms symmetric_fork_hinge_certificate
end MaxCaterpillar.Fiber.Count65.ForkExclusion.Corner
