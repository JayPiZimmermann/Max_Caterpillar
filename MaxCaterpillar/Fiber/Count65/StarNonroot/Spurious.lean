import MaxCaterpillar.Fiber.Count65.StarNonroot.Carrier

/-! # A forced exterior carrier has a non-target crease

An explicit large point replaces the limiting small-epsilon construction:
its coordinates and every first-layer sign are strictly separated.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Count65.StarNonroot
open BigOperators MaxCaterpillar.Frontier

/-- A positive first coordinate away from its target breakpoint has an affine target germ. -/
theorem target_affine_first_near (x y z : ℝ) (hx : 0 < x)
    (hm : x ≠ max y (relu z)) :
    ∃ δ u v : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
      0 ≤ x+s ∧ target (x+s) y z = u*s+v := by
  let m := max y (relu z)
  let δ := min x |x-m|/2
  have hdiff : 0 < |x-m| := abs_pos.mpr (sub_ne_zero.mpr hm)
  have hd : 0 < δ := div_pos (lt_min hx hdiff) (by norm_num)
  have hdX : δ ≤ x/2 := by dsimp [δ]; linarith only [min_le_left x |x-m|]
  have hdM : δ ≤ |x-m|/2 := by dsimp [δ]; linarith only [min_le_right x |x-m|]
  rcases lt_or_gt_of_ne hm with hlt | hgt
  · refine ⟨δ,0,m,hd,?_⟩
    intro s hs
    obtain ⟨hs1,hs2⟩ := abs_lt.mp hs
    have hxs : 0 ≤ x+s := by linarith only [hs1,hdX,hx]
    refine ⟨hxs,?_⟩
    have hxm : x+s ≤ m := by
      rw [abs_of_neg (sub_neg.mpr hlt)] at hdM
      linarith only [hs2,hdM,hlt]
    unfold target
    rw [max_assoc, max_eq_right hxm, zero_mul, zero_add]
  · refine ⟨δ,1,x,hd,?_⟩
    intro s hs
    obtain ⟨hs1,hs2⟩ := abs_lt.mp hs
    have hxs : 0 ≤ x+s := by linarith only [hs1,hdX,hx]
    refine ⟨hxs,?_⟩
    have hmx : m ≤ x+s := by
      rw [abs_of_pos (sub_pos.mpr hgt)] at hdM
      linarith only [hs1,hdM,hgt]
    unfold target
    rw [max_assoc, max_eq_left hmx, one_mul]
    ring

/-- Every nontrivial `U(q1-q2)+W q3` core vanishes on a genuine non-target wall. -/
theorem ResidualSystem.spurious_point12 {ι : Type*} (d : ResidualSystem ι)
    (a b c : ℝ) (habc : a+b+c=0) (hc : c ≠ 0) (i : ι)
    (hu : d.U i ≠ 0) (hv : d.V i = -d.U i) (ht : d.T i = 0) :
    ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      x ≠ max y (relu z) ∧ a*x+b*y+c*z ≠ 0 ∧ d.gate a b c i x y z=0 := by
  by_cases hw : d.W i=0
  · refine ⟨1,1,2,by norm_num,by norm_num,by norm_num,?_,?_,?_⟩
    · norm_num [relu]
    · have he : a*1+b*1+c*2=c := by linarith only [habc]
      simpa only [he] using hc
    · simp only [ResidualSystem.gate,form,hv,ht,hw,zero_mul,
        relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
        relu_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      ring
  · let r := d.W i/d.U i
    let R := a*r/c
    let B := 3+|r|+|R|
    have hr : r*d.U i=d.W i := div_mul_cancel _ hu
    have hr0 : r ≠ 0 := div_ne_zero hw hu
    have hR : R*c=a*r := div_mul_cancel _ hc
    have hB : 1 < B := by dsimp [B]; linarith [abs_nonneg r,abs_nonneg R]
    have hx : 0 < B-r := by dsimp [B]; linarith [le_abs_self r,abs_nonneg R]
    have hfac : 1-B-R < 0 := by dsimp [B]; linarith [abs_nonneg r,neg_abs_le_self R]
    refine ⟨B-r,B,1,hx,by linarith,by norm_num,?_,?_,?_⟩
    · rw [relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),max_eq_left hB.le]
      intro he
      exact hr0 (by linarith only [he])
    · have he : a*(B-r)+b*B+c*1=c*(1-B-R) := by
        have hsum : (a+b+c)*B=0 := by rw [habc,zero_mul]
        nlinarith only [hsum,hR]
      rw [he]
      exact mul_ne_zero hc hfac.ne
    · simp only [ResidualSystem.gate,form,hv,ht,zero_mul,
        relu_of_nonneg hx.le,relu_of_nonneg (by linarith : (0:ℝ) ≤ B),
        relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
      nlinarith only [hr]

/-- The spurious wall cannot be canceled solely by positive-output gates. -/
theorem ResidualSystem.negative_gate_of_external12 {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (a b c : ℝ) (habc : a+b+c=0) (hc : c ≠ 0)
    (h : d.Represents a b c) (i : ι) (hi : 0 < d.out i)
    (hu : d.U i ≠ 0) (hv : d.V i = -d.U i) (ht : d.T i = 0) :
    ∃ j, d.out j < 0 := by
  obtain ⟨x,y,z,hx,hy,hz,hm,hn,hgate0⟩ := d.spurious_point12 a b c habc hc i hu hv ht
  obtain ⟨δH,u,v,hδH,hH⟩ := target_affine_first_near x y z hx hm
  obtain ⟨δT,hδT,hT⟩ := relu_affine_near a (a*x+b*y+c*z) hn
  let μ := if 0 < a*x+b*y+c*z then a else 0
  let δ := min δH δT
  have hδ : 0 < δ := lt_min hδH hδT
  have hidentity : ∀ s : ℝ, |s| < δ →
      (∑ j, d.out j*relu ((d.U j+d.T j*μ)*s+d.gate a b c j x y z)) =
        (u-(d.lU+d.lT*μ))*s+(v-d.base a b c x y z) := by
    intro s hs
    have hsH : |s| < δH := hs.trans_le (min_le_left _ _)
    have hsT : |s| < δT := hs.trans_le (min_le_right _ _)
    obtain ⟨hxs,hTarget⟩ := hH s hsH
    have he : a*(x+s)+b*y+c*z=(a*x+b*y+c*z)+a*s := by ring
    have hf : ∀ A B C D : ℝ, form a b c A B C D (x+s) y z =
        (A+D*μ)*s+form a b c A B C D x y z := by
      intro A B C D
      unfold form
      rw [relu_of_nonneg hxs,relu_of_nonneg hx.le,he,hT s hsT]
      dsimp only [μ]
      ring
    have hh := h (x+s) y z
    rw [hTarget] at hh
    have hbase := hf d.lU d.lV d.lW d.lT
    change d.base a b c (x+s) y z =
      (d.lU+d.lT*μ)*s+d.base a b c x y z at hbase
    have hg : ∀ j, d.gate a b c j (x+s) y z =
        (d.U j+d.T j*μ)*s+d.gate a b c j x y z := fun j => hf _ _ _ _
    simp_rw [hbase,hg] at hh
    nlinarith only [hh]
  obtain ⟨j,hj,_,_⟩ := exists_negative_active_zero_gate
    (fun j => d.U j+d.T j*μ) (fun j => d.gate a b c j x y z) d.out
    (u-(d.lU+d.lT*μ)) (v-d.base a b c x y z) δ hδ hidentity i hi hgate0
    (by simpa only [ht,zero_mul,add_zero] using hu)
  exact ⟨j,hj⟩

theorem ResidualSystem.exists_negative_gate {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (a b c : ℝ) (habc : a+b+c=0) (hc : c < 0)
    (h : d.Represents a b c) : ∃ j, d.out j < 0 := by
  obtain ⟨i,hi,hu,hv,ht⟩ := d.external_carrier12 a b c habc hc h
  exact d.negative_gate_of_external12 a b c habc hc.ne h i hi hu hv ht

end MaxCaterpillar.Fiber.Count65.StarNonroot
