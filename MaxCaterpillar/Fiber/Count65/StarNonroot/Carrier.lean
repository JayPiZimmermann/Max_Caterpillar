import MaxCaterpillar.Fiber.PositiveKink
import MaxCaterpillar.Fiber.KinkCancellation
import MaxCaterpillar.Fiber.Mixed65.LinearCover

/-! # Facet carriers for three outward roots and a genuine nonroot

The residual identity is quantified on all real inputs. No output sign,
normal form, coefficient alphabet, or first-layer sign cell is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Count65.StarNonroot
open BigOperators MaxCaterpillar.Frontier

noncomputable def form (a b c A B C D x y z : ℝ) : ℝ :=
  A * relu x + B * relu y + C * relu z + D * relu (a*x+b*y+c*z)

noncomputable def target (x y z : ℝ) : ℝ := max (max x y) (relu z)

structure ResidualSystem (ι : Type*) where
  lU : ℝ
  lV : ℝ
  lW : ℝ
  lT : ℝ
  out : ι → ℝ
  U : ι → ℝ
  V : ι → ℝ
  W : ι → ℝ
  T : ι → ℝ

noncomputable def ResidualSystem.base {ι : Type*} (d : ResidualSystem ι)
    (a b c x y z : ℝ) : ℝ := form a b c d.lU d.lV d.lW d.lT x y z

noncomputable def ResidualSystem.gate {ι : Type*} (d : ResidualSystem ι)
    (a b c : ℝ) (i : ι) (x y z : ℝ) : ℝ :=
  form a b c (d.U i) (d.V i) (d.W i) (d.T i) x y z

def ResidualSystem.Represents {ι : Type*} [Fintype ι] (d : ResidualSystem ι)
    (a b c : ℝ) : Prop := ∀ x y z : ℝ,
  target x y z = d.base a b c x y z + ∑ i, d.out i * relu (d.gate a b c i x y z)

private lemma relu_shift_max (s : ℝ) : max (1+s) 1 = 1+relu s := by
  rcases le_total 0 s with hs | hs
  · rw [relu_of_nonneg hs, max_eq_left (by linarith)]
  · rw [relu_of_nonpos hs, max_eq_right (by linarith)]
    ring

private lemma target_facet12 (r s : ℝ) (hr : r < 1) :
    target (1+s) 1 r = 1+relu s := by
  unfold target
  have h : relu r ≤ 1 := max_le (by norm_num) hr.le
  rw [max_eq_left (h.trans (le_max_right _ _)), relu_shift_max]

/-- A nonzero affine intercept keeps its ReLU branch on a genuine interval. -/
theorem relu_affine_near (a b : ℝ) (hb : b ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
      relu (b+a*s) = relu b + (if 0 < b then a else 0)*s := by
  let δ := |b|/(|a|+1)
  have hden : 0 < |a|+1 := by linarith [abs_nonneg a]
  have hd : 0 < δ := div_pos (abs_pos.mpr hb) hden
  have hmul : δ*(|a|+1) = |b| := div_mul_cancel _ hden.ne'
  refine ⟨δ, hd, ?_⟩
  intro s hs
  have hsmall : |a*s| < |b| := by
    rw [abs_mul]
    nlinarith only [hs, hmul, abs_nonneg a, abs_nonneg s, hd]
  rcases lt_or_gt_of_ne hb with hn | hp
  · have hz : b+a*s ≤ 0 := by
      rw [abs_of_neg hn] at hsmall
      linarith only [(abs_lt.mp hsmall).2]
    rw [relu_of_nonpos hz, relu_of_nonpos hn.le, if_neg (not_lt.mpr hn.le)]
    ring
  · have hz : 0 ≤ b+a*s := by
      rw [abs_of_pos hp] at hsmall
      linarith only [(abs_lt.mp hsmall).1]
    rw [relu_of_nonneg hz, relu_of_nonneg hp.le, if_pos hp]

/-- A target facet forces a positive gate with nonzero transverse slope. -/
theorem ResidualSystem.positive_gate12_at {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (a b c r : ℝ) (h : d.Represents a b c)
    (hr : r < 1) (ht : a+b+c*r ≠ 0) :
    ∃ i, 0 < d.out i ∧
      d.U i + d.T i * (if 0 < a+b+c*r then a else 0) ≠ 0 ∧
      d.gate a b c i 1 1 r = 0 := by
  let μ := if 0 < a+b+c*r then a else 0
  obtain ⟨δ0, hδ0, hrelu⟩ := relu_affine_near a (a+b+c*r) ht
  let δ := min 1 δ0
  have hδ : 0 < δ := lt_min (by norm_num) hδ0
  apply exists_positive_active_zero_gate
    (fun i => d.U i+d.T i*μ)
    (fun i => d.gate a b c i 1 1 r) d.out
    (d.lU+d.lT*μ) (d.base a b c 1 1 r-1) δ hδ
  intro s hs
  have hs1 : |s| < 1 := hs.trans_le (min_le_left _ _)
  have hs0 : |s| < δ0 := hs.trans_le (min_le_right _ _)
  have hpos : 0 ≤ 1+s := by linarith only [(abs_lt.mp hs1).1]
  have he : a*(1+s)+b*1+c*r = (a+b+c*r)+a*s := by ring
  have hf : ∀ A B C D : ℝ, form a b c A B C D (1+s) 1 r =
      (A+D*μ)*s+form a b c A B C D 1 1 r := by
    intro A B C D
    unfold form
    rw [relu_of_nonneg hpos, relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1), he,
      hrelu s hs0]
    dsimp only [μ]
    ring
  have hh := h (1+s) 1 r
  rw [target_facet12 r s hr] at hh
  have hbase := hf d.lU d.lV d.lW d.lT
  change d.base a b c (1+s) 1 r =
    (d.lU+d.lT*μ)*s+d.base a b c 1 1 r at hbase
  have hgate : ∀ i, d.gate a b c i (1+s) 1 r =
    (d.U i+d.T i*μ)*s+d.gate a b c i 1 1 r := fun i => hf _ _ _ _
  simp_rw [hbase, hgate] at hh
  linarith only [hh]

/-- A negative third nonroot coefficient forces a carrier independent of that feature. -/
theorem ResidualSystem.external_carrier12 {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (a b c : ℝ) (habc : a+b+c = 0) (hc : c < 0)
    (h : d.Represents a b c) :
    ∃ i, 0 < d.out i ∧ d.U i ≠ 0 ∧ d.V i = -d.U i ∧ d.T i = 0 := by
  have hcover : ∀ r ∈ Set.Ioo (-2:ℝ) (-1),
      ∃ i, (0 < d.out i ∧ d.U i+d.T i*a ≠ 0) ∧
        (d.U i+d.V i-d.T i*c)+(d.T i*c)*r = 0 := by
    intro r hr
    have htpos : 0 < a+b+c*r := by nlinarith only [habc, hc, hr.2]
    obtain ⟨i, hi, hn, hz⟩ := d.positive_gate12_at a b c r h (by linarith [hr.2]) htpos.ne'
    rw [if_pos htpos] at hn
    refine ⟨i, ⟨hi, hn⟩, ?_⟩
    simp only [ResidualSystem.gate, form, mul_one,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonpos (by linarith only [hr.2] : r ≤ 0), relu_of_nonneg htpos.le] at hz
    have hsum : d.T i*(a+b+c) = 0 := by rw [habc, mul_zero]
    nlinarith only [hz, hsum]
  obtain ⟨i, ⟨hi, hn⟩, hA, hB⟩ :=
    Mixed65.exists_zero_affine_of_interval_cover_fintype
      (fun i => d.U i+d.V i-d.T i*c) (fun i => d.T i*c)
      (fun i => 0 < d.out i ∧ d.U i+d.T i*a ≠ 0)
      (by norm_num : (-2:ℝ) < -1) hcover
  have hT : d.T i = 0 := (mul_eq_zero.mp hB).resolve_right hc.ne
  refine ⟨i, hi, ?_, ?_, hT⟩
  · simpa only [hT, zero_mul, add_zero] using hn
  · rw [hT] at hA
    linarith only [hA]

/-- On the positive first-layer cell, a positive third coefficient leaves the
nonroot feature inactive along the target facet. -/
theorem ResidualSystem.interior_carrier12_inactive {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (a b c : ℝ) (habc : a+b+c = 0) (hc : 0 < c)
    (h : d.Represents a b c) :
    ∃ i, 0 < d.out i ∧ d.U i ≠ 0 ∧ d.V i = -d.U i ∧ d.W i = 0 := by
  have hcover : ∀ r ∈ Set.Ioo (0:ℝ) 1,
      ∃ i, (0 < d.out i ∧ d.U i ≠ 0) ∧
        (d.U i+d.V i)+(d.W i)*r = 0 := by
    intro r hr
    have htneg : a+b+c*r < 0 := by nlinarith only [habc, hc, hr.2]
    obtain ⟨i, hi, hn, hz⟩ := d.positive_gate12_at a b c r h hr.2 htneg.ne
    rw [if_neg (not_lt.mpr htneg.le), mul_zero, add_zero] at hn
    refine ⟨i, ⟨hi, hn⟩, ?_⟩
    simp only [ResidualSystem.gate, form, mul_one,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonneg hr.1.le, relu_of_nonpos htneg.le] at hz
    nlinarith only [hz]
  obtain ⟨i, ⟨hi, hn⟩, hA, hB⟩ :=
    Mixed65.exists_zero_affine_of_interval_cover_fintype
      (fun i => d.U i+d.V i) d.W
      (fun i => 0 < d.out i ∧ d.U i ≠ 0)
      (by norm_num : (0:ℝ) < 1) hcover
  exact ⟨i, hi, hn, by linarith only [hA], hB⟩

/-- A negative third coefficient makes the nonroot feature active on the
positive-cell facet; the forced direction is its effective gradient. -/
theorem ResidualSystem.interior_carrier12_active {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (a b c : ℝ) (habc : a+b+c = 0) (hc : c < 0)
    (h : d.Represents a b c) :
    ∃ i, 0 < d.out i ∧ d.U i+d.T i*a ≠ 0 ∧
      d.V i+d.T i*b = -(d.U i+d.T i*a) ∧ d.W i+d.T i*c = 0 := by
  have hcover : ∀ r ∈ Set.Ioo (0:ℝ) 1,
      ∃ i, (0 < d.out i ∧ d.U i+d.T i*a ≠ 0) ∧
        (d.U i+d.V i-d.T i*c)+(d.W i+d.T i*c)*r = 0 := by
    intro r hr
    have htpos : 0 < a+b+c*r := by nlinarith only [habc, hc, hr.2]
    obtain ⟨i, hi, hn, hz⟩ := d.positive_gate12_at a b c r h hr.2 htpos.ne'
    rw [if_pos htpos] at hn
    refine ⟨i, ⟨hi, hn⟩, ?_⟩
    simp only [ResidualSystem.gate, form, mul_one,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonneg hr.1.le, relu_of_nonneg htpos.le] at hz
    have hsum : d.T i*(a+b+c) = 0 := by rw [habc, mul_zero]
    nlinarith only [hz, hsum]
  obtain ⟨i, ⟨hi, hn⟩, hA, hB⟩ :=
    Mixed65.exists_zero_affine_of_interval_cover_fintype
      (fun i => d.U i+d.V i-d.T i*c) (fun i => d.W i+d.T i*c)
      (fun i => 0 < d.out i ∧ d.U i+d.T i*a ≠ 0)
      (by norm_num : (0:ℝ) < 1) hcover
  have hsum : d.T i*(a+b+c) = 0 := by rw [habc, mul_zero]
  exact ⟨i, hi, hn, by nlinarith only [hA, hsum], hB⟩

noncomputable def ResidualSystem.swap23 {ι : Type*} (d : ResidualSystem ι) : ResidualSystem ι :=
  ⟨d.lU, d.lW, d.lV, d.lT, d.out, d.U, d.W, d.V, d.T⟩

noncomputable def ResidualSystem.swap13 {ι : Type*} (d : ResidualSystem ι) : ResidualSystem ι :=
  ⟨d.lW, d.lV, d.lU, d.lT, d.out, d.W, d.V, d.U, d.T⟩

noncomputable def ResidualSystem.swap12 {ι : Type*} (d : ResidualSystem ι) : ResidualSystem ι :=
  ⟨d.lV, d.lU, d.lW, d.lT, d.out, d.V, d.U, d.W, d.T⟩

lemma target_swap23 (x y z : ℝ) : target x z y = target x y z := by
  unfold target relu
  ac_rfl

lemma target_swap13 (x y z : ℝ) : target z y x = target x y z := by
  unfold target relu
  ac_rfl

lemma target_swap12 (x y z : ℝ) : target y x z = target x y z := by
  unfold target
  rw [max_comm y x]

lemma form_swap23 (a b c A B C D x y z : ℝ) :
    form a c b A C B D x y z = form a b c A B C D x z y := by
  unfold form
  have he : a*x+c*y+b*z = a*x+b*z+c*y := by ring
  rw [he]
  ring

lemma form_swap13 (a b c A B C D x y z : ℝ) :
    form c b a C B A D x y z = form a b c A B C D z y x := by
  unfold form
  have he : c*x+b*y+a*z = a*z+b*y+c*x := by ring
  rw [he]
  ring

lemma form_swap12 (a b c A B C D x y z : ℝ) :
    form b a c B A C D x y z = form a b c A B C D y x z := by
  unfold form
  have he : b*x+a*y+c*z = a*y+b*x+c*z := by ring
  rw [he]
  ring

lemma ResidualSystem.represents_swap23 {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (a b c : ℝ) (h : d.Represents a b c) :
    d.swap23.Represents a c b := by
  intro x y z
  simpa only [ResidualSystem.base, ResidualSystem.gate, ResidualSystem.swap23,
    form_swap23, target_swap23] using h x z y

lemma ResidualSystem.represents_swap13 {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (a b c : ℝ) (h : d.Represents a b c) :
    d.swap13.Represents c b a := by
  intro x y z
  simpa only [ResidualSystem.base, ResidualSystem.gate, ResidualSystem.swap13,
    form_swap13, target_swap13] using h z y x

lemma ResidualSystem.represents_swap12 {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (a b c : ℝ) (h : d.Represents a b c) :
    d.swap12.Represents b a c := by
  intro x y z
  simpa only [ResidualSystem.base, ResidualSystem.gate, ResidualSystem.swap12,
    form_swap12, target_swap12] using h y x z

/-- A single strict inactive point for all three outward roots and the nonroot.
A large common offset makes the witness explicit and avoids a genericity argument. -/
theorem exists_all_inactive (a b c : ℝ) (habc : a+b+c=0) (ha : a≠0) :
    ∃ x y z : ℝ, x<0 ∧ y<0 ∧ z<0 ∧ a*x+b*y+c*z<0 := by
  let M : ℝ := 1+|a|+|b|+|c|
  refine ⟨-M-a,-M-b,-M-c,?_,?_,?_,?_⟩
  · dsimp [M]
    linarith only [neg_abs_le_self a,abs_nonneg b,abs_nonneg c]
  · dsimp [M]
    linarith only [neg_abs_le_self b,abs_nonneg a,abs_nonneg c]
  · dsimp [M]
    linarith only [neg_abs_le_self c,abs_nonneg a,abs_nonneg b]
  · have hsum : M*(a+b+c)=0 := by rw [habc,mul_zero]
    nlinarith only [hsum,sq_pos_of_ne_zero a ha,sq_nonneg b,sq_nonneg c]

end MaxCaterpillar.Fiber.Count65.StarNonroot
