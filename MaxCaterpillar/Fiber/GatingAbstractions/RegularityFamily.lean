import MaxCaterpillar.Fiber.Minimal63
import MaxCaterpillar.Fiber.Basic

/-! # A local rational family filling the regular Max4 split fiber

The seventeen parameters are actual free entries of the bias-free network.
No classification or exactness assumption is built into the family.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.GatingAbstractions.RegularityFamily
open BigOperators Frontier

abbrev Params := Fin 17 → ℝ

noncomputable def det (p : Params) : ℝ := p 2 * p 5 - p 3 * p 4
noncomputable def lu (p : Params) : ℝ := p 6 / p 2
noncomputable def lv (p : Params) : ℝ := p 7 / p 5

noncomputable def firstRows (p : Params) : Fin 6 → Fin 4 → ℝ :=
  ![![p 0,-p 0,0,0], ![0,0,p 1,-p 1], ![0,p 2,0,p 3],
    ![0,lu p*p 2,0,lu p*p 3], ![0,p 4,0,p 5],
    ![0,lv p*p 4,0,lv p*p 5]]

noncomputable def features (p : Params) (x : Point 4) : Fin 6 → ℝ :=
  fun j => relu (∑ i, firstRows p j i * x i)

noncomputable def uRead (p : Params) : Fin 6 → ℝ := ![0,0,1,1/lu p,0,0]
noncomputable def vRead (p : Params) : Fin 6 → ℝ := ![0,0,0,0,1,1/lv p]
noncomputable def aRead (p : Params) (j : Fin 6) : ℝ :=
  (p 5 * uRead p j - p 3 * vRead p j) / det p
noncomputable def bRead (p : Params) (j : Fin 6) : ℝ :=
  (-p 4 * uRead p j + p 2 * vRead p j) / det p
noncomputable def aMaxRead (p : Params) (j : Fin 6) : ℝ :=
  aRead p j + if j = 0 then 1 / p 0 else 0
noncomputable def bMaxRead (p : Params) (j : Fin 6) : ℝ :=
  bRead p j + if j = 1 then 1 / p 1 else 0
noncomputable def negativeRow (p : Params) : Fin 6 → ℝ :=
  ![p 11,p 12,p 13,p 14,p 15,p 16]
noncomputable def positiveRow (p : Params) (j : Fin 6) : ℝ :=
  (bMaxRead p j - p 9 * negativeRow p j) / p 8
noncomputable def comparisonRow (p : Params) (j : Fin 6) : ℝ :=
  (aMaxRead p j - bMaxRead p j) / p 10

noncomputable def family (p : Params) : Network 4 6 3 where
  W₁ := firstRows p
  b₁ := 0
  W₂ := ![positiveRow p, negativeRow p, comparisonRow p]
  b₂ := 0
  w₃ := ![p 8,p 9,p 10]
  b₃ := 0

/-- An open, nonvacuous domain of rational exact reconstructions. -/
def Good (p : Params) : Prop :=
  0 < p 0 ∧ 0 < p 1 ∧ p 2 ≠ 0 ∧ p 5 ≠ 0 ∧ det p ≠ 0 ∧
  lu p < 0 ∧ lv p < 0 ∧ 0 < p 8 ∧ p 9 < 0 ∧ 0 < p 10 ∧
  (∀ j, 0 < negativeRow p j) ∧ ∀ j, 0 < positiveRow p j

lemma features_nonneg (p : Params) (x : Point 4) (j : Fin 6) :
    0 ≤ features p x j := relu_nonneg _

lemma features_explicit (p : Params) (x : Point 4) :
    features p x =
      ![relu (p 0*(x 0-x 1)), relu (p 1*(x 2-x 3)),
        relu (p 2*x 1+p 3*x 3), relu (lu p*(p 2*x 1+p 3*x 3)),
        relu (p 4*x 1+p 5*x 3), relu (lv p*(p 4*x 1+p 5*x 3))] := by
  funext j
  fin_cases j <;> norm_num [features, firstRows, Fin.sum_univ_succ] <;> congr 1 <;> ring <;> rfl

private lemma relu_negative_scaled (l t : ℝ) (hl : l < 0) :
    relu (l*t) = (-l)*relu (-t) := by
  have he : l*t=(-l)*(-t) := by ring
  rw [he, relu_mul_pos (neg_pos.mpr hl)]

lemma read_u (p : Params) (x : Point 4) (hu : lu p < 0) :
    (∑ j, uRead p j * features p x j) = p 2*x 1+p 3*x 3 := by
  rw [features_explicit]
  simp only [uRead, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, zero_mul, one_mul, add_zero, zero_add, Fin.sum_univ_zero]
  rw [relu_negative_scaled _ _ hu]
  have hne : lu p ≠ 0 := ne_of_lt hu
  have he : 1 / lu p * (-lu p * relu (-(p 2*x 1+p 3*x 3))) =
      -relu (-(p 2*x 1+p 3*x 3)) := by field_simp; ring
  rw [he]
  exact relu_sub_relu_neg _

lemma read_v (p : Params) (x : Point 4) (hv : lv p < 0) :
    (∑ j, vRead p j * features p x j) = p 4*x 1+p 5*x 3 := by
  rw [features_explicit]
  simp only [vRead, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, zero_mul, one_mul, add_zero, zero_add, Fin.sum_univ_zero]
  rw [relu_negative_scaled _ _ hv]
  have hne : lv p ≠ 0 := ne_of_lt hv
  have he : 1 / lv p * (-lv p * relu (-(p 4*x 1+p 5*x 3))) =
      -relu (-(p 4*x 1+p 5*x 3)) := by field_simp; ring
  rw [he]
  exact relu_sub_relu_neg _

lemma read_a (p : Params) (x : Point 4) (hdet : det p ≠ 0)
    (hu : lu p < 0) (hv : lv p < 0) :
    (∑ j, aRead p j * features p x j) = x 1 := by
  simp only [aRead, div_mul_eq_mul_div, sub_mul, mul_assoc]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    read_u p x hu, read_v p x hv]
  apply (div_eq_iff hdet).mpr
  simp only [det]
  ring

lemma read_b (p : Params) (x : Point 4) (hdet : det p ≠ 0)
    (hu : lu p < 0) (hv : lv p < 0) :
    (∑ j, bRead p j * features p x j) = x 3 := by
  simp only [bRead, div_mul_eq_mul_div, add_mul, mul_assoc]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    read_u p x hu, read_v p x hv]
  apply (div_eq_iff hdet).mpr
  simp only [det]
  ring

lemma read_aMax (p : Params) (x : Point 4) (ha : 0 < p 0)
    (hdet : det p ≠ 0) (hu : lu p < 0) (hv : lv p < 0) :
    (∑ j, aMaxRead p j * features p x j) = max (x 0) (x 1) := by
  simp only [aMaxRead, add_mul, Finset.sum_add_distrib]
  rw [read_a p x hdet hu hv]
  have hs : (∑ j : Fin 6, (if j=0 then 1/p 0 else 0)*features p x j) =
      1/p 0*relu (p 0*(x 0-x 1)) := by
    rw [features_explicit]
    norm_num [Fin.sum_univ_succ]
  rw [hs, relu_mul_pos ha]
  have he : 1/p 0*(p 0*relu (x 0-x 1)) = relu (x 0-x 1) := by
    field_simp [ha.ne']
    ring
  rw [he]
  have := relu_sub_add (x 1) (x 0)
  rw [max_comm] at this
  linarith

lemma read_bMax (p : Params) (x : Point 4) (hb : 0 < p 1)
    (hdet : det p ≠ 0) (hu : lu p < 0) (hv : lv p < 0) :
    (∑ j, bMaxRead p j * features p x j) = max (x 2) (x 3) := by
  simp only [bMaxRead, add_mul, Finset.sum_add_distrib]
  rw [read_b p x hdet hu hv]
  have hs : (∑ j : Fin 6, (if j=1 then 1/p 1 else 0)*features p x j) =
      1/p 1*relu (p 1*(x 2-x 3)) := by
    rw [features_explicit]
    norm_num [Fin.sum_univ_succ]
  rw [hs, relu_mul_pos hb]
  have he : 1/p 1*(p 1*relu (x 2-x 3)) = relu (x 2-x 3) := by
    field_simp [hb.ne']
    ring
  rw [he]
  have := relu_sub_add (x 3) (x 2)
  rw [max_comm] at this
  linarith

lemma family_zeroBiases (p : Params) : (family p).HasZeroBiases := ⟨rfl,rfl,rfl⟩

/-- Every point of the domain is a globally exact physical network. -/
theorem family_exact (p : Params) (hp : Good p) (x : Point 4) :
    (family p).eval x = Maximum 4 x := by
  rcases hp with ⟨ha,hb,hu0,hv0,hd,hu,hv,hs,hneg,ht,hH,hG⟩
  have hGs : 0 ≤ ∑ j, positiveRow p j * features p x j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hG j).le (features_nonneg p x j)
  have hHs : 0 ≤ ∑ j, negativeRow p j * features p x j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hH j).le (features_nonneg p x j)
  have hc : ∀ j, p 8 * positiveRow p j + p 9 * negativeRow p j = bMaxRead p j := by
    intro j
    unfold positiveRow
    field_simp [hs.ne']
    <;> ring
  have hbase : p 8 * (∑ j, positiveRow p j * features p x j) +
      p 9 * (∑ j, negativeRow p j * features p x j) = max (x 2) (x 3) := by
    calc
      _ = ∑ j, (p 8 * positiveRow p j + p 9 * negativeRow p j) * features p x j := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ j, bMaxRead p j * features p x j := by simp only [hc]
      _ = _ := read_bMax p x hb hd hu hv
  have hcomp : p 10 * (∑ j, comparisonRow p j * features p x j) =
      max (x 0) (x 1) - max (x 2) (x 3) := by
    calc
      _ = ∑ j, (aMaxRead p j-bMaxRead p j)*features p x j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        unfold comparisonRow
        field_simp [ht.ne']
        <;> ring
      _ = _ := by
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [read_aMax p x ha hd hu hv, read_bMax p x hb hd hu hv]
  simp only [Network.eval, family, Pi.zero_apply, add_zero, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons]
  change p 8 * relu (∑ j, positiveRow p j * features p x j) +
    p 9 * relu (∑ j, negativeRow p j * features p x j) +
    p 10 * relu (∑ j, comparisonRow p j * features p x j) = Maximum 4 x
  rw [relu_of_nonneg hGs, relu_of_nonneg hHs, hbase, ← relu_mul_pos ht, hcomp,
    Maximum_four]
  have he := relu_sub_add (max (x 2) (x 3)) (max (x 0) (x 1))
  rw [max_comm (max (x 2) (x 3))] at he
  linarith only [he]

/-- Free coordinates of the canonical common-offset family. -/
noncomputable def base (c : ℝ) : Params :=
  fun i => match i.val with
    | 3 | 4 => 0
    | 6 | 7 | 9 => -1
    | 11 => c
    | 16 => 2
    | _ => 1

@[simp] lemma base_0 (c : ℝ) : base c 0 = 1 := rfl
@[simp] lemma base_1 (c : ℝ) : base c 1 = 1 := rfl
@[simp] lemma base_2 (c : ℝ) : base c 2 = 1 := rfl
@[simp] lemma base_3 (c : ℝ) : base c 3 = 0 := rfl
@[simp] lemma base_4 (c : ℝ) : base c 4 = 0 := rfl
@[simp] lemma base_5 (c : ℝ) : base c 5 = 1 := rfl
@[simp] lemma base_6 (c : ℝ) : base c 6 = -1 := rfl
@[simp] lemma base_7 (c : ℝ) : base c 7 = -1 := rfl
@[simp] lemma base_8 (c : ℝ) : base c 8 = 1 := rfl
@[simp] lemma base_9 (c : ℝ) : base c 9 = -1 := rfl
@[simp] lemma base_10 (c : ℝ) : base c 10 = 1 := rfl
@[simp] lemma base_11 (c : ℝ) : base c 11 = c := rfl
@[simp] lemma base_12 (c : ℝ) : base c 12 = 1 := rfl
@[simp] lemma base_13 (c : ℝ) : base c 13 = 1 := rfl
@[simp] lemma base_14 (c : ℝ) : base c 14 = 1 := rfl
@[simp] lemma base_15 (c : ℝ) : base c 15 = 1 := rfl
@[simp] lemma base_16 (c : ℝ) : base c 16 = 2 := rfl

lemma good_base (c : ℝ) (hc : 0 < c) : Good (base c) := by
  refine ⟨by norm_num,by norm_num,by norm_num,
    by norm_num,by norm_num [det],by norm_num [lu],
    by norm_num [lv],by norm_num,by norm_num,by norm_num,?_,?_⟩
  · intro j
    fin_cases j <;> norm_num [negativeRow] <;> exact hc
  · intro j
    fin_cases j <;>
      norm_num [positiveRow,negativeRow,bMaxRead,bRead,uRead,vRead,det,lu,lv,Fin.ext_iff,Fin.coe_ofNat_eq_mod] <;>
      exact hc

end MaxCaterpillar.Fiber.GatingAbstractions.RegularityFamily
