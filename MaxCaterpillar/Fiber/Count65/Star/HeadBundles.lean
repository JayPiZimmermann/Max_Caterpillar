import MaxCaterpillar.Fiber.Count65.Star.HeadComponents

/-! # Head components over the full connected star residual branches

The invariant input change `q = r*q'` identifies every positive-r feature
space with the fixed actual space at r=1. Remainder coefficients are explicit
continuous functions of r and slack. The resulting total reconstruction fiber
has exactly two components for every fixed orientation correction, including
r=1 and the finite slack endpoints.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star
open BigOperators Set MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Star65

/-- Positive dictionary parameter and a closed slack half-line. -/
def residualDomain (cap : ℝ) : Set (ℝ×ℝ) :=
  {p | 0<p.1 ∧ p.1≤1 ∧ p.2≤cap}
abbrev ResidualBase (cap : ℝ) := residualDomain cap

lemma residualDomain_convex (cap : ℝ) : Convex ℝ (residualDomain cap) := by
  intro x hx y hy a b ha hb hab
  change 0<a*x.1+b*y.1 ∧ a*x.1+b*y.1≤1 ∧ a*x.2+b*y.2≤cap
  refine ⟨?_,?_,?_⟩
  · by_cases ha0 : a=0
    · have hb1 : b=1 := by linarith only [hab,ha0]
      simpa only [ha0,hb1,zero_mul,one_mul,zero_add] using hy.1
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hx.1) (mul_nonneg hb hy.1.le)
  · calc
      a*x.1+b*y.1 ≤ a*1+b*1 := add_le_add
        (mul_le_mul_of_nonneg_left hx.2.1 ha) (mul_le_mul_of_nonneg_left hy.2.1 hb)
      _ = 1 := by linarith only [hab]
  · calc
      a*x.2+b*y.2 ≤ a*cap+b*cap := add_le_add
        (mul_le_mul_of_nonneg_left hx.2.2 ha) (mul_le_mul_of_nonneg_left hy.2.2 hb)
      _ = cap := by rw [← add_mul,hab,one_mul]

instance residualBase_pathConnected (cap : ℝ) : PathConnectedSpace (ResidualBase cap) :=
  isPathConnected_iff_pathConnectedSpace.mp
    ((residualDomain_convex cap).isPathConnected ⟨(1,cap),by norm_num [residualDomain]⟩)

/-- First-branch oriented remainder after the invertible input rescaling. -/
noncomputable def branchICoefficients (i j z : ℝ) (p : ResidualBase 0) : Fin 4→ℝ :=
  ![i*(p.val.1-1)+j*(p.val.1*p.val.2)-z*(p.val.1*p.val.2-1),
    j,1-i-j+z,i-z]

/-- Second-branch oriented remainder in the same fixed actual feature space. -/
noncomputable def branchIICoefficients (i j z : ℝ) (p : ResidualBase (-1)) : Fin 4→ℝ :=
  ![i*(p.val.1-1)+j*p.val.1-z*p.val.1,
    i*p.val.2+j-z*(1+p.val.2),1-i-j+z,i]

/-- The dictionary comparison under the invertible actual input rescaling. -/
lemma comparison_rescale {r : ℝ} (hr : 0<r) (q v : ℝ) :
    comparison r (r*q) v=relu (q+v)-(1-r)*relu q := by
  have hq : max 0 (r*q)=r*max 0 q := relu_mul_pos hr q
  have ht : max 0 (r*q+r*v)=r*max 0 (q+v) := by
    rw [← mul_add]
    exact relu_mul_pos hr (q+v)
  unfold comparison
  rw [hq,ht]
  unfold relu
  field_simp [ne_of_gt hr]
  ring

/-- The first coefficient bundle is the actual oriented remainder evaluated
at `q=r*q'`; its feature-space identification is not an assumed recoding. -/
lemma branchI_readout_actual (i j z : ℝ) (p : ResidualBase 0) (q v w : ℝ) :
    (coefficientReadout 1 (branchICoefficients i j z p) : InvariantState→ℝ) (q,v,w)=
      max 0 w+i*(comparison p.val.1 (p.val.1*q) v-max 0 w)+
      j*(max 0 v-max 0 w+p.val.2*max 0 (p.val.1*q))-
      z*(comparison p.val.1 (p.val.1*q) v-max 0 (p.val.1*q)-max 0 w+
        p.val.2*max 0 (p.val.1*q)) := by
  change (i*(p.val.1-1)+j*(p.val.1*p.val.2)-z*(p.val.1*p.val.2-1))*max 0 q+
      j*max 0 v+(1-i-j+z)*max 0 w+(i-z)*max 0 (q+1*v)=_
  rw [comparison_rescale p.property.1,
    show max 0 (p.val.1*q)=p.val.1*max 0 q from relu_mul_pos p.property.1 q]
  simp only [one_mul,relu]
  ring

/-- The same actual input identification for the second residual branch. -/
lemma branchII_readout_actual (i j z : ℝ) (p : ResidualBase (-1)) (q v w : ℝ) :
    (coefficientReadout 1 (branchIICoefficients i j z p) : InvariantState→ℝ) (q,v,w)=
      max 0 w+i*(comparison p.val.1 (p.val.1*q) v-max 0 w+p.val.2*max 0 v)+
      j*(max 0 (p.val.1*q)+max 0 v-max 0 w)-
      z*(max 0 (p.val.1*q)+(1+p.val.2)*max 0 v-max 0 w) := by
  change (i*(p.val.1-1)+j*p.val.1-z*p.val.1)*max 0 q+
      (i*p.val.2+j-z*(1+p.val.2))*max 0 v+(1-i-j+z)*max 0 w+
      i*max 0 (q+1*v)=_
  rw [comparison_rescale p.property.1,
    show max 0 (p.val.1*q)=p.val.1*max 0 q from relu_mul_pos p.property.1 q]
  simp only [one_mul,relu]
  ring

lemma continuous_branchICoefficients (i j z : ℝ) : Continuous (branchICoefficients i j z) := by
  have hr : Continuous (fun p : ResidualBase 0 => p.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hk : Continuous (fun p : ResidualBase 0 => p.val.2) :=
    continuous_snd.comp continuous_subtype_val
  apply continuous_pi
  intro n
  fin_cases n
  · change Continuous (fun p : ResidualBase 0 =>
      i*(p.val.1-1)+j*(p.val.1*p.val.2)-z*(p.val.1*p.val.2-1))
    exact ((continuous_const.mul (hr.sub continuous_const)).add
      (continuous_const.mul (hr.mul hk))).sub
      (continuous_const.mul ((hr.mul hk).sub continuous_const))
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

lemma continuous_branchIICoefficients (i j z : ℝ) : Continuous (branchIICoefficients i j z) := by
  have hr : Continuous (fun p : ResidualBase (-1) => p.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hh : Continuous (fun p : ResidualBase (-1) => p.val.2) :=
    continuous_snd.comp continuous_subtype_val
  apply continuous_pi
  intro n
  fin_cases n
  · change Continuous (fun p : ResidualBase (-1) => i*(p.val.1-1)+j*p.val.1-z*p.val.1)
    exact ((continuous_const.mul (hr.sub continuous_const)).add
      (continuous_const.mul hr)).sub (continuous_const.mul hr)
  · change Continuous (fun p : ResidualBase (-1) => i*p.val.2+j-z*(1+p.val.2))
    exact ((continuous_const.mul hh).add continuous_const).sub
      (continuous_const.mul (continuous_const.add hh))
  · exact continuous_const
  · exact continuous_const

lemma branchI_remainder_nonzero (i j z : ℝ) (p : ResidualBase 0) :
    ∃ x, (coefficientReadout 1 (branchICoefficients i j z p) : InvariantState→ℝ) x≠0 := by
  by_contra hn
  push_neg at hn
  have hz := features_independent (by norm_num : (0:ℝ)<1)
    (branchICoefficients i j z p 0) (branchICoefficients i j z p 1)
    (branchICoefficients i j z p 2) (branchICoefficients i j z p 3) (by
      intro q v w
      exact hn (q,v,w))
  simp only [branchICoefficients,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.tail_cons] at hz
  have hj : j=0 := hz.2.1
  have hw : 1-i-j+z=0 := hz.2.2.1
  have ht : i-z=0 := hz.2.2.2
  linarith only [hj,hw,ht]

lemma branchII_remainder_nonzero (i j z : ℝ) (p : ResidualBase (-1)) :
    ∃ x, (coefficientReadout 1 (branchIICoefficients i j z p) : InvariantState→ℝ) x≠0 := by
  by_contra hn
  push_neg at hn
  have hz := features_independent (by norm_num : (0:ℝ)<1)
    (branchIICoefficients i j z p 0) (branchIICoefficients i j z p 1)
    (branchIICoefficients i j z p 2) (branchIICoefficients i j z p 3) (by
      intro q v w
      exact hn (q,v,w))
  simp only [branchIICoefficients,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.tail_cons] at hz
  have hi : i=0 := hz.2.2.2
  have hjz : j=z := by
    have h0 := hz.1
    rw [hi] at h0
    have he : p.val.1*(j-z)=0 := by nlinarith only [h0]
    have he' := (mul_eq_zero.mp he).resolve_left (ne_of_gt p.property.1)
    linarith only [he']
  have hw : 1-i-j+z=0 := hz.2.2.1
  linarith only [hw,hi,hjz]

private lemma coefficientReadout_nonnegative (a : Fin 4→ℝ) (ha : ∀ n,0≤a n) :
    ∀ x,0≤(coefficientReadout 1 a : InvariantState→ℝ) x := by
  intro x
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (ha 0) (le_max_left _ _))
    (mul_nonneg (ha 1) (le_max_left _ _)))
    (mul_nonneg (ha 2) (le_max_left _ _)))
    (mul_nonneg (ha 3) (le_max_left _ _))

/-- A continuous coefficient remainder supplies a continuous nonnegative
head section, so its full total reconstruction fiber has exactly two components. -/
theorem continuous_coefficient_bundle_has_two_components {β : Type*}
    [TopologicalSpace β] [PathConnectedSpace β] (c : β→Fin 4→ℝ) (hc : Continuous c)
    (hn : ∀ b,∃ x,(coefficientReadout 1 (c b) : InvariantState→ℝ) x≠0) :
    Nonempty (ConnectedComponents (HeadTopology.BundleFiber (featureSpace 1)
      (fun b => coefficientReadout 1 (c b))) ≃ Fin 2) := by
  let A : β→featureSpace 1 := fun b => coefficientReadout 1 (fun n => relu (c b n))
  let B : β→featureSpace 1 := fun b => coefficientReadout 1 (fun n => relu (-c b n))
  have hA : Continuous A := by
    apply (continuous_coefficientReadout 1).comp
    apply continuous_pi
    intro n
    exact continuous_const.max ((continuous_apply n).comp hc)
  have hB : Continuous B := by
    apply (continuous_coefficientReadout 1).comp
    apply continuous_pi
    intro n
    exact continuous_const.max (((continuous_apply n).comp hc).neg)
  have hAB : ∀ b,A b-B b=coefficientReadout 1 (c b) := by
    intro b
    apply Subtype.ext
    funext x
    change (relu (c b 0)*max 0 x.1+relu (c b 1)*max 0 x.2.1+
        relu (c b 2)*max 0 x.2.2+relu (c b 3)*max 0 (x.1+1*x.2.1))-
      (relu (-c b 0)*max 0 x.1+relu (-c b 1)*max 0 x.2.1+
        relu (-c b 2)*max 0 x.2.2+relu (-c b 3)*max 0 (x.1+1*x.2.1))=
      c b 0*max 0 x.1+c b 1*max 0 x.2.1+c b 2*max 0 x.2.2+
        c b 3*max 0 (x.1+1*x.2.1)
    linear_combination (relu_sub_relu_neg (c b 0))*max 0 x.1+
      (relu_sub_relu_neg (c b 1))*max 0 x.2.1+
      (relu_sub_relu_neg (c b 2))*max 0 x.2.2+
      (relu_sub_relu_neg (c b 3))*max 0 (x.1+1*x.2.1)
  exact HeadTopology.has_two_head_bundle_components (featureSpace 1)
    (clippingRigid_featureSpace (by norm_num)) (fun b => coefficientReadout 1 (c b)) A B
    hA hB (fun b => coefficientReadout_nonnegative _ (fun _ => relu_nonneg _))
    (fun b => coefficientReadout_nonnegative _ (fun _ => relu_nonneg _)) hAB hn

/-- Exact head count over the complete first branch, including both endpoints. -/
theorem branchI_total_heads_have_two_components (i j z : ℝ) :
    Nonempty (ConnectedComponents (HeadTopology.BundleFiber (featureSpace 1)
      (fun p : ResidualBase 0 => coefficientReadout 1 (branchICoefficients i j z p))) ≃ Fin 2) :=
  continuous_coefficient_bundle_has_two_components (branchICoefficients i j z)
    (continuous_branchICoefficients i j z) (branchI_remainder_nonzero i j z)

/-- Exact head count over the complete second branch, including both endpoints. -/
theorem branchII_total_heads_have_two_components (i j z : ℝ) :
    Nonempty (ConnectedComponents (HeadTopology.BundleFiber (featureSpace 1)
      (fun p : ResidualBase (-1) => coefficientReadout 1 (branchIICoefficients i j z p))) ≃ Fin 2) :=
  continuous_coefficient_bundle_has_two_components (branchIICoefficients i j z)
    (continuous_branchIICoefficients i j z) (branchII_remainder_nonzero i j z)
end MaxCaterpillar.Fiber.Count65.Star
