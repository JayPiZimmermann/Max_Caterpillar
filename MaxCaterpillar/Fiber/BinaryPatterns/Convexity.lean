import MaxCaterpillar.Fiber.BinaryPatterns.Core

/-!
# A convexity principle for a fixed first hidden layer and physical readout

Binary second-layer gates suffice for straight interpolation when the first
hidden affine map and output weights agree. No equality at zero gates, no
minimum-width hypothesis, and no restriction to a finite input sample is used.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.BinaryPatterns
open BigOperators Frontier unitInterval
variable {N h₁ h₂ : ℕ}

/-- Linear interpolation of the second matrix and its two remaining biases.
The first layer and physical readout are held at the first endpoint. -/
noncomputable def interpolate (a b : Network N h₁ h₂) (t : ℝ) : Network N h₁ h₂ where
  W₁ := a.W₁
  b₁ := a.b₁
  W₂ k j := (1-t)*a.W₂ k j+t*b.W₂ k j
  b₂ k := (1-t)*a.b₂ k+t*b.b₂ k
  w₃ := a.w₃
  b₃ := (1-t)*a.b₃+t*b.b₃

@[simp] theorem interpolate_zero (a b : Network N h₁ h₂) : interpolate a b 0 = a := by
  cases a
  simp [interpolate]

theorem interpolate_one (a b : Network N h₁ h₂)
    (hW : a.W₁ = b.W₁) (hb : a.b₁ = b.b₁) (hw : a.w₃ = b.w₃) :
    interpolate a b 1 = b := by
  cases a
  cases b
  simp only [Network.mk.injEq] at hW hb hw ⊢
  simp only [interpolate, sub_self,zero_mul,one_mul,zero_add]
  cases hW
  cases hb
  cases hw
  rfl

lemma firstHidden_interpolate (a b : Network N h₁ h₂) (t : ℝ) (x : Point N) :
    (interpolate a b t).firstHidden x = a.firstHidden x := rfl

/-- ReLU is affine along a segment whose endpoints have the same binary status. -/
theorem relu_affine_same_binary (u v t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hg : 0 < u ↔ 0 < v) :
    relu ((1-t)*u+t*v) = (1-t)*relu u+t*relu v := by
  by_cases hu : 0 < u
  · have hv := hg.mp hu
    rw [relu_of_nonneg hu.le,relu_of_nonneg hv.le]
    exact relu_of_nonneg (add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hu.le)
      (mul_nonneg ht hv.le))
  · have hv : v ≤ 0 := le_of_not_gt (fun hv => hu (hg.mpr hv))
    have hu' : u ≤ 0 := le_of_not_gt hu
    rw [relu_of_nonpos hu',relu_of_nonpos hv,mul_zero,mul_zero,add_zero]
    exact relu_of_nonpos (add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) hu')
      (mul_nonpos_of_nonneg_of_nonpos ht hv))

lemma affine_positive_iff (u v t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hg : 0 < u ↔ 0 < v) : 0 < (1-t)*u+t*v ↔ 0 < u := by
  by_cases hu : 0 < u
  · have hv := hg.mp hu
    have hp : 0 < (1-t)*u+t*v := by
      by_cases he : t = 1
      · simpa only [he,sub_self,zero_mul,one_mul,zero_add] using hv
      · exact add_pos_of_pos_of_nonneg
          (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht1 he)) hu) (mul_nonneg ht hv.le)
    exact iff_of_true hp hu
  · have hv : v ≤ 0 := le_of_not_gt (fun hv => hu (hg.mpr hv))
    have hn := add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) (le_of_not_gt hu))
      (mul_nonpos_of_nonneg_of_nonpos ht hv)
    exact iff_of_false (not_lt_of_ge hn) hu

lemma preactivation_binary_iff (a b : Network N h₁ h₂)
    (hg : ∀ x,a.secondBinary x = b.secondBinary x) (x : Point N) (k : Fin h₂) :
    0 < a.secondPreactivation x k ↔ 0 < b.secondPreactivation x k := by
  change (0 < (∑ j,a.W₂ k j*a.firstHidden x j)+a.b₂ k) ↔
    (0 < (∑ j,b.W₂ k j*b.firstHidden x j)+b.b₂ k)
  rw [←Network.secondBinary_eq_true_iff,←Network.secondBinary_eq_true_iff,hg x]

lemma secondPreactivation_interpolate (a b : Network N h₁ h₂)
    (hW : a.W₁ = b.W₁) (hb : a.b₁ = b.b₁) (t : ℝ) (x : Point N) (k : Fin h₂) :
    (interpolate a b t).secondPreactivation x k =
      (1-t)*a.secondPreactivation x k+t*b.secondPreactivation x k := by
  have hhidden := Network.firstHidden_congr hW hb x
  unfold Network.secondPreactivation
  rw [firstHidden_interpolate,←hhidden]
  change (∑ j,((1-t)*a.W₂ k j+t*b.W₂ k j)*a.firstHidden x j)+
      ((1-t)*a.b₂ k+t*b.b₂ k) = _
  simp only [add_mul, mul_assoc, Finset.sum_add_distrib,←Finset.mul_sum]
  ring

lemma secondHidden_interpolate (a b : Network N h₁ h₂)
    (hW : a.W₁ = b.W₁) (hb : a.b₁ = b.b₁)
    (hg : ∀ x,a.secondBinary x = b.secondBinary x)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : Point N) (k : Fin h₂) :
    (interpolate a b t).secondHidden x k =
      (1-t)*a.secondHidden x k+t*b.secondHidden x k := by
  change relu ((interpolate a b t).secondPreactivation x k) =
    (1-t)*relu (a.secondPreactivation x k)+t*relu (b.secondPreactivation x k)
  rw [secondPreactivation_interpolate a b hW hb]
  exact relu_affine_same_binary _ _ t ht ht1 (preactivation_binary_iff a b hg x k)

/-- The complete physical binary second-layer map stays unchanged along the segment. -/
theorem interpolate_secondBinary (a b : Network N h₁ h₂)
    (hW : a.W₁ = b.W₁) (hb : a.b₁ = b.b₁)
    (hg : ∀ x,a.secondBinary x = b.secondBinary x)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : Point N) :
    (interpolate a b t).secondBinary x = a.secondBinary x := by
  funext k
  have hiff : (interpolate a b t).secondBinary x k = true ↔ a.secondBinary x k = true := by
    rw [Network.secondBinary_eq_true_iff,Network.secondBinary_eq_true_iff]
    change (0 < (interpolate a b t).secondPreactivation x k) ↔ 0 < a.secondPreactivation x k
    rw [secondPreactivation_interpolate a b hW hb]
    exact affine_positive_iff _ _ t ht ht1 (preactivation_binary_iff a b hg x k)
  cases h1 : (interpolate a b t).secondBinary x k <;>
    cases h2 : a.secondBinary x k <;> simp_all

/-- Realization is affine along the segment, for every real input. -/
theorem eval_interpolate (a b : Network N h₁ h₂)
    (hW : a.W₁ = b.W₁) (hb : a.b₁ = b.b₁) (hw : a.w₃ = b.w₃)
    (hg : ∀ x,a.secondBinary x = b.secondBinary x)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : Point N) :
    (interpolate a b t).eval x = (1-t)*a.eval x+t*b.eval x := by
  rw [Network.eval_eq_secondHidden,Network.eval_eq_secondHidden,
    Network.eval_eq_secondHidden]
  simp only [secondHidden_interpolate a b hW hb hg t ht ht1]
  change (∑ k,a.w₃ k*((1-t)*a.secondHidden x k+t*b.secondHidden x k))+
    ((1-t)*a.b₃+t*b.b₃) = _
  rw [←hw]
  simp only [mul_add,mul_left_comm,Finset.sum_add_distrib,←Finset.mul_sum]
  ring

theorem continuous_interpolate (a b : Network N h₁ h₂) : Continuous (interpolate a b) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,continuous_const,?_,?_,continuous_const,?_⟩
  · apply continuous_pi
    intro k
    apply continuous_pi
    intro j
    exact ((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)
  · apply continuous_pi
    intro k
    exact ((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)
  · exact ((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)

variable [NeZero N]

/-- Fixed first layer and readout turn a shared binary gate map into an exact straight path. -/
noncomputable def straightPath (a b : ExactFiber N h₁ h₂)
    (hW : a.val.W₁ = b.val.W₁) (hb : a.val.b₁ = b.val.b₁) (hw : a.val.w₃ = b.val.w₃)
    (hg : ∀ x,a.val.secondBinary x = b.val.secondBinary x) : Path a b where
  toFun t := ⟨interpolate a.val b.val t,fun x => by
    rw [eval_interpolate a.val b.val hW hb hw hg t t.property.1 t.property.2,
      a.property x,b.property x]
    ring⟩
  continuous_toFun := ((continuous_interpolate a.val b.val).comp continuous_subtype_val).subtype_mk _
  source' := by apply Subtype.ext;exact interpolate_zero a.val b.val
  target' := by apply Subtype.ext;exact interpolate_one a.val b.val hW hb hw

theorem joined_of_fixed_first_readout_same_binary (a b : ExactFiber N h₁ h₂)
    (hW : a.val.W₁ = b.val.W₁) (hb : a.val.b₁ = b.val.b₁) (hw : a.val.w₃ = b.val.w₃)
    (hg : ∀ x,a.val.secondBinary x = b.val.secondBinary x) : Joined a b :=
  ⟨straightPath a b hW hb hw hg⟩

end MaxCaterpillar.Fiber.BinaryPatterns
