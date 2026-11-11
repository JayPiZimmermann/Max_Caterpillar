import MaxCaterpillar.Fiber.BinaryPatterns.ConvexityScaling

/-! # Aligning biases of globally inactive first hidden neurons -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.BinaryPatterns
open BigOperators Frontier unitInterval
variable {N h₁ h₂ : ℕ}

/-- First biases already agree, except possibly at globally inactive zero rows. -/
def BiasCompatible (a b : Network N h₁ h₂) : Prop :=
  ∀ j,a.b₁ j = b.b₁ j ∨ (a.W₁ j = 0 ∧ a.b₁ j ≤ 0 ∧ b.b₁ j ≤ 0)

noncomputable def biasInterpolate (a b : Network N h₁ h₂) (t : ℝ) : Network N h₁ h₂ :=
  ⟨a.W₁,fun j => (1-t)*a.b₁ j+t*b.b₁ j,a.W₂,a.b₂,a.w₃,a.b₃⟩

lemma biasInterpolate_zero (a b : Network N h₁ h₂) : biasInterpolate a b 0 = a := by
  cases a
  simp [biasInterpolate]

lemma firstHidden_biasInterpolate (a b : Network N h₁ h₂) (hc : BiasCompatible a b)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : Point N) :
    (biasInterpolate a b t).firstHidden x = a.firstHidden x := by
  funext j
  change relu ((∑ i,a.W₁ j i*x i)+((1-t)*a.b₁ j+t*b.b₁ j)) =
    relu ((∑ i,a.W₁ j i*x i)+a.b₁ j)
  rcases hc j with h | ⟨hw,ha,hb⟩
  · rw [←h]
    congr 1
    ring
  · have hn : (1-t)*a.b₁ j+t*b.b₁ j ≤ 0 := add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) ha)
      (mul_nonpos_of_nonneg_of_nonpos ht hb)
    simp only [hw,Pi.zero_apply,zero_mul,Finset.sum_const_zero,zero_add]
    rw [relu_of_nonpos hn,relu_of_nonpos ha]

lemma secondHidden_biasInterpolate (a b : Network N h₁ h₂) (hc : BiasCompatible a b)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : Point N) :
    (biasInterpolate a b t).secondHidden x = a.secondHidden x := by
  unfold Network.secondHidden
  rw [firstHidden_biasInterpolate a b hc t ht ht1]
  rfl

lemma eval_biasInterpolate (a b : Network N h₁ h₂) (hc : BiasCompatible a b)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : Point N) :
    (biasInterpolate a b t).eval x = a.eval x := by
  rw [Network.eval_eq_secondHidden,Network.eval_eq_secondHidden,
    secondHidden_biasInterpolate a b hc t ht ht1]
  rfl

lemma firstBinary_biasInterpolate (a b : Network N h₁ h₂) (hc : BiasCompatible a b)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : Point N) :
    (biasInterpolate a b t).firstBinary x = a.firstBinary x :=
  congrArg (fun z : Fin h₁ → ℝ => fun j => decide (0 < z j))
    (firstHidden_biasInterpolate a b hc t ht ht1 x)

lemma secondBinary_biasInterpolate (a b : Network N h₁ h₂) (hc : BiasCompatible a b)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : Point N) :
    (biasInterpolate a b t).secondBinary x = a.secondBinary x :=
  congrArg (fun z : Fin h₂ → ℝ => fun k => decide (0 < z k))
    (secondHidden_biasInterpolate a b hc t ht ht1 x)

theorem continuous_biasInterpolate (a b : Network N h₁ h₂) : Continuous (biasInterpolate a b) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,?_,continuous_const,continuous_const,continuous_const,continuous_const⟩
  apply continuous_pi
  intro j
  exact ((continuous_const.sub continuous_id).mul continuous_const).add
    (continuous_id.mul continuous_const)

variable [NeZero N]
noncomputable def biasFiber (a : ExactFiber N h₁ h₂) (b : Network N h₁ h₂)
    (hc : BiasCompatible a.val b) : ExactFiber N h₁ h₂ :=
  ⟨biasInterpolate a.val b 1,fun x =>
    (eval_biasInterpolate a.val b hc 1 (by norm_num) (by norm_num) x).trans (a.property x)⟩

noncomputable def biasPath (a : ExactFiber N h₁ h₂) (b : Network N h₁ h₂)
    (hc : BiasCompatible a.val b) : Path a (biasFiber a b hc) where
  toFun t := ⟨biasInterpolate a.val b t,fun x =>
    (eval_biasInterpolate a.val b hc t t.property.1 t.property.2 x).trans (a.property x)⟩
  continuous_toFun := ((continuous_biasInterpolate a.val b).comp continuous_subtype_val).subtype_mk _
  source' := by apply Subtype.ext;exact biasInterpolate_zero a.val b
  target' := by apply Subtype.ext;rfl

lemma biasFiber_W₁ (a : ExactFiber N h₁ h₂) (b : Network N h₁ h₂)
    (hc : BiasCompatible a.val b) : (biasFiber a b hc).val.W₁ = a.val.W₁ := rfl
lemma biasFiber_b₁ (a : ExactFiber N h₁ h₂) (b : Network N h₁ h₂)
    (hc : BiasCompatible a.val b) : (biasFiber a b hc).val.b₁ = b.b₁ := by
  funext j
  change (1-(1:ℝ))*a.val.b₁ j+1*b.b₁ j = b.b₁ j
  ring
lemma biasFiber_w₃ (a : ExactFiber N h₁ h₂) (b : Network N h₁ h₂)
    (hc : BiasCompatible a.val b) : (biasFiber a b hc).val.w₃ = a.val.w₃ := rfl
lemma biasFiber_secondBinary (a : ExactFiber N h₁ h₂) (b : Network N h₁ h₂)
    (hc : BiasCompatible a.val b) (x : Point N) :
    (biasFiber a b hc).val.secondBinary x = a.val.secondBinary x :=
  secondBinary_biasInterpolate a.val b hc 1 (by norm_num) (by norm_num) x

end MaxCaterpillar.Fiber.BinaryPatterns
