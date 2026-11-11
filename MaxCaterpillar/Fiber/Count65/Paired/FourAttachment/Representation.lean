import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.OffsetPath

/-! # Functional extraction is realized by actual incoming-row interpolation

The carrier identity is deduced from actual all-input exactness. The source
carrier row is replaced by its forced row through a path of real parameters.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators Frontier Absorption
variable {N m k : ℕ}

lemma oriented_comparisons_sum (A : Fin m → Point N) (β B D : Fin m → ℝ)
    (F : Fin k → Fin m → ℝ) (j : Fin k → ℝ) (flip : Fin k → Bool) (x : Point N)
    (hbal : Paired65.AtomBalance j (fun i => preact A β (F i) 0 x)) :
    (∑ i,j i*relu (if flip i then -(preact A β D 0 x-preact A β (F i) 0 x)
      else preact A β D 0 x-preact A β (F i) 0 x))=
      preact A β B 0 x+relu (preact A β D 0 x)-
        preact A β (carrierRow j flip B D F) 0 x := by
  simp_rw [oriented_relu,mul_sub]
  rw [Finset.sum_sub_distrib,Paired65.relu_identity_of_atomBalance j _ hbal,
    preact_carrierRow]
  simp only [mul_sub,← mul_assoc]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul]
  simp only [orientationWeight]
  ring

/-- Exactness determines the carrier on natural first-layer features, even
when coefficientwise feature injectivity has not been established. -/
theorem orientedCompletion_carrier_forced [NeZero N] (net : ExactFiber N m (k+1))
    (B D : Fin m → ℝ) (F : Fin k → Fin m → ℝ)
    (j : Fin k → ℝ) (flip : Fin k → Bool)
    (hb₂ : net.val.b₂=0) (hb₃ : net.val.b₃=0)
    (hout : net.val.w₃=Fin.cons 1 j)
    (hloc : ∀ i x,preact net.val.W₁ net.val.b₁ (net.val.W₂ i.succ) 0 x=
      if flip i then -(preact net.val.W₁ net.val.b₁ D 0 x-preact net.val.W₁ net.val.b₁ (F i) 0 x)
      else preact net.val.W₁ net.val.b₁ D 0 x-preact net.val.W₁ net.val.b₁ (F i) 0 x)
    (hbal : ∀ x,Paired65.AtomBalance j (fun i => preact net.val.W₁ net.val.b₁ (F i) 0 x))
    (hg : ∀ x,0≤preact net.val.W₁ net.val.b₁ (net.val.W₂ 0) 0 x)
    (hmax : ∀ x,preact net.val.W₁ net.val.b₁ B 0 x+
      relu (preact net.val.W₁ net.val.b₁ D 0 x)=Maximum N x) :
    ∀ x,preact net.val.W₁ net.val.b₁ (net.val.W₂ 0) 0 x=
      preact net.val.W₁ net.val.b₁ (carrierRow j flip B D F) 0 x := by
  intro x
  have he := net.property x
  rw [Network.eval,hb₂,hb₃,hout,Fin.sum_univ_succ] at he
  simp only [Fin.cons_zero,Fin.cons_succ,Pi.zero_apply,one_mul,add_zero] at he
  have hz : (∑ i,j i*relu (preact net.val.W₁ net.val.b₁ (net.val.W₂ i.succ) 0 x))=
      preact net.val.W₁ net.val.b₁ B 0 x+relu (preact net.val.W₁ net.val.b₁ D 0 x)-
        preact net.val.W₁ net.val.b₁ (carrierRow j flip B D F) 0 x := by
    simp_rw [hloc]
    exact oriented_comparisons_sum net.val.W₁ net.val.b₁ B D F j flip x (hbal x)
  have he' : relu (preact net.val.W₁ net.val.b₁ (net.val.W₂ 0) 0 x)+
      (∑ i,j i*relu (preact net.val.W₁ net.val.b₁ (net.val.W₂ i.succ) 0 x))=Maximum N x := by
    simpa only [preact,add_zero] using he
  rw [relu_of_nonneg (hg x),hz,← hmax x] at he'
  linarith only [he']

/-- A source with functionally extracted oriented offsets reaches the actual
forced-row representative. Only incoming second-layer rows move. -/
theorem orientedCompletion_rowReplacement [NeZero N] (net : ExactFiber N m (k+1))
    (B D : Fin m → ℝ) (F : Fin k → Fin m → ℝ)
    (j : Fin k → ℝ) (flip : Fin k → Bool)
    (hb₂ : net.val.b₂=0) (hb₃ : net.val.b₃=0)
    (hout : net.val.w₃=Fin.cons 1 j)
    (hloc : ∀ i x,preact net.val.W₁ net.val.b₁ (net.val.W₂ i.succ) 0 x=
      if flip i then -(preact net.val.W₁ net.val.b₁ D 0 x-preact net.val.W₁ net.val.b₁ (F i) 0 x)
      else preact net.val.W₁ net.val.b₁ D 0 x-preact net.val.W₁ net.val.b₁ (F i) 0 x)
    (hbal : ∀ x,Paired65.AtomBalance j (fun i => preact net.val.W₁ net.val.b₁ (F i) 0 x))
    (hg : ∀ x,0≤preact net.val.W₁ net.val.b₁ (net.val.W₂ 0) 0 x)
    (hmax : ∀ x,preact net.val.W₁ net.val.b₁ B 0 x+
      relu (preact net.val.W₁ net.val.b₁ D 0 x)=Maximum N x) :
    JoinedIn (ExactSet N m (k+1)) net.val
      (withSecondRows net.val
        (Fin.cons (carrierRow j flip B D F) (fun i => if flip i then -(D-F i) else D-F i)) 0) := by
  let rows : Fin (k+1) → Fin m → ℝ := Fin.cons (carrierRow j flip B D F) (fun i => if flip i then -(D-F i) else D-F i)
  have hrow : ∀ i,net.val.w₃ i≠0 → ∀ x,
      preact net.val.W₁ net.val.b₁ (rows i) 0 x=
        preact net.val.W₁ net.val.b₁ (net.val.W₂ i) (net.val.b₂ i) x := by
    intro i _ x
    rw [hb₂]
    simp only [Pi.zero_apply]
    refine Fin.cases ?_ (fun i => ?_) i
    · exact (orientedCompletion_carrier_forced net B D F j flip hb₂ hb₃ hout hloc hbal hg hmax x).symm
    · change preact net.val.W₁ net.val.b₁ (if flip i then -(D-F i) else D-F i) 0 x=
        preact net.val.W₁ net.val.b₁ (net.val.W₂ i.succ) 0 x
      rw [hloc]
      cases hf : flip i
      · simp only [hf,if_false,preact_sub_zero]
      · simp only [hf,if_true]
        have hn : preact net.val.W₁ net.val.b₁ (-(D-F i)) 0 x=
            -preact net.val.W₁ net.val.b₁ (D-F i) 0 x := by
          simpa only [neg_zero] using preact_neg net.val.W₁ net.val.b₁ (D-F i) 0 x
        rw [hn,preact_sub_zero]
  apply JoinedIn.ofLine (continuous_interpolateSecondRows net.val rows 0).continuousOn
    (interpolateSecondRows_zero _ _ _) (interpolateSecondRows_one _ _ _)
  rintro _ ⟨t,_,rfl⟩ x
  rw [interpolateSecondRows_eval net.val rows 0 hrow t x]
  exact net.property x

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
