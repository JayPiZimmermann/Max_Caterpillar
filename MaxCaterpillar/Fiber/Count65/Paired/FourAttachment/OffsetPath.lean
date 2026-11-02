import MaxCaterpillar.Fiber.Count65.Paired.Cancellation
import MaxCaterpillar.Fiber.Count65.Paired.RowInterpolation
import MaxCaterpillar.Fiber.Count65.Paired.HalflineCarrier

/-! # Actual parameter paths for oriented offset completions

The first hidden layer stays fixed. The carrier row is defined by its forced
orientation correction; the comparison rows retain all physical slots.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators Frontier Absorption
variable {N m k : ℕ}

noncomputable def orientationWeight (j : Fin k → ℝ) (flip : Fin k → Bool)
    (i : Fin k) : ℝ := j i*(if flip i then 1 else 0)

noncomputable def carrierRow (j : Fin k → ℝ) (flip : Fin k → Bool)
    (B D : Fin m → ℝ) (F : Fin k → Fin m → ℝ) : Fin m → ℝ :=
  fun l => B l+(∑ i, orientationWeight j flip i)*D l-
    ∑ i, orientationWeight j flip i*F i l

noncomputable def orientedCompletionNet (A : Fin m → Point N) (β : Fin m → ℝ)
    (B D : Fin m → ℝ) (F : Fin k → Fin m → ℝ)
    (j : Fin k → ℝ) (flip : Fin k → Bool) : Network N m (k+1) where
  W₁ := A
  b₁ := β
  W₂ := Fin.cons (carrierRow j flip B D F)
    (fun i => if flip i then -(D-F i) else D-F i)
  b₂ := 0
  w₃ := Fin.cons 1 j
  b₃ := 0

lemma preact_sub_zero (A : Fin m → Point N) (β D F : Fin m → ℝ) (x : Point N) :
    preact A β (D-F) 0 x=preact A β D 0 x-preact A β F 0 x := by
  simp only [preact,Pi.sub_apply,sub_mul,Finset.sum_sub_distrib,add_zero]

lemma preact_carrierRow (A : Fin m → Point N) (β B D : Fin m → ℝ)
    (F : Fin k → Fin m → ℝ) (j : Fin k → ℝ) (flip : Fin k → Bool)
    (x : Point N) :
    preact A β (carrierRow j flip B D F) 0 x=
      preact A β B 0 x+(∑ i, orientationWeight j flip i)*preact A β D 0 x-
        ∑ i, orientationWeight j flip i*preact A β (F i) 0 x := by
  simp only [preact,carrierRow,add_zero,sub_mul,add_mul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_mul,mul_assoc]
  simp only [Finset.mul_sum]
  congr 1
  · congr 1
    exact Finset.sum_comm
  · exact Finset.sum_comm

lemma orientedCompletionNet_eval (A : Fin m → Point N) (β B D : Fin m → ℝ)
    (F : Fin k → Fin m → ℝ) (j : Fin k → ℝ) (flip : Fin k → Bool)
    (x : Point N)
    (hbal : Paired65.AtomBalance j (fun i => preact A β (F i) 0 x))
    (hcarrier : 0≤preact A β (carrierRow j flip B D F) 0 x) :
    (orientedCompletionNet A β B D F j flip).eval x=
      preact A β B 0 x+relu (preact A β D 0 x) := by
  have hp (i : Fin k) :
      preact A β (if flip i then -(D-F i) else D-F i) 0 x=
        if flip i then -(preact A β D 0 x-preact A β (F i) 0 x)
          else preact A β D 0 x-preact A β (F i) 0 x := by
    cases hf : flip i
    · simp only [hf,if_false,preact_sub_zero]
    · simp only [hf,if_true]
      have hn : preact A β (-(D-F i)) 0 x = -preact A β (D-F i) 0 x :=
        by simpa only [neg_zero] using preact_neg A β (D-F i) 0 x
      rw [hn,preact_sub_zero]
  have hc := hcarrier
  rw [preact_carrierRow] at hc
  have he := oriented_carrier_identity j (fun i => preact A β (F i) 0 x) flip hbal
    (preact A β B 0 x) (preact A β D 0 x) hc
  change relu (preact A β B 0 x+(∑ i,orientationWeight j flip i)*preact A β D 0 x-
    ∑ i,orientationWeight j flip i*preact A β (F i) 0 x)+_=_ at he
  rw [← preact_carrierRow] at he
  simp_rw [← hp] at he
  rw [Network.eval,Fin.sum_univ_succ]
  simp only [orientedCompletionNet,Fin.cons_zero,Fin.cons_succ,Pi.zero_apply,one_mul,add_zero]
  simpa only [preact,add_zero] using he

theorem continuous_orientedCompletionNet (A : Fin m → Point N) (β B D : Fin m → ℝ)
    (F : ℝ → Fin k → Fin m → ℝ) (hF : Continuous F)
    (j : Fin k → ℝ) (flip : Fin k → Bool) :
    Continuous (fun t => orientedCompletionNet A β B D (F t) j flip) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,continuous_const,?_,continuous_const,continuous_const,continuous_const⟩
  apply continuous_pi
  intro i
  apply continuous_pi
  intro l
  refine Fin.cases ?_ (fun i => ?_) i
  · change Continuous (fun t => B l+(∑ i, orientationWeight j flip i)*D l-
      ∑ i, orientationWeight j flip i*F t i l)
    apply Continuous.sub continuous_const
    apply continuous_finset_sum
    intro i _
    exact continuous_const.mul ((continuous_apply l).comp ((continuous_apply i).comp hF))
  · change Continuous (fun t => (if flip i then -(D-F t i) else D-F t i) l)
    cases hf : flip i <;> simp only [hf,if_true,if_false,Pi.neg_apply,Pi.sub_apply]
    · exact continuous_const.sub ((continuous_apply l).comp ((continuous_apply i).comp hF))
    · exact (continuous_const.sub ((continuous_apply l).comp ((continuous_apply i).comp hF))).neg

/-- A continuous offset deformation gives a continuous path of the actual
incoming weights. Its hypotheses are scalar atom balance and physical carrier
nonnegativity at each time; all first parameters and output weights are fixed. -/
theorem orientedCompletionNet_joinedIn_exact [NeZero N]
    (A : Fin m → Point N) (β B D : Fin m → ℝ)
    (F : ℝ → Fin k → Fin m → ℝ) (hF : Continuous F)
    (j : Fin k → ℝ) (flip : Fin k → Bool)
    (hbal : ∀ t, t∈Set.Icc (0:ℝ) 1 → ∀ x,
      Paired65.AtomBalance j (fun i => preact A β (F t i) 0 x))
    (hcarrier : ∀ t, t∈Set.Icc (0:ℝ) 1 → ∀ x,
      0≤preact A β (carrierRow j flip B D (F t)) 0 x)
    (hexact : ∀ x, preact A β B 0 x+relu (preact A β D 0 x)=Maximum N x) :
    JoinedIn (ExactSet N m (k+1))
      (orientedCompletionNet A β B D (F 0) j flip)
      (orientedCompletionNet A β B D (F 1) j flip) := by
  apply JoinedIn.ofLine (continuous_orientedCompletionNet A β B D F hF j flip).continuousOn rfl rfl
  rintro _ ⟨t,ht,rfl⟩ x
  rw [orientedCompletionNet_eval A β B D (F t) j flip x (hbal t ht x) (hcarrier t ht x)]
  exact hexact x

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
