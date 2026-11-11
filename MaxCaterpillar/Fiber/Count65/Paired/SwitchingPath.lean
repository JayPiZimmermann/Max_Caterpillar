import MaxCaterpillar.Fiber.Count65.Paired.Cancellation
import MaxCaterpillar.Fiber.Count65.Paired.Absorption

/-! # Actual switching-comparison contractions for the nonexceptional orientations

Three normalized comparison atoms of weights (1,1,-1) have offsets F,G,F+G
with F*G=0 on all real inputs. If the first and third orientations agree, F
can contract to zero while all spectator parameters remain fixed. This is the
physical path needed for four of the six nonexceptional orientation triples;
the other two follow by exchanging F and G.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Frontier Absorption
variable {N m r : ℕ}

def orientationIndicator (b : Bool) : ℝ := if b then 1 else 0
private def orientRow (b : Bool) (H : Fin m → ℝ) : Fin m → ℝ :=
  fun j => if b then -H j else H j
private def orientBias (b : Bool) (h : ℝ) : ℝ := if b then -h else h

private lemma preact_orient (A : Fin m → Point N) (β H : Fin m → ℝ)
    (h : ℝ) (b : Bool) (x : Point N) :
    preact A β (orientRow b H) (orientBias b h) x=
      if b then -preact A β H h x else preact A β H h x := by
  cases b
  · change preact A β (fun j => H j) h x=preact A β H h x
    rfl
  · change preact A β (fun j => -H j) (-h) x= -preact A β H h x
    exact preact_neg A β H h x

private lemma preact_three (A : Fin m → Point N) (β D F G : Fin m → ℝ)
    (δ φ γ a b : ℝ) (x : Point N) :
    preact A β (fun j => D j+a*F j+b*G j) (δ+a*φ+b*γ) x=
      preact A β D δ x+a*preact A β F φ x+b*preact A β G γ x := by
  simp only [preact,add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

lemma switching_oriented_identity (D F G : ℝ) (b₁ b₂ b₃ : Bool) (hFG : F*G=0) :
    relu (if b₁ then -(D-F) else D-F)+
      relu (if b₂ then -(D-G) else D-G)-
      relu (if b₃ then -(D-(F+G)) else D-(F+G))=
    relu D-(orientationIndicator b₁+orientationIndicator b₂-orientationIndicator b₃)*D+
      (orientationIndicator b₁-orientationIndicator b₃)*F+(orientationIndicator b₂-orientationIndicator b₃)*G := by
  simp only [oriented_relu]
  have hh := (Paired65.three_relu_offset_identity_iff F G (F+G)).mpr ⟨hFG,rfl⟩ D
  unfold orientationIndicator
  linear_combination hh

noncomputable def switchingTripleNet (A : Fin m → Point N)
    (β D F G : Fin m → ℝ) (δ φ γ θ : ℝ) (b₁ b₂ b₃ : Bool) (t : ℝ) :
    Network N m 3 where
  W₁ := A
  b₁ := β
  W₂ := ![orientRow b₁ (fun j => D j+(t-1)*F j+0*G j),
    orientRow b₂ (fun j => D j+0*F j+(-1)*G j),
    orientRow b₃ (fun j => D j+(t-1)*F j+(-1)*G j)]
  b₂ := ![orientBias b₁ (δ+(t-1)*φ+0*γ),
    orientBias b₂ (δ+0*φ+(-1)*γ),orientBias b₃ (δ+(t-1)*φ+(-1)*γ)]
  w₃ := ![1,1,-1]
  b₃ := θ

lemma switchingTripleNet_eval (A : Fin m → Point N)
    (β D F G : Fin m → ℝ) (δ φ γ θ : ℝ) (b₁ b₂ b₃ : Bool)
    (hFG : ∀ x, preact A β F φ x*preact A β G γ x=0)
    (t : ℝ) (x : Point N) :
    (switchingTripleNet A β D F G δ φ γ θ b₁ b₂ b₃ t).eval x=
      relu (preact A β D δ x)-(orientationIndicator b₁+orientationIndicator b₂-orientationIndicator b₃)*preact A β D δ x+
        (orientationIndicator b₁-orientationIndicator b₃)*((1-t)*preact A β F φ x)+
        (orientationIndicator b₂-orientationIndicator b₃)*preact A β G γ x+θ := by
  simp only [Network.eval,switchingTripleNet,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,
    one_mul,add_zero]
  change relu (preact A β (orientRow b₁ (fun j => D j+(t-1)*F j+0*G j))
      (orientBias b₁ (δ+(t-1)*φ+0*γ)) x)+
    (relu (preact A β (orientRow b₂ (fun j => D j+0*F j+(-1)*G j))
      (orientBias b₂ (δ+0*φ+(-1)*γ)) x)+(-1)*relu (preact A β (orientRow b₃ (fun j => D j+(t-1)*F j+(-1)*G j))
      (orientBias b₃ (δ+(t-1)*φ+(-1)*γ)) x))+θ = _
  simp_rw [preact_orient]
  simp_rw [preact_three]
  simp only [zero_mul,add_zero,neg_one_mul,zero_add]
  have hf : preact A β D δ x+(t-1)*preact A β F φ x=
      preact A β D δ x-(1-t)*preact A β F φ x := by ring
  have hg : preact A β D δ x+-preact A β G γ x=
      preact A β D δ x-preact A β G γ x := by ring
  have hfg : preact A β D δ x+(t-1)*preact A β F φ x+-preact A β G γ x=
      preact A β D δ x-((1-t)*preact A β F φ x+preact A β G γ x) := by ring
  rw [hfg,hf,hg]
  have hh := switching_oriented_identity (preact A β D δ x)
    ((1-t)*preact A β F φ x) (preact A β G γ x) b₁ b₂ b₃
    (by rw [mul_assoc,hFG x,mul_zero])
  linarith only [hh]

theorem continuous_switchingTripleNet (A : Fin m → Point N)
    (β D F G : Fin m → ℝ) (δ φ γ θ : ℝ) (b₁ b₂ b₃ : Bool) :
    Continuous (switchingTripleNet A β D F G δ φ γ θ b₁ b₂ b₃) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,continuous_const,?_,?_,continuous_const,continuous_const⟩
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i
    · change Continuous (fun t : ℝ => if b₁ then -(D j+(t-1)*F j+0*G j)
        else D j+(t-1)*F j+0*G j)
      cases b₁ <;> simp only [if_true,if_false] <;> continuity
    · change Continuous (fun _ : ℝ => if b₂ then -(D j+0*F j+(-1)*G j)
        else D j+0*F j+(-1)*G j)
      exact continuous_const
    · change Continuous (fun t : ℝ => if b₃ then -(D j+(t-1)*F j+(-1)*G j)
        else D j+(t-1)*F j+(-1)*G j)
      cases b₃ <;> simp only [if_true,if_false] <;> continuity
  · apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun t : ℝ => if b₁ then -(δ+(t-1)*φ+0*γ) else δ+(t-1)*φ+0*γ)
      cases b₁ <;> simp only [if_true,if_false] <;> continuity
    · change Continuous (fun _ : ℝ => if b₂ then -(δ+0*φ+(-1)*γ) else δ+0*φ+(-1)*γ)
      exact continuous_const
    · change Continuous (fun t : ℝ => if b₃ then -(δ+(t-1)*φ+(-1)*γ) else δ+(t-1)*φ+(-1)*γ)
      cases b₃ <;> simp only [if_true,if_false] <;> continuity

noncomputable def switchingWithSpectators (A : Fin m → Point N)
    (β D F G : Fin m → ℝ) (δ φ γ θ : ℝ) (b₁ b₂ b₃ : Bool)
    (rows : Fin r → Fin m → ℝ) (biases weights : Fin r → ℝ) (t : ℝ) : Network N m (3+r) :=
  appendSpectators (switchingTripleNet A β D F G δ φ γ θ b₁ b₂ b₃ t) rows biases weights

/-- Contract F to zero when its orientation correction vanishes. The second
comparison offset and every spectator coefficient remain unchanged. -/
theorem switchingWithSpectators_joinedIn_exact [NeZero N]
    (A : Fin m → Point N) (β D F G : Fin m → ℝ) (δ φ γ θ : ℝ) (b₁ b₂ : Bool)
    (rows : Fin r → Fin m → ℝ) (biases weights : Fin r → ℝ)
    (hFG : ∀ x, preact A β F φ x*preact A β G γ x=0)
    (hsource : ∀ x,
      (switchingWithSpectators A β D F G δ φ γ θ b₁ b₂ b₁ rows biases weights 0).eval x=Maximum N x) :
    JoinedIn (ExactSet N m (3+r))
      (switchingWithSpectators A β D F G δ φ γ θ b₁ b₂ b₁ rows biases weights 0)
      (switchingWithSpectators A β D F G δ φ γ θ b₁ b₂ b₁ rows biases weights 1) := by
  have hc := continuous_appendSpectators
    (switchingTripleNet A β D F G δ φ γ θ b₁ b₂ b₁)
    (continuous_switchingTripleNet A β D F G δ φ γ θ b₁ b₂ b₁) rows biases weights
  apply JoinedIn.ofLine hc.continuousOn rfl rfl
  rintro _ ⟨t,_,rfl⟩ x
  have he : (switchingWithSpectators A β D F G δ φ γ θ b₁ b₂ b₁ rows biases weights t).eval x=
      (switchingWithSpectators A β D F G δ φ γ θ b₁ b₂ b₁ rows biases weights 0).eval x := by
    simp only [switchingWithSpectators,appendSpectators_eval,
      switchingTripleNet_eval A β D F G δ φ γ θ b₁ b₂ b₁ hFG,sub_self,zero_mul,add_zero]
    rfl
  exact he.trans (hsource x)

end MaxCaterpillar.Fiber.Count65.Paired
