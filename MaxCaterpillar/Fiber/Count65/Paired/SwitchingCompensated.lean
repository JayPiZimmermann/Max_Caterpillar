import MaxCaterpillar.Fiber.Count65.Paired.SwitchingPath
import MaxCaterpillar.Fiber.Count65.Paired.AffineHeads

/-! # Switching contractions with a signed or split compensating baseline

If the two baseline gates are either a signed pair or the coefficientwise
positive/negative split of one affine readout, every orientation admits the
same offset contraction. This supplies the exceptional orientation cases once
the actual two-gate baseline has been classified and physically normalized.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Frontier Absorption
variable {N m : ℕ}

noncomputable def switchingCompensatedNet (A : Fin m → Point N)
    (β D F G H : Fin m → ℝ) (δ φ γ η θ : ℝ)
    (b₁ b₂ b₃ split : Bool) (t : ℝ) : Network N m 5 :=
  appendSpectators (switchingTripleNet A β D F G δ φ γ θ b₁ b₂ b₃ t)
    (affineHeadRows split (fun j => H j+t*(orientationIndicator b₁-orientationIndicator b₃)*F j))
    (affineHeadBiases split (η+t*(orientationIndicator b₁-orientationIndicator b₃)*φ))
    ![1,-1]

lemma switchingCompensatedNet_eval (A : Fin m → Point N)
    (β D F G H : Fin m → ℝ) (δ φ γ η θ : ℝ)
    (b₁ b₂ b₃ split : Bool)
    (hFG : ∀ x, preact A β F φ x*preact A β G γ x=0)
    (t : ℝ) (x : Point N) :
    (switchingCompensatedNet A β D F G H δ φ γ η θ b₁ b₂ b₃ split t).eval x=
      relu (preact A β D δ x)-
        (orientationIndicator b₁+orientationIndicator b₂-orientationIndicator b₃)*preact A β D δ x+
        (orientationIndicator b₁-orientationIndicator b₃)*preact A β F φ x+
        (orientationIndicator b₂-orientationIndicator b₃)*preact A β G γ x+
        preact A β H η x+θ := by
  rw [switchingCompensatedNet,appendSpectators_eval,
    switchingTripleNet_eval A β D F G δ φ γ θ b₁ b₂ b₃ hFG t x]
  have hh := affineHeadNet_eval A β
    (fun j => H j+t*(orientationIndicator b₁-orientationIndicator b₃)*F j)
    (η+t*(orientationIndicator b₁-orientationIndicator b₃)*φ) split x
  have hs : (∑ j : Fin 2, (![1,-1] : Fin 2 → ℝ) j*
      relu (preact (switchingTripleNet A β D F G δ φ γ θ b₁ b₂ b₃ t).W₁
        (switchingTripleNet A β D F G δ φ γ θ b₁ b₂ b₃ t).b₁
        (affineHeadRows split (fun j => H j+t*(orientationIndicator b₁-orientationIndicator b₃)*F j) j)
        (affineHeadBiases split (η+t*(orientationIndicator b₁-orientationIndicator b₃)*φ) j) x))=
      preact A β H η x+t*(orientationIndicator b₁-orientationIndicator b₃)*preact A β F φ x := by
    rw [preact_addmul] at hh
    simpa only [Network.eval,affineHeadNet,add_zero] using hh
  rw [hs]
  ring

theorem continuous_switchingCompensatedNet (A : Fin m → Point N)
    (β D F G H : Fin m → ℝ) (δ φ γ η θ : ℝ) (b₁ b₂ b₃ split : Bool) :
    Continuous (switchingCompensatedNet A β D F G H δ φ γ η θ b₁ b₂ b₃ split) := by
  have hH : Continuous (fun t : ℝ => fun j => H j+t*(orientationIndicator b₁-orientationIndicator b₃)*F j) := by
    apply continuous_pi
    intro j
    continuity
  have hη : Continuous (fun t : ℝ => η+t*(orientationIndicator b₁-orientationIndicator b₃)*φ) := by continuity
  have hh := continuous_affineHeadNet A β _ _ hH hη split
  rcases (continuous_network_iff _).mp hh with ⟨_,_,hR,hb,_,_⟩
  exact continuous_appendSpectators_varying
    (switchingTripleNet A β D F G δ φ γ θ b₁ b₂ b₃)
    (continuous_switchingTripleNet A β D F G δ φ γ θ b₁ b₂ b₃)
    _ _ _ hR hb continuous_const

/-- The first comparison becomes a global target-knot gate. The baseline
compensation permits all eight orientations, including both exceptional ones. -/
theorem switchingCompensatedNet_joinedIn_exact [NeZero N]
    (A : Fin m → Point N) (β D F G H : Fin m → ℝ) (δ φ γ η θ : ℝ)
    (b₁ b₂ b₃ split : Bool)
    (hFG : ∀ x, preact A β F φ x*preact A β G γ x=0)
    (hsource : ∀ x,
      (switchingCompensatedNet A β D F G H δ φ γ η θ b₁ b₂ b₃ split 0).eval x=Maximum N x) :
    JoinedIn (ExactSet N m 5)
      (switchingCompensatedNet A β D F G H δ φ γ η θ b₁ b₂ b₃ split 0)
      (switchingCompensatedNet A β D F G H δ φ γ η θ b₁ b₂ b₃ split 1) := by
  apply JoinedIn.ofLine
    (continuous_switchingCompensatedNet A β D F G H δ φ γ η θ b₁ b₂ b₃ split).continuousOn rfl rfl
  rintro _ ⟨t,_,rfl⟩ x
  change (switchingCompensatedNet A β D F G H δ φ γ η θ b₁ b₂ b₃ split t).eval x=Maximum N x
  rw [switchingCompensatedNet_eval A β D F G H δ φ γ η θ b₁ b₂ b₃ split hFG t x,
    ← switchingCompensatedNet_eval A β D F G H δ φ γ η θ b₁ b₂ b₃ split hFG 0 x]
  exact hsource x

end MaxCaterpillar.Fiber.Count65.Paired
