import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointScaled
import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointPositive

/-! # Normalize every nonzero signed baseline coefficient and clear dormant slots -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired

private lemma endpoint_network_ext {a b : Network 4 6 5}
    (hW₁ : a.W₁=b.W₁) (hb₁ : a.b₁=b.b₁) (hW₂ : a.W₂=b.W₂)
    (hb₂ : a.b₂=b.b₂) (hw₃ : a.w₃=b.w₃) (hb₃ : a.b₃=b.b₃) : a=b := by
  apply (networkEquivParameters 4 6 5).injective
  exact Prod.ext hW₁ (Prod.ext hb₁ (Prod.ext hW₂ (Prod.ext hb₂ (Prod.ext hw₃ hb₃))))

lemma scaledEndpointNet_neg (U : Code) (d K : ℝ) (Z : Fin 6 → ℝ) :
    scaledEndpointNet U d (-K) Z=
      permuteHidden (scaledEndpointNet U d K Z) (Equiv.refl _) (Equiv.swap 1 2) := by
  have hW₂ : (scaledEndpointNet U d (-K) Z).W₂=
      (permuteHidden (scaledEndpointNet U d K Z) (Equiv.refl _) (Equiv.swap 1 2)).W₂ := by
    funext k
    fin_cases k
    · change (0 : Fin 6 → ℝ)=0; rfl
    · change (-K)⁻¹ • baselineRow U= -(K⁻¹ • baselineRow U)
      rw [inv_neg,neg_smul]
    · change -((-K)⁻¹ • baselineRow U)=K⁻¹ • baselineRow U
      rw [inv_neg,neg_smul,neg_neg]
    · change comparisonRow U=comparisonRow U; rfl
    · change Z=Z; rfl
  have hw₃ : (scaledEndpointNet U d (-K) Z).w₃=
      (permuteHidden (scaledEndpointNet U d K Z) (Equiv.refl _) (Equiv.swap 1 2)).w₃ := by
    funext k
    fin_cases k
    · change d=d; rfl
    · change -K= -K; rfl
    · change -(-K)=K; exact neg_neg K
    · change (1 : ℝ)=1; rfl
    · change (0 : ℝ)=0; rfl
  exact endpoint_network_ext (a:=scaledEndpointNet U d (-K) Z)
    (b:=permuteHidden (scaledEndpointNet U d K Z) (Equiv.refl _) (Equiv.swap 1 2))
    rfl rfl hW₂ rfl hw₃ rfl

def scaledEndpointOrder : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (![1,2,3,0,4] : Fin 5 → Fin 5) (by decide)

lemma scaledEndpoint_canonical_permutation (U : Code) :
    pairedMinimalNet U=
      permuteHidden (scaledEndpointNet U 0 1 0) (Equiv.refl _) scaledEndpointOrder := by
  have hW₂ : (pairedMinimalNet U).W₂=
      (permuteHidden (scaledEndpointNet U 0 1 0) (Equiv.refl _) scaledEndpointOrder).W₂ := by
    funext k
    fin_cases k
    · change baselineRow U=(1 : ℝ)⁻¹ • baselineRow U
      rw [inv_one,one_smul]
    · change -baselineRow U= -((1 : ℝ)⁻¹ • baselineRow U)
      rw [inv_one,one_smul]
    · change comparisonRow U=comparisonRow U; rfl
    · change (0 : Fin 6 → ℝ)=0; rfl
    · change (0 : Fin 6 → ℝ)=0; rfl
  have hw₃ : (pairedMinimalNet U).w₃=
      (permuteHidden (scaledEndpointNet U 0 1 0) (Equiv.refl _) scaledEndpointOrder).w₃ := by
    funext k
    fin_cases k <;> rfl
  exact endpoint_network_ext (a:=pairedMinimalNet U)
    (b:=permuteHidden (scaledEndpointNet U 0 1 0) (Equiv.refl _) scaledEndpointOrder)
    rfl rfl hW₂ rfl hw₃ rfl

lemma scaledEndpoint_canonical_quotient (U : Code) (hU : codeDet U≠0) :
    quotientMk (scaledEndpointPoint U hU 0 1 (by norm_num) 0)=
      quotientMk (pairedMinimalPoint U hU) := by
  have he : pairedMinimalPoint U hU=
      permuteHiddenFiber (Equiv.refl _) scaledEndpointOrder
        (scaledEndpointPoint U hU 0 1 (by norm_num) 0) :=
    Subtype.ext (scaledEndpoint_canonical_permutation U)
  rw [he]
  exact quotientMk_eq_of_step (SymmetryStep.hidden _ (Equiv.refl _) scaledEndpointOrder)

lemma scaledEndpoint_positive_quotient_joined (U : Code) (hU : codeDet U≠0)
    (d K : ℝ) (hK : 0<K) (Z : Fin 6 → ℝ) :
    Joined (quotientMk (scaledEndpointPoint U hU d K hK.ne' Z))
      (quotientMk (pairedMinimalPoint U hU)) := by
  have hp := (scaledEndpointPositivePath U hU d K hK Z).map quotientMk_continuous
  rw [← scaledEndpoint_canonical_quotient U hU]
  exact ⟨hp⟩

/-- Arbitrary nonzero baseline output scaling, either sign, and arbitrary
silent output/dormant row attach to the actual unit signed paired endpoint. -/
theorem scaledEndpoint_quotient_joined (U : Code) (hU : codeDet U≠0)
    (d K : ℝ) (hK : K≠0) (Z : Fin 6 → ℝ) :
    Joined (quotientMk (scaledEndpointPoint U hU d K hK Z))
      (quotientMk (pairedMinimalPoint U hU)) := by
  rcases lt_or_gt_of_ne hK with hn | hp
  · have hk : 0 < -K := neg_pos.mpr hn
    have he : scaledEndpointPoint U hU d K hK Z=
        permuteHiddenFiber (Equiv.refl _) (Equiv.swap 1 2)
          (scaledEndpointPoint U hU d (-K) hk.ne' Z) := by
      apply Subtype.ext
      simpa only [neg_neg] using scaledEndpointNet_neg U d (-K) Z
    have hq : quotientMk (scaledEndpointPoint U hU d K hK Z)=
        quotientMk (scaledEndpointPoint U hU d (-K) hk.ne' Z) := by
      rw [he]
      exact (quotientMk_eq_of_step (SymmetryStep.hidden _ (Equiv.refl _) (Equiv.swap 1 2))).symm
    rw [hq]
    exact scaledEndpoint_positive_quotient_joined U hU d (-K) hk Z
  · exact scaledEndpoint_positive_quotient_joined U hU d K hp Z

noncomputable def scaledEndpointZeroPoint (U : Code) (hU : codeDet U≠0)
    (d K : ℝ) (hK : K≠0) (Z : Fin 6 → ℝ) : ZeroBiasFiber 4 6 5 :=
  ⟨scaledEndpointPoint U hU d K hK Z,⟨rfl,rfl,rfl⟩⟩

/-- The same attachment in the exact quotient used by zero-bias component
counting. Bias removal maps the exhibited genuine-quotient path continuously. -/
theorem scaledEndpoint_zeroQuotient_joined (U : Code) (hU : codeDet U≠0)
    (d K : ℝ) (hK : K≠0) (Z : Fin 6 → ℝ) :
    Joined (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5)
      (scaledEndpointZeroPoint U hU d K hK Z)) (pairedMinimalZeroQuotient U hU) := by
  have respect : ∀ a b : ExactFiber 4 6 5, (symmetrySetoid 4 6 5).r a b →
      (zeroBiasSymmetrySetoid 4 6 5).r (zeroBiasRetraction a) (zeroBiasRetraction b) := by
    intro a b h
    change (symmetrySetoid 4 6 5).r (zeroBiasFiber a) (zeroBiasFiber b)
    exact zeroBiasFiber_symmetry h
  let erase : SymmetryQuotient 4 6 5 → ZeroBiasSymmetryQuotient 4 6 5 :=
    Quotient.map' zeroBiasRetraction respect
  have hc : Continuous erase := continuous_zeroBiasRetraction.quotient_map' respect
  have hs : erase (quotientMk (scaledEndpointPoint U hU d K hK Z))=
      Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) (scaledEndpointZeroPoint U hU d K hK Z) :=
    congrArg (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5))
      (zeroBiasRetraction_include (scaledEndpointZeroPoint U hU d K hK Z))
  have ht : erase (quotientMk (pairedMinimalPoint U hU))=pairedMinimalZeroQuotient U hU :=
    congrArg (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5))
      (zeroBiasRetraction_include (pairedMinimalZeroPoint U hU))
  have hj := (scaledEndpoint_quotient_joined U hU d K hK Z).somePath.map hc
  rw [hs,ht] at hj
  exact ⟨hj⟩

#print axioms scaledEndpoint_quotient_joined
#print axioms scaledEndpoint_zeroQuotient_joined
end MaxCaterpillar.Fiber.Count65.Paired
