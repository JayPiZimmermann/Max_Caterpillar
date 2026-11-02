import MaxCaterpillar.Fiber.BinaryPatterns.Convexity
import MaxCaterpillar.Fiber.ScalingPaths

/-! # A shared nonzero output-sign vector suffices after positive scaling

A fixed first hidden affine map and a shared full binary second-layer map,
with nonzero output coefficients of matching signs, admit an explicit exact
path: normalize output magnitudes, interpolate, undo normalization.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.BinaryPatterns
open BigOperators Frontier unitInterval
variable {N h₁ h₂ : ℕ}

lemma firstHidden_scaleSecond (a : Network N h₁ h₂) (s : Fin h₂ → ℝ) (x : Point N) :
    (scaleSecond a s).firstHidden x = a.firstHidden x := rfl

lemma secondPreactivation_scaleSecond (a : Network N h₁ h₂) (s : Fin h₂ → ℝ)
    (x : Point N) (k : Fin h₂) :
    (scaleSecond a s).secondPreactivation x k = s k*a.secondPreactivation x k := by
  unfold Network.secondPreactivation
  rw [firstHidden_scaleSecond]
  change (∑ j,s k*a.W₂ k j*a.firstHidden x j)+s k*a.b₂ k = _
  rw [mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positive second-neuron scaling preserves the complete physical binary map. -/
theorem secondBinary_scaleSecond (a : Network N h₁ h₂) (s : Fin h₂ → ℝ)
    (hs : ∀ k,0 < s k) (x : Point N) :
    (scaleSecond a s).secondBinary x = a.secondBinary x := by
  funext k
  have hiff : (scaleSecond a s).secondBinary x k = true ↔ a.secondBinary x k = true := by
    rw [Network.secondBinary_eq_true_iff,Network.secondBinary_eq_true_iff]
    change 0 < (scaleSecond a s).secondPreactivation x k ↔ 0 < a.secondPreactivation x k
    rw [secondPreactivation_scaleSecond]
    constructor
    · intro h
      by_contra hn
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (hs k).le (le_of_not_gt hn))) h
    · exact mul_pos (hs k)
  cases h1 : (scaleSecond a s).secondBinary x k <;>
    cases h2 : a.secondBinary x k <;> simp_all

noncomputable def outputMagnitude (a : Network N h₁ h₂) (k : Fin h₂) : ℝ := |a.w₃ k|

lemma outputMagnitude_pos (a : Network N h₁ h₂) (ha : ∀ k,a.w₃ k ≠ 0) :
    ∀ k,0 < outputMagnitude a k := fun k => abs_pos.mpr (ha k)

lemma normalized_readout_eq (a b : Network N h₁ h₂)
    (ha : ∀ k,a.w₃ k ≠ 0) (hb : ∀ k,b.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.w₃ k ↔ 0 < b.w₃ k) :
    (scaleSecond a (outputMagnitude a)).w₃ =
      (scaleSecond b (outputMagnitude b)).w₃ := by
  funext k
  change a.w₃ k/|a.w₃ k| = b.w₃ k/|b.w₃ k|
  by_cases hpos : 0 < a.w₃ k
  · rw [abs_of_pos hpos,abs_of_pos ((hsign k).mp hpos),div_self (ha k),div_self (hb k)]
  · have hneg : a.w₃ k < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (ha k)
    have hbpos : ¬0 < b.w₃ k := fun h => hpos ((hsign k).mpr h)
    have hbneg : b.w₃ k < 0 := lt_of_le_of_ne (le_of_not_gt hbpos) (hb k)
    rw [abs_of_neg hneg,abs_of_neg hbneg]
    simp only [div_neg,div_self (ha k),div_self (hb k)]

variable [NeZero N]

noncomputable def normalizedFiber (a : ExactFiber N h₁ h₂) (ha : ∀ k,a.val.w₃ k ≠ 0) :
    ExactFiber N h₁ h₂ := scaleSecondFiber (outputMagnitude a.val) (outputMagnitude_pos a.val ha) a

noncomputable def normalizationPath (a : ExactFiber N h₁ h₂) (ha : ∀ k,a.val.w₃ k ≠ 0) :
    Path a (normalizedFiber a ha) :=
  scaleSecondPath (outputMagnitude a.val) (outputMagnitude_pos a.val ha) a

lemma normalized_binary (a : ExactFiber N h₁ h₂) (ha : ∀ k,a.val.w₃ k ≠ 0) (x : Point N) :
    (normalizedFiber a ha).val.secondBinary x = a.val.secondBinary x :=
  secondBinary_scaleSecond a.val (outputMagnitude a.val) (outputMagnitude_pos a.val ha) x

/-- With a fixed first layer, a binary gate map and nonzero output signs determine
one exact-fiber path component. Magnitudes of output coefficients need not agree. -/
noncomputable def sameSignPath (a b : ExactFiber N h₁ h₂)
    (hW : a.val.W₁ = b.val.W₁) (hb : a.val.b₁ = b.val.b₁)
    (hg : ∀ x,a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k,a.val.w₃ k ≠ 0) (hbout : ∀ k,b.val.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) : Path a b :=
  (normalizationPath a ha).trans
    ((straightPath (normalizedFiber a ha) (normalizedFiber b hbout) hW hb
      (normalized_readout_eq a.val b.val ha hbout hsign)
      (fun x => (normalized_binary a ha x).trans ((hg x).trans (normalized_binary b hbout x).symm))).trans
      (normalizationPath b hbout).symm)

lemma normalizationPath_binary (a : ExactFiber N h₁ h₂) (ha : ∀ k,a.val.w₃ k ≠ 0)
    (t : I) (x : Point N) :
    (normalizationPath a ha t).val.secondBinary x = a.val.secondBinary x :=
  secondBinary_scaleSecond a.val
    (scaleSegment (outputMagnitude a.val) t)
    (scaleSegment_pos (outputMagnitude a.val) (outputMagnitude_pos a.val ha) t) x

private lemma all_trans {X : Type*} [TopologicalSpace X] {a b c : X}
    (p : Path a b) (q : Path b c) (P : X → Prop)
    (hp : ∀ t,P (p t)) (hq : ∀ t,P (q t)) (t : I) : P ((p.trans q) t) := by
  rw [Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

/-- The explicit normalized path never changes the given full binary gate map. -/
theorem sameSignPath_binary (a b : ExactFiber N h₁ h₂)
    (hW : a.val.W₁ = b.val.W₁) (hb : a.val.b₁ = b.val.b₁)
    (hg : ∀ x,a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k,a.val.w₃ k ≠ 0) (hbout : ∀ k,b.val.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) (t : I) (x : Point N) :
    (sameSignPath a b hW hb hg ha hbout hsign t).val.secondBinary x = a.val.secondBinary x := by
  unfold sameSignPath
  refine all_trans _ _ (fun n : ExactFiber N h₁ h₂ => n.val.secondBinary x = a.val.secondBinary x) ?_ ?_ t
  · intro u
    exact normalizationPath_binary a ha u x
  · intro u
    refine all_trans _ _ (fun n : ExactFiber N h₁ h₂ => n.val.secondBinary x = a.val.secondBinary x) ?_ ?_ u
    · intro v
      exact (interpolate_secondBinary (normalizedFiber a ha).val (normalizedFiber b hbout).val
        hW hb (fun y => (normalized_binary a ha y).trans ((hg y).trans (normalized_binary b hbout y).symm))
        v v.property.1 v.property.2 x).trans (normalized_binary a ha x)
    · intro v
      change (normalizationPath b hbout (σ v)).val.secondBinary x = a.val.secondBinary x
      exact (normalizationPath_binary b hbout (σ v) x).trans (hg x).symm

theorem joined_of_fixed_first_same_binary_output_signs (a b : ExactFiber N h₁ h₂)
    (hW : a.val.W₁ = b.val.W₁) (hb : a.val.b₁ = b.val.b₁)
    (hg : ∀ x,a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k,a.val.w₃ k ≠ 0) (hbout : ∀ k,b.val.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) : Joined a b :=
  ⟨sameSignPath a b hW hb hg ha hbout hsign⟩


theorem components_eq_of_fixed_first_same_binary_output_signs (a b : ExactFiber N h₁ h₂)
    (hW : a.val.W₁ = b.val.W₁) (hb : a.val.b₁ = b.val.b₁)
    (hg : ∀ x,a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k,a.val.w₃ k ≠ 0) (hbout : ∀ k,b.val.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) :
    ConnectedComponents.mk a = ConnectedComponents.mk b :=
  ConnectedComponents.coe_eq_coe'.mpr
    (pathComponent_subset_component _
      (joined_of_fixed_first_same_binary_output_signs a b hW hb hg ha hbout hsign).symm)

end MaxCaterpillar.Fiber.BinaryPatterns
