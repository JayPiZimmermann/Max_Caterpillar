import MaxCaterpillar.Fiber.BinaryPatterns.GlobalConvexity

/-! # The global binary-map path also preserves every nonzero output sign -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.BinaryPatterns
open unitInterval
variable {N h₁ h₂ : ℕ} [NeZero N]

private lemma all_trans_signs {X : Type*} [TopologicalSpace X] {a b c : X}
    (p : Path a b) (q : Path b c) (P : X → Prop)
    (hp : ∀ t,P (p t)) (hq : ∀ t,P (q t)) (t : I) : P ((p.trans q) t) := by
  rw [Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

private lemma division_status (r d : ℝ) (hr : r ≠ 0) (hd : 0 < d) :
    r/d ≠ 0 ∧ (0 < r/d ↔ 0 < r) := by
  refine ⟨div_ne_zero hr (ne_of_gt hd),?_,fun h => div_pos h hd⟩
  intro h
  have hp := mul_pos h hd
  have he : (r/d)*d = r := by field_simp
  rwa [he] at hp

lemma normalizationPath_output (a : ExactFiber N h₁ h₂) (ha : ∀ k,a.val.w₃ k ≠ 0)
    (t : I) (k : Fin h₂) :
    (normalizationPath a ha t).val.w₃ k ≠ 0 ∧
      (0 < (normalizationPath a ha t).val.w₃ k ↔ 0 < a.val.w₃ k) :=
  division_status (a.val.w₃ k) _ (ha k)
    (scaleSegment_pos (outputMagnitude a.val) (outputMagnitude_pos a.val ha) t k)

theorem sameSignPath_output (a b : ExactFiber N h₁ h₂)
    (hW : a.val.W₁ = b.val.W₁) (hb : a.val.b₁ = b.val.b₁)
    (hg : ∀ x,a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k,a.val.w₃ k ≠ 0) (hbout : ∀ k,b.val.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) (t : I) (k : Fin h₂) :
    (sameSignPath a b hW hb hg ha hbout hsign t).val.w₃ k ≠ 0 ∧
      (0 < (sameSignPath a b hW hb hg ha hbout hsign t).val.w₃ k ↔ 0 < a.val.w₃ k) := by
  unfold sameSignPath
  refine all_trans_signs _ _ (fun n : ExactFiber N h₁ h₂ =>
    n.val.w₃ k ≠ 0 ∧ (0 < n.val.w₃ k ↔ 0 < a.val.w₃ k)) ?_ ?_ t
  · intro u
    exact normalizationPath_output a ha u k
  · intro u
    refine all_trans_signs _ _ (fun n : ExactFiber N h₁ h₂ =>
      n.val.w₃ k ≠ 0 ∧ (0 < n.val.w₃ k ↔ 0 < a.val.w₃ k)) ?_ ?_ u
    · intro _v
      exact division_status (a.val.w₃ k) _ (ha k) (outputMagnitude_pos a.val ha k)
    · intro v
      have hs := normalizationPath_output b hbout (σ v) k
      exact ⟨hs.1,hs.2.trans (hsign k).symm⟩

lemma alignmentPath_readout (a b : ExactFiber N h₁ h₂)
    (hg : ∀ x,a.val.firstBinary x = b.val.firstBinary x) (t : I) :
    (alignmentPath a b hg t).val.w₃ = a.val.w₃ := by
  unfold alignmentPath
  refine all_trans_signs _ _ (fun n : ExactFiber N h₁ h₂ => n.val.w₃ = a.val.w₃) ?_ ?_ t
  · intro _u
    rfl
  · intro _u
    rfl

theorem globalSameBinaryPath_output (a b : ExactFiber N h₁ h₂)
    (hg₁ : ∀ x,a.val.firstBinary x = b.val.firstBinary x)
    (hg₂ : ∀ x,a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k,a.val.w₃ k ≠ 0) (hb : ∀ k,b.val.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) (t : I) (k : Fin h₂) :
    (globalSameBinaryPath a b hg₁ hg₂ ha hb hsign t).val.w₃ k ≠ 0 ∧
      (0 < (globalSameBinaryPath a b hg₁ hg₂ ha hb hsign t).val.w₃ k ↔ 0 < a.val.w₃ k) := by
  unfold globalSameBinaryPath
  refine all_trans_signs _ _ (fun n : ExactFiber N h₁ h₂ =>
    n.val.w₃ k ≠ 0 ∧ (0 < n.val.w₃ k ↔ 0 < a.val.w₃ k)) ?_ ?_ t
  · intro u
    rw [alignmentPath_readout]
    exact ⟨ha k,Iff.rfl⟩
  · intro u
    exact sameSignPath_output (alignedFiber a b hg₁) b
      (alignedFiber_W₁ a b hg₁) (alignedFiber_b₁ a b hg₁)
      (fun y => (alignedFiber_secondBinary a b hg₁ y).trans (hg₂ y)) ha hb hsign u k

end MaxCaterpillar.Fiber.BinaryPatterns
