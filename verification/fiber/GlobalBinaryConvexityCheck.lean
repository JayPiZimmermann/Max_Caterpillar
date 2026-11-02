import MaxCaterpillar.Fiber.BinaryPatterns.GlobalConvexitySigns

set_option autoImplicit false
open BigOperators MaxCaterpillar MaxCaterpillar.Fiber MaxCaterpillar.Fiber.BinaryPatterns
open unitInterval
variable {N h₁ h₂ : ℕ}

example (w v : Fin N → ℝ) (b c : ℝ)
    (h : ∀ x,0 < AffineHalfspace.affineValue w b x ↔ 0 < AffineHalfspace.affineValue v c x)
    (hne : ∃ x,0 < AffineHalfspace.affineValue w b x) :
    ∃ s : ℝ,0 < s ∧ v = (fun j => s*w j) ∧ c = s*b :=
  AffineHalfspace.positive_proportional w v b c h hne

example (w v : Fin N → ℝ) (b c : ℝ)
    (h : ∀ x,0 < AffineHalfspace.affineValue w b x ↔ 0 < AffineHalfspace.affineValue v c x) :
    (∃ s : ℝ,0 < s ∧ v = (fun j => s*w j) ∧ c = s*b) ∨
      (w = 0 ∧ b ≤ 0 ∧ v = 0 ∧ c ≤ 0) :=
  AffineHalfspace.binary_gate_alternatives w v b c h

example (a b : Network N h₁ h₂) (hg : ∀ x,a.firstBinary x = b.firstBinary x) :
    ∃ s : Fin h₁ → ℝ, (∀ j,0 < s j) ∧
      (scaleFirst a s).W₁ = b.W₁ ∧ BiasCompatible (scaleFirst a s) b :=
  exists_first_alignment a b hg

example (a b : Network N h₁ h₂) (hc : BiasCompatible a b)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : Point N) :
    (biasInterpolate a b t).firstHidden x = a.firstHidden x :=
  firstHidden_biasInterpolate a b hc t ht ht1 x

variable [NeZero N]
noncomputable example (a b : ExactFiber N h₁ h₂)
    (hg₁ : ∀ x,a.val.firstBinary x = b.val.firstBinary x)
    (hg₂ : ∀ x,a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k,a.val.w₃ k ≠ 0) (hb : ∀ k,b.val.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) : Path a b :=
  globalSameBinaryPath a b hg₁ hg₂ ha hb hsign

example (a b : ExactFiber N h₁ h₂)
    (hg₁ : ∀ x,a.val.firstBinary x = b.val.firstBinary x)
    (hg₂ : ∀ x,a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k,a.val.w₃ k ≠ 0) (hb : ∀ k,b.val.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) : Joined a b :=
  joined_of_global_binary_maps_output_signs a b hg₁ hg₂ ha hb hsign

example (a b : ExactFiber N h₁ h₂)
    (hg₁ : ∀ x,a.val.firstBinary x = b.val.firstBinary x)
    (hg₂ : ∀ x,a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k,a.val.w₃ k ≠ 0) (hb : ∀ k,b.val.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) :
    ConnectedComponents.mk a = ConnectedComponents.mk b :=
  components_eq_of_global_binary_maps_output_signs a b hg₁ hg₂ ha hb hsign

example (a b : ExactFiber N h₁ h₂)
    (hg₁ : ∀ x,a.val.firstBinary x = b.val.firstBinary x)
    (hg₂ : ∀ x,a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k,a.val.w₃ k ≠ 0) (hb : ∀ k,b.val.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) (t : I) (x : Point N) :
    (globalSameBinaryPath a b hg₁ hg₂ ha hb hsign t).val.firstBinary x = a.val.firstBinary x ∧
      (globalSameBinaryPath a b hg₁ hg₂ ha hb hsign t).val.secondBinary x = a.val.secondBinary x :=
  globalSameBinaryPath_binary a b hg₁ hg₂ ha hb hsign t x

example (a b : ExactFiber N h₁ h₂)
    (hg₁ : ∀ x,a.val.firstBinary x = b.val.firstBinary x)
    (hg₂ : ∀ x,a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k,a.val.w₃ k ≠ 0) (hb : ∀ k,b.val.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) (t : I) (k : Fin h₂) :
    (globalSameBinaryPath a b hg₁ hg₂ ha hb hsign t).val.w₃ k ≠ 0 ∧
      (0 < (globalSameBinaryPath a b hg₁ hg₂ ha hb hsign t).val.w₃ k ↔ 0 < a.val.w₃ k) :=
  globalSameBinaryPath_output a b hg₁ hg₂ ha hb hsign t k

/- A concrete satisfiable instance has genuinely different first-layer matrices. -/
noncomputable def checkFirstScaled : ExactFiber 4 6 3 :=
  scaleFirstFiber (fun _ => 2) (fun _ => by norm_num) zeroExact

example : zeroExact.val.W₁ 0 0 = 1 := by norm_num [zeroExact,net]
example : checkFirstScaled.val.W₁ 0 0 = 2 := by norm_num [checkFirstScaled,scaleFirstFiber,scaleFirst,zeroExact,net]
example : zeroExact.val.W₁ ≠ checkFirstScaled.val.W₁ := by
  intro h
  have hh := congrFun (congrFun h 0) 0
  norm_num [checkFirstScaled,scaleFirstFiber,scaleFirst,zeroExact,net] at hh

example : Joined zeroExact checkFirstScaled := by
  apply joined_of_global_binary_maps_output_signs
  · intro x
    exact (firstBinary_scaleFirst zeroExact.val (fun _ => 2) (fun _ => by norm_num) x).symm
  · intro x
    exact (secondBinary_scaleFirst zeroExact.val (fun _ => 2) (fun _ => by norm_num) x).symm
  · exact output_weights_nonzero 0
  · exact output_weights_nonzero 0
  · intro _k
    rfl

#check @AffineHalfspace.binary_gate_alternatives
#check @joined_of_global_binary_maps_output_signs
#check @globalSameBinaryPath_binary
#check @globalSameBinaryPath_output
#print axioms AffineHalfspace.positive_halfline
#print axioms AffineHalfspace.inactive_row
#print axioms AffineHalfspace.positive_proportional
#print axioms AffineHalfspace.binary_gate_alternatives
#print axioms firstHidden_biasInterpolate
#print axioms eval_biasInterpolate
#print axioms biasPath
#print axioms exists_first_alignment
#print axioms alignmentPath
#print axioms globalSameBinaryPath
#print axioms joined_of_global_binary_maps_output_signs
#print axioms components_eq_of_global_binary_maps_output_signs
#print axioms globalSameBinaryPath_binary
#print axioms globalSameBinaryPath_output
