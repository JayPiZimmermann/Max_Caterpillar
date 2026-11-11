import MaxCaterpillar.Fiber.BinaryPatterns.GlobalConvexityAlignment

/-!
# A global binary-map and output-sign converse

For ordinary ReLU networks of arbitrary widths and biases, equality of both
labelled global binary hidden maps and of the labelled nonzero output-sign
vectors suffices for a path in the all-input exact fiber. First-layer weights
need not agree. The path rescales first neurons, aligns inactive biases,
normalizes output magnitudes, interpolates, and undoes output normalization.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.BinaryPatterns
open BigOperators Frontier unitInterval
variable {N h₁ h₂ : ℕ}

noncomputable def alignmentScales (a b : Network N h₁ h₂)
    (hg : ∀ x,a.firstBinary x = b.firstBinary x) : Fin h₁ → ℝ :=
  Classical.choose (exists_first_alignment a b hg)

lemma alignmentScales_pos (a b : Network N h₁ h₂)
    (hg : ∀ x,a.firstBinary x = b.firstBinary x) : ∀ j,0 < alignmentScales a b hg j :=
  (Classical.choose_spec (exists_first_alignment a b hg)).1
lemma alignmentScales_rows (a b : Network N h₁ h₂)
    (hg : ∀ x,a.firstBinary x = b.firstBinary x) :
    (scaleFirst a (alignmentScales a b hg)).W₁ = b.W₁ :=
  (Classical.choose_spec (exists_first_alignment a b hg)).2.1
lemma alignmentScales_bias (a b : Network N h₁ h₂)
    (hg : ∀ x,a.firstBinary x = b.firstBinary x) :
    BiasCompatible (scaleFirst a (alignmentScales a b hg)) b :=
  (Classical.choose_spec (exists_first_alignment a b hg)).2.2

variable [NeZero N]
noncomputable def firstScaledFiber (a b : ExactFiber N h₁ h₂)
    (hg : ∀ x,a.val.firstBinary x = b.val.firstBinary x) : ExactFiber N h₁ h₂ :=
  scaleFirstFiber (alignmentScales a.val b.val hg) (alignmentScales_pos a.val b.val hg) a

noncomputable def alignedFiber (a b : ExactFiber N h₁ h₂)
    (hg : ∀ x,a.val.firstBinary x = b.val.firstBinary x) : ExactFiber N h₁ h₂ :=
  biasFiber (firstScaledFiber a b hg) b.val (alignmentScales_bias a.val b.val hg)

lemma alignedFiber_W₁ (a b : ExactFiber N h₁ h₂)
    (hg : ∀ x,a.val.firstBinary x = b.val.firstBinary x) :
    (alignedFiber a b hg).val.W₁ = b.val.W₁ := alignmentScales_rows a.val b.val hg
lemma alignedFiber_b₁ (a b : ExactFiber N h₁ h₂)
    (hg : ∀ x,a.val.firstBinary x = b.val.firstBinary x) :
    (alignedFiber a b hg).val.b₁ = b.val.b₁ :=
  biasFiber_b₁ (firstScaledFiber a b hg) b.val (alignmentScales_bias a.val b.val hg)
lemma alignedFiber_w₃ (a b : ExactFiber N h₁ h₂)
    (hg : ∀ x,a.val.firstBinary x = b.val.firstBinary x) :
    (alignedFiber a b hg).val.w₃ = a.val.w₃ := rfl
lemma alignedFiber_firstBinary (a b : ExactFiber N h₁ h₂)
    (hg : ∀ x,a.val.firstBinary x = b.val.firstBinary x) (x : Point N) :
    (alignedFiber a b hg).val.firstBinary x = a.val.firstBinary x :=
  (firstBinary_biasInterpolate (firstScaledFiber a b hg).val b.val
    (alignmentScales_bias a.val b.val hg) 1 (by norm_num) (by norm_num) x).trans
      (firstBinary_scaleFirst a.val (alignmentScales a.val b.val hg) (alignmentScales_pos a.val b.val hg) x)
lemma alignedFiber_secondBinary (a b : ExactFiber N h₁ h₂)
    (hg : ∀ x,a.val.firstBinary x = b.val.firstBinary x) (x : Point N) :
    (alignedFiber a b hg).val.secondBinary x = a.val.secondBinary x :=
  (biasFiber_secondBinary (firstScaledFiber a b hg) b.val
    (alignmentScales_bias a.val b.val hg) x).trans
      (secondBinary_scaleFirst a.val (alignmentScales a.val b.val hg) (alignmentScales_pos a.val b.val hg) x)

noncomputable def alignmentPath (a b : ExactFiber N h₁ h₂)
    (hg : ∀ x,a.val.firstBinary x = b.val.firstBinary x) : Path a (alignedFiber a b hg) :=
  (scaleFirstPath (alignmentScales a.val b.val hg) (alignmentScales_pos a.val b.val hg) a).trans
    (biasPath (firstScaledFiber a b hg) b.val (alignmentScales_bias a.val b.val hg))

/-- Shared global binary maps in both layers, with matching nonzero output signs,
suffice to join arbitrary exact networks, without fixing the first layer. -/
noncomputable def globalSameBinaryPath (a b : ExactFiber N h₁ h₂)
    (hg₁ : ∀ x,a.val.firstBinary x = b.val.firstBinary x)
    (hg₂ : ∀ x,a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k,a.val.w₃ k ≠ 0) (hb : ∀ k,b.val.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) : Path a b :=
  (alignmentPath a b hg₁).trans
    (sameSignPath (alignedFiber a b hg₁) b (alignedFiber_W₁ a b hg₁) (alignedFiber_b₁ a b hg₁)
      (fun x => (alignedFiber_secondBinary a b hg₁ x).trans (hg₂ x)) ha hb hsign)

theorem joined_of_global_binary_maps_output_signs (a b : ExactFiber N h₁ h₂)
    (hg₁ : ∀ x,a.val.firstBinary x = b.val.firstBinary x)
    (hg₂ : ∀ x,a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k,a.val.w₃ k ≠ 0) (hb : ∀ k,b.val.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) : Joined a b :=
  ⟨globalSameBinaryPath a b hg₁ hg₂ ha hb hsign⟩

theorem components_eq_of_global_binary_maps_output_signs (a b : ExactFiber N h₁ h₂)
    (hg₁ : ∀ x,a.val.firstBinary x = b.val.firstBinary x)
    (hg₂ : ∀ x,a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k,a.val.w₃ k ≠ 0) (hb : ∀ k,b.val.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) :
    ConnectedComponents.mk a = ConnectedComponents.mk b :=
  ConnectedComponents.coe_eq_coe'.mpr (pathComponent_subset_component _
    (joined_of_global_binary_maps_output_signs a b hg₁ hg₂ ha hb hsign).symm)

private lemma global_all_trans {X : Type*} [TopologicalSpace X] {a b c : X}
    (p : Path a b) (q : Path b c) (P : X → Prop)
    (hp : ∀ t,P (p t)) (hq : ∀ t,P (q t)) (t : I) : P ((p.trans q) t) := by
  rw [Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

lemma sameSignPath_firstBinary (a b : ExactFiber N h₁ h₂)
    (hW : a.val.W₁ = b.val.W₁) (hb : a.val.b₁ = b.val.b₁)
    (hg : ∀ x,a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k,a.val.w₃ k ≠ 0) (hbout : ∀ k,b.val.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) (t : I) (x : Point N) :
    (sameSignPath a b hW hb hg ha hbout hsign t).val.firstBinary x = a.val.firstBinary x := by
  unfold sameSignPath
  refine global_all_trans _ _ (fun n : ExactFiber N h₁ h₂ => n.val.firstBinary x = a.val.firstBinary x) ?_ ?_ t
  · intro u
    rfl
  · intro u
    refine global_all_trans _ _ (fun n : ExactFiber N h₁ h₂ => n.val.firstBinary x = a.val.firstBinary x) ?_ ?_ u
    · intro _v
      rfl
    · intro _v
      change b.val.firstBinary x = a.val.firstBinary x
      exact congrArg (fun z : Fin h₁ → ℝ => fun j => decide (0 < z j))
        (Network.firstHidden_congr hW hb x).symm

lemma alignmentPath_binary (a b : ExactFiber N h₁ h₂)
    (hg : ∀ x,a.val.firstBinary x = b.val.firstBinary x) (t : I) (x : Point N) :
    (alignmentPath a b hg t).val.firstBinary x = a.val.firstBinary x ∧
      (alignmentPath a b hg t).val.secondBinary x = a.val.secondBinary x := by
  unfold alignmentPath
  refine global_all_trans _ _ (fun n : ExactFiber N h₁ h₂ =>
    n.val.firstBinary x = a.val.firstBinary x ∧ n.val.secondBinary x = a.val.secondBinary x) ?_ ?_ t
  · intro u
    exact ⟨firstBinary_scaleFirst a.val _
      (scaleSegment_pos _ (alignmentScales_pos a.val b.val hg) u) x,
      secondBinary_scaleFirst a.val _
      (scaleSegment_pos _ (alignmentScales_pos a.val b.val hg) u) x⟩
  · intro u
    exact ⟨(firstBinary_biasInterpolate (firstScaledFiber a b hg).val b.val
      (alignmentScales_bias a.val b.val hg) u u.property.1 u.property.2 x).trans
        (firstBinary_scaleFirst a.val _ (alignmentScales_pos a.val b.val hg) x),
      (secondBinary_biasInterpolate (firstScaledFiber a b hg).val b.val
      (alignmentScales_bias a.val b.val hg) u u.property.1 u.property.2 x).trans
        (secondBinary_scaleFirst a.val _ (alignmentScales_pos a.val b.val hg) x)⟩

/-- Both complete binary maps stay fixed on the entire global exact path. -/
theorem globalSameBinaryPath_binary (a b : ExactFiber N h₁ h₂)
    (hg₁ : ∀ x,a.val.firstBinary x = b.val.firstBinary x)
    (hg₂ : ∀ x,a.val.secondBinary x = b.val.secondBinary x)
    (ha : ∀ k,a.val.w₃ k ≠ 0) (hb : ∀ k,b.val.w₃ k ≠ 0)
    (hsign : ∀ k,0 < a.val.w₃ k ↔ 0 < b.val.w₃ k) (t : I) (x : Point N) :
    (globalSameBinaryPath a b hg₁ hg₂ ha hb hsign t).val.firstBinary x = a.val.firstBinary x ∧
      (globalSameBinaryPath a b hg₁ hg₂ ha hb hsign t).val.secondBinary x = a.val.secondBinary x := by
  unfold globalSameBinaryPath
  refine global_all_trans _ _ (fun n : ExactFiber N h₁ h₂ =>
    n.val.firstBinary x = a.val.firstBinary x ∧ n.val.secondBinary x = a.val.secondBinary x) ?_ ?_ t
  · intro u
    exact alignmentPath_binary a b hg₁ u x
  · intro u
    exact ⟨(sameSignPath_firstBinary (alignedFiber a b hg₁) b
      (alignedFiber_W₁ a b hg₁) (alignedFiber_b₁ a b hg₁)
      (fun y => (alignedFiber_secondBinary a b hg₁ y).trans (hg₂ y)) ha hb hsign u x).trans
        (alignedFiber_firstBinary a b hg₁ x),
      (sameSignPath_binary (alignedFiber a b hg₁) b
      (alignedFiber_W₁ a b hg₁) (alignedFiber_b₁ a b hg₁)
      (fun y => (alignedFiber_secondBinary a b hg₁ y).trans (hg₂ y)) ha hb hsign u x).trans
        (alignedFiber_secondBinary a b hg₁ x)⟩

end MaxCaterpillar.Fiber.BinaryPatterns
