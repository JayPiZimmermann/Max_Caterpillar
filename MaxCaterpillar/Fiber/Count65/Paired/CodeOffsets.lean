import MaxCaterpillar.Fiber.Count65.Paired.Extraction

/-! # The support alternative for offsets of actual paired networks

A genuine inverse anchor code turns normalized physical gate offsets into
separable combinations of the four signed code features. The atom bound then
forces the single-coordinate or common-support alternative.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Frontier
variable {m : ℕ}

/-- The ordinary right-inverse equations for a two-coordinate real code. -/
def CodeRightInverse (U R : Fin 2 → Fin 2 → ℝ) : Prop :=
  U 0 0*R 0 0+U 0 1*R 1 0=1 ∧ U 0 0*R 0 1+U 0 1*R 1 1=0 ∧
  U 1 0*R 0 0+U 1 1*R 1 0=0 ∧ U 1 0*R 0 1+U 1 1*R 1 1=1

/-- The determinant and ordinary inverse of the two-coordinate anchor code. -/
def codeDet (U : Fin 2 → Fin 2 → ℝ) : ℝ := U 0 0*U 1 1-U 0 1*U 1 0

noncomputable def inverseCode (U : Fin 2 → Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![U 1 1/codeDet U,-U 0 1/codeDet U],![-U 1 0/codeDet U,U 0 0/codeDet U]]

theorem inverseCode_rightInverse (U : Fin 2 → Fin 2 → ℝ) (h : codeDet U≠0) :
    CodeRightInverse U (inverseCode U) := by
  dsimp only [CodeRightInverse]
  constructor
  · change U 0 0*(U 1 1/codeDet U)+U 0 1*(-U 1 0/codeDet U)=1
    field_simp [h]
    unfold codeDet
    ring
  · constructor
    · change U 0 0*(-U 0 1/codeDet U)+U 0 1*(U 0 0/codeDet U)=0
      field_simp [h]
      ring
    · constructor
      · change U 1 0*(U 1 1/codeDet U)+U 1 1*(-U 1 0/codeDet U)=0
        field_simp [h]
        ring
      · change U 1 0*(-U 0 1/codeDet U)+U 1 1*(U 0 0/codeDet U)=1
        field_simp [h]
        unfold codeDet
        ring

lemma code_rightInverse_eval (U R : Fin 2 → Fin 2 → ℝ)
    (h : CodeRightInverse U R) (u v : ℝ) :
    U 0 0*(R 0 0*u+R 0 1*v)+U 0 1*(R 1 0*u+R 1 1*v)=u ∧
      U 1 0*(R 0 0*u+R 0 1*v)+U 1 1*(R 1 0*u+R 1 1*v)=v := by
  rcases h with ⟨h00,h01,h10,h11⟩
  constructor
  · calc
      _ = (U 0 0*R 0 0+U 0 1*R 1 0)*u+
        (U 0 0*R 0 1+U 0 1*R 1 1)*v := by ring
      _ = u := by rw [h00,h01]; ring
  · calc
      _ = (U 1 0*R 0 0+U 1 1*R 1 0)*u+
        (U 1 0*R 0 1+U 1 1*R 1 1)*v := by ring
      _ = v := by rw [h10,h11]; ring

/-- The coefficient of the signed first code coordinate in a physical knot. -/
noncomputable def offsetLeft (W : Fin m → Fin 6 → ℝ)
    (R : Fin 2 → Fin 2 → ℝ) (s : Bool) (k : Fin m) : ℝ :=
  if s then -(W k 2+W k 0*(R 1 0-R 0 0))/W k 0
    else -(W k 3-W k 0*(R 1 0-R 0 0))/W k 0

/-- The coefficient of the signed second code coordinate in a physical knot. -/
noncomputable def offsetRight (W : Fin m → Fin 6 → ℝ)
    (R : Fin 2 → Fin 2 → ℝ) (s : Bool) (k : Fin m) : ℝ :=
  if s then -(W k 4+W k 0*(R 1 1-R 0 1))/W k 0
    else -(W k 5-W k 0*(R 1 1-R 0 1))/W k 0

lemma physical_offset_separable (W : Fin m → Fin 6 → ℝ)
    (U R : Fin 2 → Fin 2 → ℝ) (hUR : CodeRightInverse U R)
    (k : Fin m) (hα : W k 0≠0) (u v : ℝ) :
    separableOffsets (offsetLeft W R) (offsetRight W R) u v k =
      -(codeIntercept W U (R 0 0*u+R 0 1*v) (R 1 0*u+R 1 1*v) k+
        W k 0*((R 1 0*u+R 1 1*v)-(R 0 0*u+R 0 1*v)))/W k 0 := by
  have hUV := code_rightInverse_eval U R hUR u v
  simp only [separableOffsets, offsetLeft, offsetRight, if_true, if_false,
    codeIntercept, hUV.1, hUV.2]
  field_simp [hα]
  linear_combination -(W k 0*(R 1 0-R 0 0)) * (relu_sub_relu_neg u) -
    (W k 0*(R 1 1-R 0 1)) * (relu_sub_relu_neg v)

/-- Actual all-input exactness supplies the four signed code coefficient
alternative. No presumed scalar atom identity or support pattern is assumed. -/
theorem network_offset_support_dichotomy (net : Network 4 6 m) (hm : m≤5)
    (U R : Fin 2 → Fin 2 → ℝ) (hU : net.W₁=pairedRows U)
    (hUR : CodeRightInverse U R) (hb : net.HasZeroBiases)
    (hnet : ∀ x, net.eval x=Maximum 4 x) :
    let I := EffectiveAtoms net.w₃ (fun k => net.W₂ k 0) (fun k => net.W₂ k 1)
    let a := fun s (k : I) => offsetLeft net.W₂ R s k.val
    let b := fun s (k : I) => offsetRight net.W₂ R s k.val
    (∀ s k, a s k=0) ∨ (∀ s k, b s k=0) ∨
      ∃ (S : Set I) (l n : Bool → ℝ), S.Nonempty ∧
        (∀ s k, a s k=if k∈S then l s else 0) ∧
        (∀ s k, b s k=if k∈S then n s else 0) := by
  let α := fun k => net.W₂ k 0
  let β := fun k => net.W₂ k 1
  let I := EffectiveAtoms net.w₃ α β
  let a := fun s (k : I) => offsetLeft net.W₂ R s k.val
  let b := fun s (k : I) => offsetRight net.W₂ R s k.val
  apply separable_four_relu_dichotomy
    (fun k : I => jumpWeights net.w₃ α β k.val) a b
  · intro k
    exact k.property
  · exact effectiveAtoms_card_le_four 0 0 net.w₃ (codeIntercept net.W₂ U 0 0) α β hm
      (network_two_increment_identity net U hU hb hnet 0 0)
  · intro u v t
    have hh := effective_atomBalance_of_max
      (R 0 0*u+R 0 1*v) (R 1 0*u+R 1 1*v) net.w₃
      (codeIntercept net.W₂ U (R 0 0*u+R 0 1*v) (R 1 0*u+R 1 1*v)) α β
      (network_two_increment_identity net U hU hb hnet _ _)
    have hoff : ∀ k : I, separableOffsets a b u v k =
        -(codeIntercept net.W₂ U (R 0 0*u+R 0 1*v) (R 1 0*u+R 1 1*v) k.val+
          α k.val*((R 1 0*u+R 1 1*v)-(R 0 0*u+R 0 1*v)))/α k.val := by
      intro k
      exact physical_offset_separable net.W₂ U R hUR k.val
        ((jumpWeights_ne_zero_iff net.w₃ α β k.val).mp k.property).2.1 u v
    simp_rw [hoff]
    exact Paired65.relu_identity_of_atomBalance _ _ hh t

end MaxCaterpillar.Fiber.Count65.Paired
