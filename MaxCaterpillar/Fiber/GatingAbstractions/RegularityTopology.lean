import MaxCaterpillar.Fiber.GatingAbstractions.RegularityCoordinates
import MaxCaterpillar.Fiber.Basic

/-! # The actual topology of all bias-free network weights

The forty-five raw coordinates include every first-hidden-layer weight,
every second-hidden-layer weight, and every output weight. Their ordinary
real topology is exactly the subspace topology of the existing six-array
network model with zero biases. No first-layer directions are fixed here.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.GatingAbstractions

noncomputable section

/-- Pointwise continuity in the actual network topology, checked one array at
a time. The generic statement avoids repeatedly expanding rational families. -/
theorem continuousAt_network_of_arrays {X : Type*} [TopologicalSpace X]
    {N h₁ h₂ : ℕ} (f : X → Network N h₁ h₂) (p : X)
    (hW₁ : ContinuousAt (fun q => (f q).W₁) p)
    (hb₁ : ContinuousAt (fun q => (f q).b₁) p)
    (hW₂ : ContinuousAt (fun q => (f q).W₂) p)
    (hb₂ : ContinuousAt (fun q => (f q).b₂) p)
    (hw₃ : ContinuousAt (fun q => (f q).w₃) p)
    (hb₃ : ContinuousAt (fun q => (f q).b₃) p) : ContinuousAt f p := by
  apply ((networkHomeomorphParameters N h₁ h₂).comp_continuousAt_iff f p).mp
  exact hW₁.prod (hb₁.prod (hW₂.prod (hb₂.prod (hw₃.prod hb₃))))

theorem continuous_fromRaw : Continuous (fromRaw : Raw → Network 4 6 3) := by
  apply (continuous_network_iff _).mpr
  refine ⟨?_, continuous_const, ?_, continuous_const, ?_, continuous_const⟩
  · apply continuous_pi
    intro j
    fin_cases j <;> apply continuous_pi <;> intro i <;> fin_cases i <;>
      exact continuous_apply _
  · apply continuous_pi
    intro k
    fin_cases k <;> apply continuous_pi <;> intro j <;> fin_cases j <;>
      exact continuous_apply _
  · apply continuous_pi
    intro k
    fin_cases k <;> exact continuous_apply _

theorem continuous_toRaw : Continuous (toRaw : Network 4 6 3 → Raw) := by
  apply continuous_pi
  intro i
  fin_cases i <;>
    simp only [toRaw, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.head_cons, Matrix.tail_cons] <;> first
    | exact (continuous_apply _).comp ((continuous_apply _).comp continuous_W₁)
    | exact (continuous_apply _).comp ((continuous_apply _).comp continuous_W₂)
    | exact (continuous_apply _).comp continuous_w₃

/-- The raw forty-five-dimensional space is precisely the complete bias-free
physical network parameter space, with its actual subspace topology. -/
noncomputable def rawHomeomorphZeroBias :
    Raw ≃ₜ {net : Network 4 6 3 // net.HasZeroBiases} where
  toFun p := ⟨fromRaw p, fromRaw_zeroBiases p⟩
  invFun net := toRaw net.val
  left_inv p := toRaw_fromRaw p
  right_inv net := Subtype.ext (fromRaw_toRaw net.val net.property)
  continuous_toFun := continuous_fromRaw.subtype_mk (fun p => fromRaw_zeroBiases p)
  continuous_invFun := continuous_toRaw.comp continuous_subtype_val

/-- The entire all-input bias-free exact fiber, with no row-direction restriction. -/
def RawExactSet : Set Raw :=
  {p | ∀ x, (fromRaw p).eval x = Maximum 4 x}

/-- Restricting the coordinate homeomorphism gives exactly the physical
all-input exact fiber with zero biases. -/
noncomputable def rawHomeomorphZeroBiasExact :
    ↥RawExactSet ≃ₜ {net : ExactFiber 4 6 3 // net.val.HasZeroBiases} where
  toFun p := ⟨⟨fromRaw p.val, p.property⟩, fromRaw_zeroBiases p.val⟩
  invFun net := ⟨toRaw net.val.val, by
    change ∀ x, (fromRaw (toRaw net.val.val)).eval x = Maximum 4 x
    rw [fromRaw_toRaw net.val.val net.property]
    exact net.val.property⟩
  left_inv p := Subtype.ext (toRaw_fromRaw p.val)
  right_inv net := Subtype.ext (Subtype.ext (fromRaw_toRaw net.val.val net.property))
  continuous_toFun :=
    ((continuous_fromRaw.comp continuous_subtype_val).subtype_mk
      (fun p : ↥RawExactSet => p.property)).subtype_mk
      (fun p : ↥RawExactSet => fromRaw_zeroBiases p.val)
  continuous_invFun :=
    (continuous_toRaw.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

#print axioms rawHomeomorphZeroBias
#print axioms rawHomeomorphZeroBiasExact


end
end MaxCaterpillar.Fiber.GatingAbstractions
