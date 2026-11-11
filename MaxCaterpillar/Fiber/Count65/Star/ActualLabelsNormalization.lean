import MaxCaterpillar.Fiber.Count65.Star.ActualLabelsContinuity

/-! # Actual star labels before output normalization -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.ActualStarLabels
open Set Function Star Star65 PhysicalExtraction MaxCaterpillar.Frontier

abbrev RawSlice := {p : ℝ × Network 4 6 5 //
  0 < p.1 ∧ p.1 ≤ 1 ∧ p.2.W₁=firstRows p.1 ∧ (∀ x,p.2.eval x=Maximum 4 x)}

lemma raw_outputs_nonzero (p : RawSlice) : ∀ i,p.val.2.w₃ i ≠ 0 :=
  (physical_output_sign_counts p.val.2 p.val.1 p.property.1
    p.property.2.1 p.property.2.2.1 p.property.2.2.2).2.2

noncomputable def normalizePhysical (p : RawSlice) : Slice :=
  ⟨(p.val.1,normalizeSecond p.val.2),p.property.1,p.property.2.1,p.property.2.2.1,
    (fun x => (normalizeSecond_eval p.val.2 (raw_outputs_nonzero p) x).trans
      (p.property.2.2.2 x)),normalizeSecond_unit_outputs p.val.2 (raw_outputs_nonzero p)⟩

/-- Normalization is continuous on the full actual star physical domain;
output nonvanishing is derived from exactness, rather than imposed. -/
theorem continuous_normalizePhysical : Continuous normalizePhysical := by
  have hn : Continuous (fun p : RawSlice => p.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have ho (i : Fin 5) : Continuous (fun p : RawSlice => p.val.2.w₃ i) :=
    (continuous_apply i).comp (continuous_w₃.comp hn)
  have hc (i : Fin 5) (j : Fin 6) : Continuous (fun p : RawSlice => p.val.2.W₂ i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_W₂.comp hn))
  have hb (i : Fin 5) : Continuous (fun p : RawSlice => p.val.2.b₂ i) :=
    (continuous_apply i).comp (continuous_b₂.comp hn)
  have hnet : Continuous (fun p : RawSlice => normalizeSecond p.val.2) := by
    apply (continuous_network_iff _).mpr
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · change Continuous (fun p : RawSlice => p.val.2.W₁)
      exact continuous_W₁.comp hn
    · change Continuous (fun p : RawSlice => p.val.2.b₁)
      exact continuous_b₁.comp hn
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact (ho i).abs.mul (hc i j)
    · apply continuous_pi
      intro i
      exact (ho i).abs.mul (hb i)
    · apply continuous_pi
      intro i
      exact (ho i).div (ho i).abs (fun p => (abs_pos.mpr (raw_outputs_nonzero p i)).ne')
    · change Continuous (fun p : RawSlice => p.val.2.b₃)
      exact continuous_b₃.comp hn
  exact ((continuous_fst.comp continuous_subtype_val).prod_mk hnet).subtype_mk _

noncomputable def rawComponentLabel (p : RawSlice) : NonpairedLabel :=
  componentLabel (normalizePhysical p)

/-- A continuous 32-valued invariant on actual networks with the complete
canonical star first matrix, with arbitrary original biases and suffix. -/
theorem continuous_rawComponentLabel : Continuous rawComponentLabel :=
  continuous_componentLabel.comp continuous_normalizePhysical

noncomputable def rawComponentLabel32 (p : RawSlice) : Fin 32 :=
  componentLabel32 (normalizePhysical p)
theorem continuous_rawComponentLabel32 : Continuous rawComponentLabel32 :=
  continuous_componentLabel32.comp continuous_normalizePhysical

/-- The entire actual endpoint slice, including arbitrary original biases. -/
abbrev EndpointSlice := {net : Network 4 6 5 //
  net.W₁=firstRows 1 ∧ ∀ x,net.eval x=Maximum 4 x}
noncomputable def endpointPhysical (p : EndpointSlice) : RawSlice :=
  ⟨(1,p.val),zero_lt_one,le_rfl,p.property.1,p.property.2⟩
lemma continuous_endpointPhysical : Continuous endpointPhysical :=
  (continuous_const.prod_mk continuous_subtype_val).subtype_mk _
noncomputable def endpointLabel32 (p : EndpointSlice) : Fin 32 :=
  rawComponentLabel32 (endpointPhysical p)
theorem continuous_endpointLabel32 : Continuous endpointLabel32 :=
  continuous_rawComponentLabel32.comp continuous_endpointPhysical

#print axioms continuous_normalizePhysical
#print axioms continuous_rawComponentLabel
#print axioms continuous_rawComponentLabel32
#print axioms continuous_endpointLabel32
end MaxCaterpillar.Fiber.Count65.ActualStarLabels
