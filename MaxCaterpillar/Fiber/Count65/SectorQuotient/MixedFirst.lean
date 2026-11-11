import MaxCaterpillar.Fiber.Count65.SectorQuotient.FirstNormalization
import MaxCaterpillar.Fiber.Mixed65.BoundaryRows
import MaxCaterpillar.Fiber.Mixed65.SectorNormalForm
import MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsNormalization

/-! Explicit continuous first-frame normalization on the actual positively
scaled mixed sector. Every bias and suffix parameter is retained physically. -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

abbrev MixedDomain := {net : ExactFiber 4 6 5 // net ∈ Mixed65.labeledScaledSector}

noncomputable def mixedParameter (n : MixedDomain) : ℝ :=
  Mixed65.mixedA n.val.val / Mixed65.mixedB n.val.val

noncomputable def mixedScales (n : MixedDomain) : Fin 6 → ℝ :=
  Mixed65.rowScale n.val.val

lemma mixed_first_data (n : MixedDomain) :
    0 < mixedParameter n ∧ (∀ j, 0 < mixedScales n j) ∧
    n.val.val.W₁ = fun j i => mixedScales n j * Mixed65.firstRows (mixedParameter n) j i := by
  obtain ⟨t,ht,s,hs,hw⟩ := n.property
  have hscale := Mixed65.rowScale_of_scaled_firstRows n.val.val t s hw
  have ha : Mixed65.mixedA n.val.val = s 3 * t := by
    unfold Mixed65.mixedA
    rw [hw]
    rfl
  have hb : Mixed65.mixedB n.val.val = s 3 := by
    unfold Mixed65.mixedB
    rw [hw]
    change s 3 * 1 = s 3
    ring
  have hp : mixedParameter n = t := by
    unfold mixedParameter
    rw [ha,hb]
    field_simp [(hs 3).ne']
    ring
  have hsc : mixedScales n = s := hscale
  refine ⟨hp ▸ ht, ?_, ?_⟩
  · simpa only [hsc] using hs
  · rw [hp,hsc]
    exact hw

lemma mixed_scales_pos (n : MixedDomain) (j : Fin 6) : 0 < mixedScales n j :=
  (mixed_first_data n).2.1 j

noncomputable def mixedFirst (n : MixedDomain) : ActualMixedLabels.RawSlice :=
  ⟨(mixedParameter n,scaleFirst n.val.val (fun j => (mixedScales n j)⁻¹)),
    (mixed_first_data n).1,
    reciprocal_first_weights n.val.val (mixedScales n) _
      (fun j => (mixed_scales_pos n j).ne') (mixed_first_data n).2.2,
    fun x => (scaleFirst_eval n.val.val _
      (fun j => inv_pos.mpr (mixed_scales_pos n j)) x).trans (n.val.property x)⟩

private lemma continuous_mixed_network : Continuous (fun n : MixedDomain => n.val.val) :=
  continuous_subtype_val.comp continuous_subtype_val

lemma continuous_mixedScales : Continuous mixedScales :=
  Mixed65.continuous_rowScale.comp continuous_mixed_network

lemma continuous_mixedParameter : Continuous mixedParameter := by
  apply (Mixed65.continuous_mixedA.comp continuous_mixed_network).div
    (Mixed65.continuous_mixedB.comp continuous_mixed_network)
  intro n
  exact (mixed_scales_pos n 3).ne'

lemma continuous_mixedFirst : Continuous mixedFirst := by
  have hi : Continuous (fun n : MixedDomain => fun j => (mixedScales n j)⁻¹) := by
    apply continuous_pi
    intro j
    exact ((continuous_apply j).comp continuous_mixedScales).inv₀
      (fun n => (mixed_scales_pos n j).ne')
  have hn := continuous_variable_scaleFirst (fun n : MixedDomain => n.val.val)
    (fun n j => (mixedScales n j)⁻¹) continuous_mixed_network hi
    (fun n j => inv_ne_zero (mixed_scales_pos n j).ne')
  exact (continuous_mixedParameter.prod_mk hn).subtype_mk _

noncomputable def mixedFirstExact (n : MixedDomain) : ExactFiber 4 6 5 :=
  ⟨(mixedFirst n).val.2,(mixedFirst n).property.2.2⟩

lemma continuous_mixedFirstExact : Continuous mixedFirstExact :=
  (continuous_snd.comp (continuous_subtype_val.comp continuous_mixedFirst)).subtype_mk _

lemma mixedFirst_sameQuotient (n : MixedDomain) :
    quotientMk (mixedFirstExact n) = quotientMk n.val := by
  exact (quotientMk_eq_of_step (SymmetryStep.first n.val
    (fun j => (mixedScales n j)⁻¹) (fun j => inv_pos.mpr (mixed_scales_pos n j)))).symm

end MaxCaterpillar.Fiber.Count65.SectorQuotient
