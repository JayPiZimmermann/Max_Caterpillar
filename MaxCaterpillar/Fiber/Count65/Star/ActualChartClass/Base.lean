import MaxCaterpillar.Fiber.Count65.Star.ActualLabelsPermutation
import MaxCaterpillar.Fiber.Count65.Star.PhysicalChart.Embedding
import MaxCaterpillar.Fiber.Count65.Star.PhysicalChart.Coverage

/-! # Actual star chart slices and their connected head-kind sectors

The public orientation bit means a negative physical W coefficient. The
existing physical chart uses its opposite, recorded by chartFlipBits.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MaxCaterpillar.Fiber.Count65.ActualStarLabels
open Set Function Star Star65 Star.PhysicalChart MaxCaterpillar.Frontier
open MaxCaterpillar.Fiber.Mixed65 (Heads)

abbrev ChartI (bits : Fin 3 → Bool) := BranchIFiber (chartFlipBits bits)
abbrev ChartII (bits : Fin 3 → Bool) := BranchIIFiber (chartFlipBits bits)

noncomputable def chartI (bits : Fin 3 → Bool) (q : ChartI bits) : Slice :=
  ⟨(q.val.1.val.1,branchIChart (chartFlipBits bits) q),q.val.1.property.1,
    q.val.1.property.2.1,rfl,branchIChart_eval _ q,by
      intro i
      rw [branchIChart_outputs]
      fin_cases i <;> norm_num⟩
noncomputable def chartII (bits : Fin 3 → Bool) (q : ChartII bits) : Slice :=
  ⟨(q.val.1.val.1,branchIIChart (chartFlipBits bits) q),q.val.1.property.1,
    q.val.1.property.2.1,rfl,branchIIChart_eval _ q,by
      intro i
      rw [branchIIChart_outputs]
      fin_cases i <;> norm_num⟩

lemma chartI_zeroBiases (bits : Fin 3 → Bool) (q : ChartI bits) :
    (chartI bits q).val.2.HasZeroBiases := ⟨rfl,rfl,rfl⟩
lemma chartII_zeroBiases (bits : Fin 3 → Bool) (q : ChartII bits) :
    (chartII bits q).val.2.HasZeroBiases := ⟨rfl,rfl,rfl⟩

lemma continuous_chartI (bits : Fin 3 → Bool) : Continuous (chartI bits) :=
  ((((continuous_fst.comp continuous_subtype_val).comp
    (continuous_fst.comp continuous_subtype_val))).prod_mk
      (continuous_branchIChart (chartFlipBits bits))).subtype_mk _
lemma continuous_chartII (bits : Fin 3 → Bool) : Continuous (chartII bits) :=
  ((((continuous_fst.comp continuous_subtype_val).comp
    (continuous_fst.comp continuous_subtype_val))).prod_mk
      (continuous_branchIIChart (chartFlipBits bits))).subtype_mk _

noncomputable def remainderI (bits : Fin 3 → Bool) (b : ResidualBase 0) : featureSpace 1 :=
  coefficientReadout 1 (branchICoefficients (flipValue (chartFlipBits bits 0))
    (flipValue (chartFlipBits bits 1)) (flipValue (chartFlipBits bits 2)) b)
noncomputable def remainderII (bits : Fin 3 → Bool) (b : ResidualBase (-1)) : featureSpace 1 :=
  coefficientReadout 1 (branchIICoefficients (flipValue (chartFlipBits bits 0))
    (flipValue (chartFlipBits bits 1)) (flipValue (chartFlipBits bits 2)) b)

def headSectorI (bits : Fin 3 → Bool) (kind : Bool) : Set (ChartI bits) :=
  if kind then HeadTopology.bundleSignedSector (featureSpace 1) (remainderI bits)
  else (HeadTopology.bundleSignedSector (featureSpace 1) (remainderI bits))ᶜ
def headSectorII (bits : Fin 3 → Bool) (kind : Bool) : Set (ChartII bits) :=
  if kind then HeadTopology.bundleSignedSector (featureSpace 1) (remainderII bits)
  else (HeadTopology.bundleSignedSector (featureSpace 1) (remainderII bits))ᶜ

lemma headKind_iff_test {α : Type*} (E : Submodule ℝ (α → ℝ)) (hE : Mixed65.ClippingRigid E)
    (D : HeadTopology.Data E) (L : E) (hr : (HeadTopology.toHeads D).Reconstructs (L : α → ℝ))
    (hnz : ∃ x,(L : α → ℝ) x ≠ 0) (kind : Bool) :
    (if kind then (HeadTopology.toHeads D).IsSigned (L : α → ℝ)
      else ¬ (HeadTopology.toHeads D).IsSigned (L : α → ℝ)) ↔
    (if kind then ∀ x : α,(HeadTopology.toHeads D).A x+(HeadTopology.toHeads D).B x=0
    else ∀ x : α,0 ≤ (HeadTopology.toHeads D).A x ∧ 0 ≤ (HeadTopology.toHeads D).B x) := by
  letI : Nonempty α := ⟨hnz.choose⟩
  let h := HeadTopology.toHeads D
  cases kind
  · constructor
    · intro hn
      have hh := (Heads.reconstructs_iff_signed_or_splitHybrid E hE h
        (L : α → ℝ) D.2.1.property D.2.2.property L.property).mp hr
      have hh := (hh.resolve_left hn).intercepts_nonneg
      exact fun x => ⟨hh.1 x,hh.2 x⟩
    · intro ht hs
      obtain ⟨x,hx⟩ := hnz
      have hp : 0 ≤ (L : α → ℝ) x := by simpa only [hs.1] using (ht x).1
      have hn : 0 ≤ -(L : α → ℝ) x := by simpa only [hs.2.1] using (ht x).2
      exact hx (by linarith only [hp,hn])
  · constructor
    · intro hs x
      rw [hs.1,hs.2.1]
      exact add_neg_self _
    · intro ht
      apply (HeadTopology.signed_iff_intercepts E hE h
        (L : α → ℝ) D.2.1.property D.2.2.property L.property hr hnz).mpr
      have ha : h.A=(L : α → ℝ) := by
        funext x
        have hb : h.B x = -h.A x := by linarith only [ht x]
        have hv := hr x 0
        norm_num [Heads.eval,relu] at hv
        rw [hb] at hv
        have hpos := relu_sub_relu_neg (h.A x)
        unfold relu at hpos
        linarith only [hv,hpos]
      refine ⟨ha,?_⟩
      funext x
      have hh := ht x
      change h.A x+h.B x=0 at hh
      rw [ha] at hh
      linarith only [hh]

lemma headSectorI_iff_test (bits : Fin 3 → Bool) (kind : Bool) (q : ChartI bits) :
    q ∈ headSectorI bits kind ↔
    (if kind then ∀ x : InvariantState,
      (HeadTopology.toHeads q.val.2).A x+(HeadTopology.toHeads q.val.2).B x=0
    else ∀ x : InvariantState,
      0 ≤ (HeadTopology.toHeads q.val.2).A x ∧ 0 ≤ (HeadTopology.toHeads q.val.2).B x) := by
  have hh := headKind_iff_test (featureSpace 1) (clippingRigid_featureSpace (by norm_num))
    q.val.2 (remainderI bits q.val.1) q.property (branchI_remainder_nonzero _ _ _ q.val.1) kind
  cases kind <;> simpa [headSectorI,HeadTopology.bundleSignedSector] using hh
lemma headSectorII_iff_test (bits : Fin 3 → Bool) (kind : Bool) (q : ChartII bits) :
    q ∈ headSectorII bits kind ↔
    (if kind then ∀ x : InvariantState,
      (HeadTopology.toHeads q.val.2).A x+(HeadTopology.toHeads q.val.2).B x=0
    else ∀ x : InvariantState,
      0 ≤ (HeadTopology.toHeads q.val.2).A x ∧ 0 ≤ (HeadTopology.toHeads q.val.2).B x) := by
  have hh := headKind_iff_test (featureSpace 1) (clippingRigid_featureSpace (by norm_num))
    q.val.2 (remainderII bits q.val.1) q.property (branchII_remainder_nonzero _ _ _ q.val.1) kind
  cases kind <;> simpa [headSectorII,HeadTopology.bundleSignedSector] using hh

#print axioms headSectorI_iff_test
#print axioms headSectorII_iff_test
end MaxCaterpillar.Fiber.Count65.ActualStarLabels
