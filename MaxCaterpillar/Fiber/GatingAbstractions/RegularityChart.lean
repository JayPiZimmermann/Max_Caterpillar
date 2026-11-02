import MaxCaterpillar.Fiber.GatingAbstractions.SmoothRegularity
import MaxCaterpillar.Fiber.GatingAbstractions.SmoothCombined
import MaxCaterpillar.Fiber.GatingAbstractions.RegularityTopology
import MaxCaterpillar.Fiber.GatingAbstractions.RegularitySplit
import MaxCaterpillar.Fiber.GatingAbstractions.RegularityFamilyBase
import MaxCaterpillar.Fiber.GatingAbstractions.RegularityJacobian

/-!
# The whole bias-free exact Max4 fiber is regular at the merge examples

All forty-five physical weights are allowed to vary. Finite evaluations and
seventeen actual free weight entries form local coordinates. An explicit
exact family proves that their regular finite level set is locally the whole
all-input exact fiber; no first-layer classification is assumed.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section

namespace MaxCaterpillar.Fiber.GatingAbstractions

open Filter Topology

lemma continuous_freeCoordinates : Continuous (freeCoordinates : Raw → Free) :=
  continuous_pi fun i => continuous_apply (freeIndices i)

lemma family_mem_rawExactSet (c : ℝ) (hc : 0 ≤ c) :
    toRaw (family c) ∈ RawExactSet := by
  have hz : (family c).HasZeroBiases := ⟨rfl, rfl, rfl⟩
  change ∀ x, (fromRaw (toRaw (family c))).eval x = Maximum 4 x
  rw [fromRaw_toRaw (family c) hz]
  exact family_eval c hc

lemma split_combinedMap (p : Raw) :
    splitCoordinates (combinedMap p) = (observations p, freeCoordinates p) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

/-- The exact family and finite evaluations fill an ambient regular chart.
The derivative hypothesis is discharged for each final merge point below. -/
theorem smooth_regular_family_of_strict_combined (c : ℝ) (hc : 0 < c)
    (hJ : HasStrictFDerivAt combinedMap
      (jacEquiv c : Raw →L[ℝ] Raw) (toRaw (family c))) :
    HasSmoothRegularFiberChartAt (V := Observed) (W := Free)
      RawExactSet (toRaw (family c)) := by
  let a := toRaw (family c)
  let L : Raw ≃L[ℝ] (Observed × Free) := (jacEquiv c).trans splitCoordinates
  have hMap : (fun p => (splitCoordinates : Raw →L[ℝ] Observed × Free)
      (combinedMap p)) = (fun p => (observations p, freeCoordinates p)) := by
    funext p
    exact split_combinedMap p
  have hL : HasStrictFDerivAt (fun p => (observations p, freeCoordinates p))
      (L : Raw →L[ℝ] Observed × Free) a := by
    have h := (splitCoordinates : Raw →L[ℝ] Observed × Free).hasStrictFDerivAt.comp a hJ
    change HasStrictFDerivAt (fun p =>
      (splitCoordinates : Raw →L[ℝ] Observed × Free) (combinedMap p))
      (L : Raw →L[ℝ] Observed × Free) a at h
    rw [hMap] at h
    exact h
  have hsm : ContDiffAt ℝ ⊤ (fun p => (observations p, freeCoordinates p)) a := by
    have h := (splitCoordinates : Raw →L[ℝ] Observed × Free).contDiff.contDiffAt.comp a
      (smooth_combined c hc)
    change ContDiffAt ℝ ⊤ (fun p =>
      (splitCoordinates : Raw →L[ℝ] Observed × Free) (combinedMap p)) a at h
    rw [hMap] at h
    exact h
  have hsec := RegularityFamily.local_exact_section c hc
  have ha := family_mem_rawExactSet c hc.le
  apply smooth_regular_fiber_chart_of_inverse_coordinates RawExactSet observations
    freeCoordinates RegularityFamily.familyRaw a L hL hsm
  · exact RegularityFamily.familyRaw_freeCoordinates_base c
  · simpa only [a, RegularityFamily.freeCoordinates_base] using hsec.1
  · exact continuous_freeCoordinates.continuousAt
  · intro p hp
    funext i
    exact (hp (samples i)).trans (ha (samples i)).symm
  · change ∀ᶠ p in 𝓝 (freeCoordinates (toRaw (family c))),
      RegularityFamily.familyRaw p ∈ RawExactSet
    rw [RegularityFamily.freeCoordinates_base]
    exact hsec.2.mono fun p hp => hp.1
  · change ∀ᶠ p in 𝓝 (freeCoordinates (toRaw (family c))),
      freeCoordinates (RegularityFamily.familyRaw p) = p
    rw [RegularityFamily.freeCoordinates_base]
    exact hsec.2.mono fun p hp => hp.2

/-- The whole bias-free exact fiber has a smooth ambient chart at the first
representation-merging event. No classification or rank hypothesis remains. -/
theorem smooth_regular_family_one :
    HasSmoothRegularFiberChartAt (V := Observed) (W := Free)
      RawExactSet (toRaw (family 1)) :=
  smooth_regular_family_of_strict_combined 1 (by norm_num)
    hasStrictFDerivAt_combined_one

/-- The same full-fiber conclusion at the second merging event. -/
theorem smooth_regular_family_two :
    HasSmoothRegularFiberChartAt (V := Observed) (W := Free)
      RawExactSet (toRaw (family 2)) :=
  smooth_regular_family_of_strict_combined 2 (by norm_num)
    hasStrictFDerivAt_combined_two

theorem regular_family_one :
    HasRegularFiberChartAt (V := Observed) (W := Free)
      RawExactSet (toRaw (family 1)) := smooth_regular_family_one.regular

theorem regular_family_two :
    HasRegularFiberChartAt (V := Observed) (W := Free)
      RawExactSet (toRaw (family 2)) := smooth_regular_family_two.regular

#print axioms smooth_regular_family_one
#print axioms smooth_regular_family_two
#print axioms regular_family_one
#print axioms regular_family_two

end MaxCaterpillar.Fiber.GatingAbstractions
