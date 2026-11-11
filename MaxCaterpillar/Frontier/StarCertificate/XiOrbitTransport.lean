import MaxCaterpillar.Frontier.StarCertificate.XiOrbitData
import MaxCaterpillar.Frontier.StarCertificate.StarLeafEquivariance
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate

/-- All eighty actual real anchored expressions vanish at this point. -/
def AllStarAnovaZero (z : Fin 4 → ℝ) : Prop :=
  ∀ t : Fin 80, evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z = 0

theorem allStarAnovaZero_iff_components (z : Fin 4 → ℝ) :
    AllStarAnovaZero z ↔ ∀ (S A : Finset (Fin 4)), S.Nonempty → A ⊆ S →
      component starPsi S A z = 0 := by
  constructor
  · intro h S A hS hA
    obtain ⟨t,hs,ha⟩ := pair_cover S A hS hA
    rw [component_linearization]
    simpa only [starAnovaCoefficients,hs,ha] using h t
  · intro h t
    change evalForm (componentCoefficients (maskSet (pairS t)) (maskSet (pairA t))
      (actualSigns subsetForms z)) z = 0
    rw [← component_linearization]
    exact h _ _ (pair_valid t).1 (pair_valid t).2

theorem allStarAnovaZero_permute_forward (e : Equiv.Perm (Fin 4)) (z : Fin 4 → ℝ)
    (h : AllStarAnovaZero z) : AllStarAnovaZero (fun i => z (e i)) := by
  rw [allStarAnovaZero_iff_components] at h ⊢
  intro S A hS hA
  rw [component_starPsi_leaf_permute]
  have hmap : (S.map e.toEmbedding).Nonempty := by
    obtain ⟨i,hi⟩ := hS
    exact ⟨e i,Finset.mem_map.mpr ⟨i,hi,rfl⟩⟩
  exact h _ _ hmap (Finset.map_subset_map.mpr hA)

theorem allStarAnovaZero_permute (e : Equiv.Perm (Fin 4)) (z : Fin 4 → ℝ) :
    AllStarAnovaZero (fun i => z (e i)) ↔ AllStarAnovaZero z := by
  constructor
  · intro h
    have hh := allStarAnovaZero_permute_forward e.symm (fun i => z (e i)) h
    simpa only [Equiv.apply_symm_apply] using hh
  · exact allStarAnovaZero_permute_forward e z

theorem allStarAnovaZero_reorderLeafPoint (p : Fin 24) (z : Fin 4 → ℝ) :
    AllStarAnovaZero (reorderLeafPoint p z) ↔ AllStarAnovaZero z := by
  simpa only [reorderLeafPoint,leafPermutationEquiv_apply] using
    allStarAnovaZero_permute (leafPermutationEquiv p) z

theorem allStarAnovaZero_neg (z : Fin 4 → ℝ) :
    AllStarAnovaZero (fun i => -z i) ↔ AllStarAnovaZero z := by
  constructor
  · intro h t
    rw [← starAnova_eval_neg z t]
    exact h t
  · intro h t
    rw [starAnova_eval_neg z t]
    exact h t

theorem allStarAnovaZero_orbitPoint (d : OrbitDescriptor) (z : Fin 4 → ℝ) :
    AllStarAnovaZero (orbitPoint d z) ↔ AllStarAnovaZero z := by
  unfold orbitPoint
  split_ifs
  · exact (allStarAnovaZero_neg _).trans (allStarAnovaZero_reorderLeafPoint _ _)
  · exact allStarAnovaZero_reorderLeafPoint _ _

theorem orbitPoint_sign_pattern (j : Fin 900) (z : Fin 4 → ℝ)
    (hz : actualSigns subsetForms z = orbitLeafPattern j)
    (hcheck : orbitPatternTransform (orbitDescriptor j) (orbitLeafPattern j) =
      orbitRepresentativePattern (orbitDescriptor j).representative) :
    actualSigns subsetForms (orbitPoint (orbitDescriptor j) z) =
      orbitRepresentativePattern (orbitDescriptor j).representative := by
  rw [actualSigns_orbitPoint,hz,hcheck]

/-- Raw-pattern form used directly with the existing geometry catalogue. -/
theorem orbit_reduce_pattern (s : Fin 15 → Sign) (d : OrbitDescriptor)
    (hcheck : orbitPatternTransform d s = orbitRepresentativePattern d.representative)
    (hrep : ∀ (z : Fin 4 → ℝ),
      actualSigns subsetForms z = orbitRepresentativePattern d.representative → AllStarAnovaZero z) :
    ∀ (z : Fin 4 → ℝ), actualSigns subsetForms z = s → AllStarAnovaZero z := by
  intro z hz
  apply (allStarAnovaZero_orbitPoint d z).mp
  apply hrep
  rw [actualSigns_orbitPoint,hz,hcheck]

/-- A finite checked orbit descriptor transfers representative stratum
soundness to this entire real sign stratum, without any coefficient-vector
identity on lower-dimensional faces. -/
theorem orbit_reduce_leaf (j : Fin 900)
    (hcheck : orbitPatternTransform (orbitDescriptor j) (orbitLeafPattern j) =
      orbitRepresentativePattern (orbitDescriptor j).representative)
    (hrep : ∀ (z : Fin 4 → ℝ),
      actualSigns subsetForms z = orbitRepresentativePattern (orbitDescriptor j).representative →
      AllStarAnovaZero z) :
    ∀ (z : Fin 4 → ℝ), actualSigns subsetForms z = orbitLeafPattern j → AllStarAnovaZero z := by
  intro z hz
  apply (allStarAnovaZero_orbitPoint (orbitDescriptor j) z).mp
  exact hrep _ (orbitPoint_sign_pattern j z hz hcheck)

end MaxCaterpillar.Frontier.StarCertificate
