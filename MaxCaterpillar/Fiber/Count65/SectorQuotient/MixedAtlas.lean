import MaxCaterpillar.Fiber.Count65.SectorQuotient.SectorAtlas
import MaxCaterpillar.Fiber.Count65.SectorQuotient.AtlasPermutations
import MaxCaterpillar.Fiber.Count65.SectorQuotient.CanonicalLabels
import MaxCaterpillar.Fiber.Count65.SectorQuotient.MixedFirst
import MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsOrbit
import MaxCaterpillar.Fiber.Disconnected65

/-! An honest finite closed normalization atlas on the actual mixed sector. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

noncomputable def mixedChart (i : FrameIndex) : Set Mixed65.sector :=
  {x | (Mixed65.permutationHomeomorph i.1 i.2).symm x.val ∈ Mixed65.labeledScaledSector}

lemma isClosed_mixedChart (i : FrameIndex) : IsClosed (mixedChart i) :=
  (Mixed65.isClosed_labeledScaledSector_of_coefficient_bound
    Mixed65.normalizedCoefficientBound).preimage
    ((Mixed65.permutationHomeomorph i.1 i.2).symm.continuous.comp continuous_subtype_val)

lemma mixedChart_cover (x : Mixed65.sector) : ∃ i,x ∈ mixedChart i := by
  have hx : x.val ∈ ⋃ p : Equiv.Perm (Fin 6), ⋃ q : Equiv.Perm (Fin 4),
      Mixed65.permutationHomeomorph p q '' Mixed65.labeledScaledSector := by
    rw [←Mixed65.sector_eq_iUnion_permutationImage]
    exact x.property
  obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hx
  obtain ⟨q,y,hy,he⟩ := Set.mem_iUnion.mp hp
  refine ⟨(p,q),?_⟩
  change (Mixed65.permutationHomeomorph p q).symm x.val ∈ Mixed65.labeledScaledSector
  rw [←he,(Mixed65.permutationHomeomorph p q).symm_apply_apply]
  exact hy

noncomputable def mixedChartLabeled (i : FrameIndex) (x : mixedChart i) : MixedDomain :=
  ⟨(Mixed65.permutationHomeomorph i.1 i.2).symm x.val.val,x.property⟩

lemma continuous_mixedChartLabeled (i : FrameIndex) : Continuous (mixedChartLabeled i) :=
  ((Mixed65.permutationHomeomorph i.1 i.2).symm.continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

noncomputable def mixedChartNormalize (i : FrameIndex) (x : mixedChart i) :
    ActualMixedLabels.Slice :=
  ActualMixedLabels.normalizePhysical (mixedFirst (mixedChartLabeled i x))

lemma continuous_mixedChartNormalize (i : FrameIndex) :
    Continuous (mixedChartNormalize i) :=
  ActualMixedLabels.continuous_normalizePhysical.comp
    (continuous_mixedFirst.comp (continuous_mixedChartLabeled i))

lemma mixedChart_quotient_correct (i : FrameIndex) (x : mixedChart i) :
    quotientMk (canonicalMixedFiber (mixedChartNormalize i x))=quotientMk x.val.val := by
  exact (ActualMixedLabels.normalizePhysical_sameQuotient
    (mixedFirst (mixedChartLabeled i x))).trans
    ((mixedFirst_sameQuotient (mixedChartLabeled i x)).trans
      (permutationHomeomorph_symm_sameQuotient i.1 i.2 x.val.val))

noncomputable def mixedAtlas : SectorAtlas Mixed65.sector ActualMixedLabels.Slice where
  canonical := canonicalMixedFiber
  component := ActualMixedLabels.componentLabel
  continuous_component := ActualMixedLabels.continuous_componentLabel
  component_eq_of_quotient := mixed_componentLabel_eq_of_quotientMk_eq
  chart := mixedChart
  closed_chart := isClosed_mixedChart
  cover := mixedChart_cover
  normalize := mixedChartNormalize
  continuous_normalize := continuous_mixedChartNormalize
  quotient_correct := mixedChart_quotient_correct

end MaxCaterpillar.Fiber.Count65.SectorQuotient
