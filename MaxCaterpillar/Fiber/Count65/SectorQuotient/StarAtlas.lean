import MaxCaterpillar.Fiber.Count65.SectorQuotient.SectorAtlas
import MaxCaterpillar.Fiber.Count65.SectorQuotient.AtlasPermutations
import MaxCaterpillar.Fiber.Count65.SectorQuotient.CanonicalLabels
import MaxCaterpillar.Fiber.Count65.SectorQuotient.StarFirst
import MaxCaterpillar.Fiber.Count65.SectorQuotient.Partition

/-! An honest finite closed normalization atlas on the complete star sector. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

open SectorSeparation

noncomputable def starChart (i : FrameIndex) : Set starSet :=
  {x | (Mixed65.permutationHomeomorph i.1 i.2).symm x.val ∈ StarClosed.labeled}

lemma isClosed_starChart (i : FrameIndex) : IsClosed (starChart i) :=
  StarClosed.isClosed_labeled.preimage
    ((Mixed65.permutationHomeomorph i.1 i.2).symm.continuous.comp continuous_subtype_val)

lemma starChart_cover (x : starSet) : ∃ i,x ∈ starChart i := by
  have hx : x.val ∈ ⋃ p : Equiv.Perm (Fin 6), ⋃ q : Equiv.Perm (Fin 4),
      Mixed65.permutationHomeomorph p q '' StarClosed.labeled := by
    rw [←StarClosed.star_eq_iUnion]
    exact x.property
  obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hx
  obtain ⟨q,y,hy,he⟩ := Set.mem_iUnion.mp hp
  refine ⟨(p,q),?_⟩
  change (Mixed65.permutationHomeomorph p q).symm x.val ∈ StarClosed.labeled
  rw [←he,(Mixed65.permutationHomeomorph p q).symm_apply_apply]
  exact hy

noncomputable def starChartLabeled (i : FrameIndex) (x : starChart i) : StarDomain :=
  ⟨(Mixed65.permutationHomeomorph i.1 i.2).symm x.val.val,x.property⟩

lemma continuous_starChartLabeled (i : FrameIndex) : Continuous (starChartLabeled i) :=
  ((Mixed65.permutationHomeomorph i.1 i.2).symm.continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

noncomputable def starChartNormalize (i : FrameIndex) (x : starChart i) :
    ActualStarLabels.Slice :=
  ActualStarLabels.normalizePhysical (starFirst (starChartLabeled i x))

lemma continuous_starChartNormalize (i : FrameIndex) : Continuous (starChartNormalize i) :=
  ActualStarLabels.continuous_normalizePhysical.comp
    (continuous_starFirst.comp (continuous_starChartLabeled i))

lemma star_normalizePhysical_sameQuotient (p : ActualStarLabels.RawSlice) :
    quotientMk (canonicalStarFiber (ActualStarLabels.normalizePhysical p))=
      quotientMk (⟨p.val.2,p.property.2.2.2⟩ : ExactFiber 4 6 5) := by
  exact (quotientMk_eq_of_step (SymmetryStep.second
    (⟨p.val.2,p.property.2.2.2⟩ : ExactFiber 4 6 5)
    (fun k => |p.val.2.w₃ k|)
    (fun k => abs_pos.mpr (ActualStarLabels.raw_outputs_nonzero p k)))).symm

lemma starChart_quotient_correct (i : FrameIndex) (x : starChart i) :
    quotientMk (canonicalStarFiber (starChartNormalize i x))=quotientMk x.val.val := by
  exact (star_normalizePhysical_sameQuotient (starFirst (starChartLabeled i x))).trans
    ((starFirst_sameQuotient (starChartLabeled i x)).trans
      (permutationHomeomorph_symm_sameQuotient i.1 i.2 x.val.val))

noncomputable def starAtlas : SectorAtlas starSet ActualStarLabels.Slice where
  canonical := canonicalStarFiber
  component := ActualStarLabels.componentLabel
  continuous_component := ActualStarLabels.continuous_componentLabel
  component_eq_of_quotient := star_componentLabel_eq_of_quotientMk_eq
  chart := starChart
  closed_chart := isClosed_starChart
  cover := starChart_cover
  normalize := starChartNormalize
  continuous_normalize := continuous_starChartNormalize
  quotient_correct := starChart_quotient_correct

end MaxCaterpillar.Fiber.Count65.SectorQuotient
