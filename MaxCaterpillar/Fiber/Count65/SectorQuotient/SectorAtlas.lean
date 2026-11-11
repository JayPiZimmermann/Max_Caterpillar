import MaxCaterpillar.Fiber.Count65.SectorQuotient.ClosedCover
import MaxCaterpillar.Fiber.Count65.SectorQuotient.PhysicalOrbit
import MaxCaterpillar.Fiber.Count65.Topology

/-! Continuous sector labels from actual finite first-frame normalization
charts. Every normalization's genuine quotient equality is an explicit input. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

abbrev FrameIndex := Equiv.Perm (Fin 6) × Equiv.Perm (Fin 4)

structure SectorAtlas (S : Set (ExactFiber 4 6 5)) (K : Type*) [TopologicalSpace K] where
  canonical : K → ExactFiber 4 6 5
  component : K → NonpairedLabel
  continuous_component : Continuous component
  component_eq_of_quotient : ∀ a b,quotientMk (canonical a)=quotientMk (canonical b) →
    component a=component b
  chart : FrameIndex → Set S
  closed_chart : ∀ i,IsClosed (chart i)
  cover : ∀ x,∃ i,x∈chart i
  normalize : ∀ i,chart i → K
  continuous_normalize : ∀ i,Continuous (normalize i)
  quotient_correct : ∀ i (x : chart i),
    quotientMk (canonical (normalize i x))=quotientMk x.val.val

namespace SectorAtlas
variable {S : Set (ExactFiber 4 6 5)} {K : Type*} [TopologicalSpace K]

noncomputable def label (d : SectorAtlas S K) : S → NonpairedLabel :=
  closedCoverGlue d.chart d.cover (fun i => d.component ∘ d.normalize i)

lemma label_eq_normalize (d : SectorAtlas S K) (i : FrameIndex) (x : d.chart i) :
    d.label x=d.component (d.normalize i x) := by
  apply closedCoverGlue_eq d.chart d.cover (fun i => d.component ∘ d.normalize i)
  intro i j x hi hj
  exact d.component_eq_of_quotient _ _
    ((d.quotient_correct i ⟨x,hi⟩).trans (d.quotient_correct j ⟨x,hj⟩).symm)

theorem continuous_label (d : SectorAtlas S K) : Continuous d.label := by
  apply continuous_closedCoverGlue d.chart d.cover d.closed_chart
    (fun i => d.component ∘ d.normalize i)
    (fun i => d.continuous_component.comp (d.continuous_normalize i))
  intro i j x hi hj
  exact d.component_eq_of_quotient _ _
    ((d.quotient_correct i ⟨x,hi⟩).trans (d.quotient_correct j ⟨x,hj⟩).symm)

theorem label_eq_of_quotient (d : SectorAtlas S K) (a b : S)
    (h : quotientMk a.val=quotientMk b.val) : d.label a=d.label b := by
  obtain ⟨i,hi⟩ := d.cover a
  obtain ⟨j,hj⟩ := d.cover b
  calc
    d.label a=d.component (d.normalize i ⟨a,hi⟩) := d.label_eq_normalize i ⟨a,hi⟩
    _=d.component (d.normalize j ⟨b,hj⟩) := d.component_eq_of_quotient _ _
      ((d.quotient_correct i ⟨a,hi⟩).trans (h.trans (d.quotient_correct j ⟨b,hj⟩).symm))
    _=d.label b := (d.label_eq_normalize j ⟨b,hj⟩).symm

theorem label_canonical (d : SectorAtlas S K) (p : K) (hp : d.canonical p∈S) :
    d.label ⟨d.canonical p,hp⟩=d.component p := by
  obtain ⟨i,hi⟩ := d.cover ⟨d.canonical p,hp⟩
  calc
    _=d.component (d.normalize i ⟨⟨d.canonical p,hp⟩,hi⟩) :=
      d.label_eq_normalize i ⟨⟨d.canonical p,hp⟩,hi⟩
    _=d.component p := d.component_eq_of_quotient _ _ (d.quotient_correct i _)

theorem label_covered (d : SectorAtlas S K) (x : S) :
    ∃ p : K,quotientMk (d.canonical p)=quotientMk x.val ∧ d.component p=d.label x := by
  obtain ⟨i,hi⟩ := d.cover x
  exact ⟨d.normalize i ⟨x,hi⟩,d.quotient_correct i _,(d.label_eq_normalize i ⟨x,hi⟩).symm⟩

end SectorAtlas

/-- A genuine quotient identification preserves zero biases; no normalization
orbits are identified by definition. -/
theorem zeroBias_of_quotientMk_eq (a b : ExactFiber 4 6 5)
    (ha : a.val.HasZeroBiases) (h : quotientMk a=quotientMk b) : b.val.HasZeroBiases := by
  obtain ⟨w⟩ := physicalOrbit_of_quotientMk_eq h
  rcases ha with ⟨h1,h2,h3⟩
  refine ⟨?_,?_,w.output_bias.trans h3⟩
  · funext j
    simpa only [h1,Pi.zero_apply,mul_zero] using w.first_bias j
  · funext j
    simpa only [h2,Pi.zero_apply,mul_zero] using w.second_bias j

#print axioms SectorAtlas.continuous_label
#print axioms SectorAtlas.label_eq_of_quotient
#print axioms zeroBias_of_quotientMk_eq
end MaxCaterpillar.Fiber.Count65.SectorQuotient
