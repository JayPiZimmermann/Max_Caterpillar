import MaxCaterpillar.Fiber.Count65.SectorQuotient.SectorAtlas
import MaxCaterpillar.Fiber.BiasQuotient
import MaxCaterpillar.Fiber.Separation

/-! Genuine full and zero-bias quotient labels from verified sector atlases. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

instance optionNonpairedLabelTopology : TopologicalSpace (Option NonpairedLabel) := ⊥
instance optionNonpairedLabelDiscrete : DiscreteTopology (Option NonpairedLabel) := ⟨rfl⟩

namespace SectorAtlas
variable {S : Set (ExactFiber 4 6 5)} {K : Type*} [TopologicalSpace K]

noncomputable def extendedLabel (d : SectorAtlas S K) : ExactFiber 4 6 5 → Option NonpairedLabel :=
  by
    classical
    exact fun x => if h : x∈S then some (d.label ⟨x,h⟩) else none

lemma extendedLabel_none_iff (d : SectorAtlas S K) (x : ExactFiber 4 6 5) :
    d.extendedLabel x=none ↔ x∉S := by
  classical
  by_cases hx : x∈S <;> simp [extendedLabel,hx]

lemma extendedLabel_some_iff (d : SectorAtlas S K) (x : ExactFiber 4 6 5) (l : NonpairedLabel) :
    d.extendedLabel x=some l ↔ ∃ h : x∈S,d.label ⟨x,h⟩=l := by
  classical
  by_cases hx : x∈S <;> simp [extendedLabel,hx]

theorem continuous_extendedLabel (d : SectorAtlas S K) (hS : IsClopen S) :
    Continuous d.extendedLabel := by
  classical
  have hs : ContinuousOn d.extendedLabel S := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (fun x : S => d.extendedLabel x)=fun x : S => some (d.label x) := by
      funext x
      simp only [extendedLabel,dif_pos x.property]
    change Continuous (fun x : S => d.extendedLabel x)
    rw [heq]
    exact (continuous_of_discreteTopology : Continuous (some : NonpairedLabel → Option NonpairedLabel)).comp
      d.continuous_label
  have hc : ContinuousOn d.extendedLabel Sᶜ := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (fun x : ↥(Sᶜ) => d.extendedLabel x)=fun _ : ↥(Sᶜ) => (none : Option NonpairedLabel) := by
      funext x
      simp only [extendedLabel,dif_neg x.property]
    change Continuous (fun x : ↥(Sᶜ) => d.extendedLabel x)
    rw [heq]
    exact continuous_const
  let C : Bool → Set (ExactFiber 4 6 5) := fun b => if b then S else Sᶜ
  have hcov : ⋃ b,C b=Set.univ := by
    ext x
    by_cases hx : x∈S <;> simp [C,hx]
  apply (locallyFinite_of_finite C).continuous hcov
  · intro b
    cases b
    · exact hS.1.isClosed_compl
    · exact hS.2
  · intro b
    cases b
    · exact hc
    · exact hs

theorem extendedLabel_symmetry (d : SectorAtlas S K) (hS : SymmetryInvariant S)
    (a b : ExactFiber 4 6 5) (h : EqvGen SymmetryStep a b) :
    d.extendedLabel a=d.extendedLabel b := by
  classical
  by_cases ha : a∈S
  · have hb : b∈S := (hS a b h).mp ha
    simp only [extendedLabel,dif_pos ha,dif_pos hb]
    congr 1
    exact d.label_eq_of_quotient ⟨a,ha⟩ ⟨b,hb⟩ ((quotientMk_eq_iff a b).mpr h)
  · have hb : b∉S := fun hb => ha ((hS a b h).mpr hb)
    simp only [extendedLabel,dif_neg ha,dif_neg hb]

noncomputable def fullQuotientLabel (d : SectorAtlas S K) (hS : SymmetryInvariant S) :
    SymmetryQuotient 4 6 5 → Option NonpairedLabel :=
  Quotient.lift d.extendedLabel (d.extendedLabel_symmetry hS)

theorem continuous_fullQuotientLabel (d : SectorAtlas S K)
    (hopen : IsClopen S) (hS : SymmetryInvariant S) : Continuous (d.fullQuotientLabel hS) := by
  apply continuous_coinduced_dom.mpr
  exact d.continuous_extendedLabel hopen

noncomputable def zeroBiasQuotientLabel (d : SectorAtlas S K) (hS : SymmetryInvariant S) :
    ZeroBiasSymmetryQuotient 4 6 5 → Option NonpairedLabel :=
  Quotient.lift (fun x : ZeroBiasFiber 4 6 5 => d.extendedLabel (includeZeroBias x))
    (fun a b h => d.extendedLabel_symmetry hS (includeZeroBias a) (includeZeroBias b) h)

theorem continuous_zeroBiasQuotientLabel (d : SectorAtlas S K)
    (hopen : IsClopen S) (hS : SymmetryInvariant S) :
    Continuous (d.zeroBiasQuotientLabel hS) := by
  apply continuous_coinduced_dom.mpr
  exact (d.continuous_extendedLabel hopen).comp continuous_includeZeroBias

lemma zeroBiasQuotientLabel_mk (d : SectorAtlas S K) (hS : SymmetryInvariant S)
    (x : ZeroBiasFiber 4 6 5) :
    d.zeroBiasQuotientLabel hS (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) x)=
      d.extendedLabel (includeZeroBias x) := rfl

lemma zeroBiasQuotientLabel_canonical (d : SectorAtlas S K) (hS : SymmetryInvariant S)
    (p : K) (hp : d.canonical p∈S) (hz : (d.canonical p).val.HasZeroBiases) :
    d.zeroBiasQuotientLabel hS
      (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) ⟨d.canonical p,hz⟩)=some (d.component p) := by
  change d.extendedLabel (d.canonical p)=some (d.component p)
  simp only [extendedLabel,dif_pos hp]
  congr 1
  exact d.label_canonical p hp

/-- Every some-label fiber has an actual zero-bias canonical representative
with the same genuine quotient point and the advertised physical label. -/
theorem zeroBiasQuotientLabel_some_covered (d : SectorAtlas S K) (hS : SymmetryInvariant S)
    (z : ZeroBiasSymmetryQuotient 4 6 5) (l : NonpairedLabel)
    (h : d.zeroBiasQuotientLabel hS z=some l) :
    ∃ (p : K) (hz : (d.canonical p).val.HasZeroBiases),
      Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) ⟨d.canonical p,hz⟩=z ∧ d.component p=l := by
  induction z using Quotient.inductionOn with
  | h x =>
    change d.extendedLabel (includeZeroBias x)=some l at h
    obtain ⟨hx,hl⟩ := (d.extendedLabel_some_iff (includeZeroBias x) l).mp h
    obtain ⟨p,hq,hlabel⟩ := d.label_covered ⟨includeZeroBias x,hx⟩
    have hz := zeroBias_of_quotientMk_eq (includeZeroBias x) (d.canonical p) x.property hq.symm
    refine ⟨p,hz,?_,hlabel.trans hl⟩
    exact Quotient.sound ((quotientMk_eq_iff _ _).mp hq)

end SectorAtlas
#print axioms SectorAtlas.continuous_extendedLabel
#print axioms SectorAtlas.continuous_zeroBiasQuotientLabel
#print axioms SectorAtlas.zeroBiasQuotientLabel_some_covered
end MaxCaterpillar.Fiber.Count65.SectorQuotient
