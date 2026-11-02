import MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsNormalization
import MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsSymmetry
import MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsOrbit
set_option autoImplicit false
noncomputable section
open MaxCaterpillar MaxCaterpillar.Fiber MaxCaterpillar.Fiber.Count65
open ActualMixedLabels

example : Continuous (rawComponentLabel :
    {p : ℝ × Network 4 6 5 // 0<p.1 ∧ p.2.W₁=Mixed65.firstRows p.1 ∧
      (∀ x,p.2.eval x=Maximum 4 x)} → Bool × (Fin 3 → Bool) × Bool) :=
  continuous_rawComponentLabel

example : Continuous (componentLabel :
    {p : ℝ × Network 4 6 5 // 0<p.1 ∧ p.2.W₁=Mixed65.firstRows p.1 ∧
      (∀ x,p.2.eval x=Maximum 4 x) ∧ (∀ i,p.2.w₃ i=1 ∨ p.2.w₃ i = -1)} →
        Bool × (Fin 3 → Bool) × Bool) := continuous_componentLabel

example (p : Slice) : ∃! l : Label,p ∈ physicalClass l := by
  obtain ⟨l,hl⟩ := physicalClasses_exhaustive p
  exact ⟨l,hl,fun m hm => physicalClass_unique p m l hm hl⟩

example (l : Label) : IsClopen (physicalClass l) := isClopen_physicalClass l
example (q : Equiv.Perm (Fin 5)) (p : Slice) :
    componentLabel (permutePhysical q p)=componentLabel p := componentLabel_permutePhysical q p

/-- This continuous classification has an actual all-real network in its domain. -/
def actualRawWitness : RawSlice :=
  ⟨(1,Mixed65.branchANet 1 1),by norm_num,rfl,
    Mixed65.branchANet_eval 1 1 (by norm_num) (by norm_num)⟩
example : ∃ p : RawSlice, ∃ l : Label, normalizePhysical p ∈ physicalClass l :=
  ⟨actualRawWitness,physicalClasses_exhaustive (normalizePhysical actualRawWitness)⟩

#print axioms physicalClasses_exhaustive
#print axioms physicalClass_unique
#print axioms continuous_actualLabel
#print axioms continuous_componentLabel
#print axioms continuous_rawComponentLabel
#print axioms componentLabel_permutePhysical
#print axioms actualRawWitness

example (p : RawSlice) : quotientMk (normalizedExactFiber p)=quotientMk (rawExactFiber p) :=
  normalizePhysical_sameQuotient p
#print axioms normalizePhysical_sameQuotient
