import MaxCaterpillar.Fiber.Count65.SectorQuotient.NormalizedOrbit
import MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsSymmetry
import MaxCaterpillar.Fiber.Count65.Star.ActualLabelsPermutation

/-! Canonical actual labels are invariant under the entire genuine quotient,
not only under a separately imposed relation on canonical parameters. -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

def canonicalMixedFiber (p : ActualMixedLabels.Slice) : ExactFiber 4 6 5 :=
  ⟨p.val.2,p.property.2.2.1⟩
def canonicalStarFiber (p : ActualStarLabels.Slice) : ExactFiber 4 6 5 :=
  ⟨p.val.2,p.property.2.2.2.1⟩

theorem mixed_componentLabel_eq_of_quotientMk_eq (a b : ActualMixedLabels.Slice)
    (h : quotientMk (canonicalMixedFiber a)=quotientMk (canonicalMixedFiber b)) :
    ActualMixedLabels.componentLabel a=ActualMixedLabels.componentLabel b := by
  have he := (quotientMk_eq_iff _ _).mp h
  obtain ⟨ht,p,hp⟩ := (mixed_normalized_symmetry_iff
    (canonicalMixedFiber a) (canonicalMixedFiber b) a.val.1 b.val.1
    a.property.1 b.property.1 a.property.2.1 b.property.2.1
    a.property.2.2.2 b.property.2.2.2).mp he
  have hb : b=ActualMixedLabels.permutePhysical p a :=
    Subtype.ext (Prod.ext ht.symm hp)
  rw [hb]
  exact (ActualMixedLabels.componentLabel_permutePhysical p a).symm

theorem star_componentLabel_eq_of_quotientMk_eq (a b : ActualStarLabels.Slice)
    (h : quotientMk (canonicalStarFiber a)=quotientMk (canonicalStarFiber b)) :
    ActualStarLabels.componentLabel a=ActualStarLabels.componentLabel b := by
  have he := (quotientMk_eq_iff _ _).mp h
  obtain ⟨ht,p,hp⟩ := (star_normalized_symmetry_iff
    (canonicalStarFiber a) (canonicalStarFiber b) a.val.1 b.val.1
    a.property.1 a.property.2.1 b.property.1 b.property.2.1
    a.property.2.2.1 b.property.2.2.1
    a.property.2.2.2.2 b.property.2.2.2.2).mp he
  have hb : b=ActualStarLabels.permuteNormalized a p :=
    Subtype.ext (Prod.ext ht.symm hp)
  rw [hb]
  exact (ActualStarLabels.componentLabel_permuteNormalized a p).symm

#print axioms mixed_componentLabel_eq_of_quotientMk_eq
#print axioms star_componentLabel_eq_of_quotientMk_eq
end MaxCaterpillar.Fiber.Count65.SectorQuotient
