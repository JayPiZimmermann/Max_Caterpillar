import MaxCaterpillar.Fiber.Count65.MatrixForms
import MaxCaterpillar.Fiber.First65
import MaxCaterpillar.Fiber.Mixed65.SectorNormalForm
import MaxCaterpillar.Fiber.Star65.Construction

/-! # First-hidden-layer normal forms for the Max4 component classification

The predicates below describe actual first weight matrices, with positive
scales and finite permutations explicit.  No exhaustiveness of these forms
is built into their definitions. The global network-to-normal-form theorem
is a separate obligation.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65

open MaxCaterpillar.Frontier

/-- The mutually distinct coefficient ranges left by the path-facet test. -/
inductive PathCoefficientCase : ℝ → ℝ → Prop
  | wall {ν : ℝ} (hν : ν < 0) : PathCoefficientCase 0 ν
  | mixed {μ ν : ℝ} (hμ : 0 < μ) (hν : ν < 0) : PathCoefficientCase μ ν
  | star {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hνμ : ν ≤ μ) :
      PathCoefficientCase μ ν

/-- Once the fourth path row is nonzero and distinct from the existing
positive root, the active-facet condition has exactly these three ranges.
This is a coefficient theorem; the separate active-facet bridge is not assumed. -/
theorem path_coefficient_cases (μ ν : ℝ)
    (hfacet : ∀ a b : ℝ, 0 < a → b < 0 → 0 ≤ μ * a + (ν - μ) * b)
    (hν : ν ≠ 0) : PathCoefficientCase μ ν := by
  obtain ⟨hμ, hνμ⟩ := (path_facet_nonneg_iff μ ν).mp hfacet
  rcases lt_or_eq_of_le hμ with hμ | hμ
  · rcases lt_or_gt_of_ne hν with hneg | hpos
    · exact PathCoefficientCase.mixed hμ hneg
    · exact PathCoefficientCase.star hμ hpos hνμ
  · subst μ
    exact PathCoefficientCase.wall (lt_of_le_of_ne hνμ hν)

/-- Normalizing a positive coefficient produces the star parameter range. -/
theorem star_path_parameter {μ ν : ℝ} (hμ : 0 < μ)
    (hν : 0 < ν) (hνμ : ν ≤ μ) :
    0 < ν / μ ∧ ν / μ ≤ 1 ∧ ν = μ * (ν / μ) := by
  exact ⟨div_pos hν hμ, (div_le_one hμ).mpr hνμ,
    (mul_div_cancel' ν hμ.ne').symm⟩

/-- Normalizing a negative coefficient produces the mixed parameter range. -/
theorem mixed_path_parameter {μ ν : ℝ} (hμ : 0 < μ) (hν : ν < 0) :
    0 < -ν / μ ∧ ν = -μ * (-ν / μ) := by
  constructor
  · exact div_pos (neg_pos.mpr hν) hμ
  · field_simp
    ring

end MaxCaterpillar.Fiber.Count65
