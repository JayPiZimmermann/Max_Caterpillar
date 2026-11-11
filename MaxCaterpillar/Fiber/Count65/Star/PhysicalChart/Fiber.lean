import MaxCaterpillar.Fiber.Count65.Star.PhysicalChart.Core
import MaxCaterpillar.Fiber.Symmetry

/-! # Continuous charts into the actual exact fiber and its symmetry quotient -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star.PhysicalChart

noncomputable def branchIExact (o : Fin 3→Bool) (p : BranchIFiber o) : ExactFiber 4 6 5 :=
  ⟨branchIChart o p,branchIChart_eval o p⟩
noncomputable def branchIIExact (o : Fin 3→Bool) (p : BranchIIFiber o) : ExactFiber 4 6 5 :=
  ⟨branchIIChart o p,branchIIChart_eval o p⟩

lemma continuous_branchIExact (o : Fin 3→Bool) : Continuous (branchIExact o) :=
  (continuous_branchIChart o).subtype_mk _
lemma continuous_branchIIExact (o : Fin 3→Bool) : Continuous (branchIIExact o) :=
  (continuous_branchIIChart o).subtype_mk _

noncomputable def branchIQuotient (o : Fin 3→Bool) : BranchIFiber o→SymmetryQuotient 4 6 5 :=
  fun p => quotientMk (branchIExact o p)
noncomputable def branchIIQuotient (o : Fin 3→Bool) : BranchIIFiber o→SymmetryQuotient 4 6 5 :=
  fun p => quotientMk (branchIIExact o p)

lemma continuous_branchIQuotient (o : Fin 3→Bool) : Continuous (branchIQuotient o) :=
  quotientMk_continuous.comp (continuous_branchIExact o)
lemma continuous_branchIIQuotient (o : Fin 3→Bool) : Continuous (branchIIQuotient o) :=
  quotientMk_continuous.comp (continuous_branchIIExact o)
end MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
