import MaxNN.Constructions.Paramid.Geom.Germ.Radial
import MaxNN.Constructions.Paramid.Geom.UnitGerm

/-! # Reflection symmetry forces a linear facet datum

DFS branch for braid cancellation: a function in the support-function span
that is invariant under a linear reflection, even up to a linear summand, has
linear two-sided germ in the reflected direction. This statement does not
assume that a particular caterpillar combination has the required symmetry.
-/

namespace MaxNN.ParamidGeom

variable {m : ℕ}

/-- Reflection along `u`, fixing the kernel of `dot b`, when `dot b u = 1`. -/
noncomputable def reflectAlong (u b : Fin m → ℝ) : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  LinearMap.id - (2 : ℝ) • (SupportCut.dotL b).smulRight u

theorem reflectAlong_apply (u b y : Fin m → ℝ) :
    reflectAlong u b y = y - (2 * dot b y) • u := by
  change y - (2 : ℝ) • (dot b y • u) = _
  rw [smul_smul]

theorem reflectAlong_self (u b : Fin m → ℝ) (hbu : dot b u = 1) :
    reflectAlong u b u = -u := by
  rw [reflectAlong_apply, hbu, mul_one]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- Symmetry up to a linear summand suffices. This form also handles reduced
simplex coordinates, where a vertex permutation may change the linear part. -/
theorem germDiff_eq_dot_of_reflection_add_linear {f : (Fin m → ℝ) → ℝ}
    (hf : f ∈ SSpan m) (u b a : Fin m → ℝ) (hbu : dot b u = 1)
    (hsym : ∀ y, f (reflectAlong u b y) = f y + dot a y) :
    germDiff u f = dot ((2 * f (-u)) • b - a) := by
  have he : (fun y => f (reflectAlong u b y)) = f + dot a := funext hsym
  have hg := germ_eq_of_isGerm
    ((isGerm_germ_of_mem_SSpan hf (reflectAlong u b u)).comp_linearMap (reflectAlong u b) u)
  rw [he, reflectAlong_self u b hbu,
    germ_add hf (GermAux.dot_mem_SSpan a), germ_dot] at hg
  funext y
  have hy := congrFun hg y
  change germ f u y + dot a y = germ f (-u) (reflectAlong u b y) at hy
  have hr : reflectAlong u b y = y + (2 * dot b y) • (-u) := by
    rw [reflectAlong_apply, smul_neg, sub_eq_add_neg]
  rw [hr, germ_add_smul_direction hf] at hy
  change germ f u y - germ f (-u) y = dot ((2 * f (-u)) • b - a) y
  rw [SupportCut.dot_sub_left, SupportCut.dot_smul_left]
  nlinarith only [hy]

theorem germDiff_mem_LSpan_zero_of_reflection_add_linear {f : (Fin m → ℝ) → ℝ}
    (hf : f ∈ SSpan m) (u b a : Fin m → ℝ) (hbu : dot b u = 1)
    (hsym : ∀ y, f (reflectAlong u b y) = f y + dot a y) :
    germDiff u f ∈ LSpan m 0 := by
  rw [germDiff_eq_dot_of_reflection_add_linear hf u b a hbu hsym]
  exact UnitGermAux.dot_mem_LSpan _ _

/-- Exact reflection invariance gives an explicit linear germ difference. -/
theorem germDiff_eq_dot_of_reflection {f : (Fin m → ℝ) → ℝ}
    (hf : f ∈ SSpan m) (u b : Fin m → ℝ) (hbu : dot b u = 1)
    (hsym : ∀ y, f (reflectAlong u b y) = f y) :
    germDiff u f = dot ((2 * f u) • b) := by
  have hneg : f (-u) = f u := by
    have h := hsym u
    rwa [reflectAlong_self u b hbu] at h
  have hlin : ∀ y, f (reflectAlong u b y) = f y + dot (0 : Fin m → ℝ) y := by
    intro y
    simp only [hsym, dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  rw [germDiff_eq_dot_of_reflection_add_linear hf u b 0 hbu hlin, sub_zero, hneg]

end MaxNN.ParamidGeom
