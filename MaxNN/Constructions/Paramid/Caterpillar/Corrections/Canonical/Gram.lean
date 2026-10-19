import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# A canonical Gram form for homogeneous correction functions

Integration over the closed unit ball separates continuous positively
homogeneous real functions.  This supplies an exact, positive-definite Gram
form for the finite correction dictionary without evaluating at chosen sample
points.
-/

open BigOperators MeasureTheory Metric Set

namespace MaxNN.Caterpillar.Corrections.Canonical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- Continuity and positive homogeneity, kept as a predicate so it applies
directly to the existing function definitions. -/
def IsPosHomContinuous (f : E → ℝ) : Prop :=
  Continuous f ∧ ∀ (c : ℝ), 0 ≤ c → ∀ x, f (c • x) = c * f x

theorem IsPosHomContinuous.zero :
    IsPosHomContinuous (fun _ : E ↦ (0 : ℝ)) := by
  refine ⟨continuous_const, fun c _ x ↦ ?_⟩
  simp

theorem IsPosHomContinuous.add {f g : E → ℝ}
    (hf : IsPosHomContinuous f) (hg : IsPosHomContinuous g) :
    IsPosHomContinuous (fun x ↦ f x + g x) := by
  refine ⟨hf.1.add hg.1, fun c hc x ↦ ?_⟩
  change f (c • x) + g (c • x) = c * (f x + g x)
  rw [hf.2 c hc x, hg.2 c hc x]
  ring

theorem IsPosHomContinuous.smul (a : ℝ) {f : E → ℝ}
    (hf : IsPosHomContinuous f) :
    IsPosHomContinuous (fun x ↦ a * f x) := by
  refine ⟨continuous_const.mul hf.1, fun c hc x ↦ ?_⟩
  change a * f (c • x) = c * (a * f x)
  rw [hf.2 c hc x]
  ring

/-- The exact Gram form used for canonical coefficients. -/
noncomputable def ballInner (f g : E → ℝ) : ℝ :=
  ∫ x in closedBall (0 : E) 1, f x * g x

theorem ballInner_self_nonneg (f : E → ℝ) :
    0 ≤ ballInner f f := by
  exact set_integral_nonneg_of_ae
    (ae_of_all volume fun x ↦ mul_self_nonneg (f x))

/-- The closed-unit-ball Gram form separates continuous positively homogeneous
functions. -/
theorem ballInner_self_eq_zero_iff [Nontrivial E] {f : E → ℝ}
    (hf : IsPosHomContinuous f) :
    ballInner f f = 0 ↔ f = 0 := by
  constructor
  · intro hzero
    unfold ballInner at hzero
    have hint : IntegrableOn (fun x ↦ f x * f x) (closedBall (0 : E) 1) volume :=
      (hf.1.mul hf.1).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : E) 1)
    have hae : (fun x ↦ f x * f x) =ᵐ[volume.restrict (closedBall (0 : E) 1)] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun x ↦ mul_self_nonneg (f x)) hint).mp hzero
    have hclosure : closedBall (0 : E) 1 ⊆
        closure (interior (closedBall (0 : E) 1)) := by
      rw [interior_closedBall (0 : E) one_ne_zero, closure_ball (0 : E) one_ne_zero]
    have hsquare : EqOn (fun x ↦ f x * f x) 0 (closedBall (0 : E) 1) :=
      volume.eqOn_of_ae_eq hae (hf.1.mul hf.1).continuousOn
        continuous_const.continuousOn hclosure
    funext x
    let c : ℝ := (1 + ‖x‖)⁻¹
    have hcpos : 0 < c := inv_pos.mpr (by positivity)
    have hcx : c • x ∈ closedBall (0 : E) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
      dsimp [c]
      rw [inv_mul_le_iff (by positivity)]
      linarith [norm_nonneg x]
    have hsq : f (c • x) * f (c • x) = 0 := hsquare hcx
    have hfcx : f (c • x) = 0 := (mul_self_eq_zero.mp hsq)
    rw [hf.2 c hcpos.le x] at hfcx
    exact (mul_eq_zero.mp hfcx).resolve_left hcpos.ne'
  · rintro rfl
    simp [ballInner]

section Finite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite linear combination, as an actual function. -/
def lincomb (v : ι → E → ℝ) (c : ι → ℝ) : E → ℝ :=
  fun x ↦ ∑ i, c i * v i x

theorem lincomb_posHomContinuous {v : ι → E → ℝ}
    (hv : ∀ i, IsPosHomContinuous (v i)) (c : ι → ℝ) :
    IsPosHomContinuous (lincomb v c) := by
  have hterm : ∀ i, IsPosHomContinuous (fun x ↦ c i * v i x) :=
    fun i ↦ (hv i).smul (c i)
  refine ⟨?_, fun a ha x ↦ ?_⟩
  · simpa only [lincomb] using
      (continuous_finset_sum Finset.univ fun i _ ↦ (hterm i).1)
  change (∑ i, c i * v i (a • x)) = a * ∑ i, c i * v i x
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (hterm i).2 a ha x

private theorem product_integrableOn (f g : E → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    IntegrableOn (fun x ↦ f x * g x) (closedBall (0 : E) 1) volume :=
  (hf.mul hg).continuousOn.integrableOn_compact (isCompact_closedBall (0 : E) 1)

theorem ballInner_lincomb_left (v : ι → E → ℝ)
    (hv : ∀ i, Continuous (v i)) (c : ι → ℝ) (g : E → ℝ)
    (hg : Continuous g) :
    ballInner (lincomb v c) g = ∑ i, c i * ballInner (v i) g := by
  unfold ballInner lincomb
  have he : (fun x ↦ (∑ i, c i * v i x) * g x) =
      fun x ↦ ∑ i, c i * (v i x * g x) := by
    funext x
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [he, integral_finset_sum Finset.univ]
  · exact Finset.sum_congr rfl fun i _ ↦ integral_mul_left (c i) _
  · intro i _
    exact (product_integrableOn (v i) g (hv i) hg).const_mul (c i)

theorem ballInner_comm (f g : E → ℝ) : ballInner f g = ballInner g f := by
  unfold ballInner
  congr 1
  funext x
  exact mul_comm _ _

theorem ballInner_lincomb_right (v : ι → E → ℝ)
    (hv : ∀ i, Continuous (v i)) (c : ι → ℝ) (f : E → ℝ)
    (hf : Continuous f) :
    ballInner f (lincomb v c) = ∑ i, c i * ballInner f (v i) := by
  rw [ballInner_comm, ballInner_lincomb_left v hv c f hf]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [ballInner_comm]

/-- The exact Gram matrix of a finite homogeneous dictionary. -/
noncomputable def gramMatrix (v : ι → E → ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ ballInner (v i) (v j)

theorem dotProduct_gram_mulVec (v : ι → E → ℝ)
    (hv : ∀ i, Continuous (v i)) (c : ι → ℝ) :
    Matrix.dotProduct c ((gramMatrix v).mulVec c) =
      ballInner (lincomb v c) (lincomb v c) := by
  have hcont : Continuous (lincomb v c) := by
    simpa only [lincomb] using
      (continuous_finset_sum Finset.univ fun i _ ↦ continuous_const.mul (hv i))
  rw [ballInner_lincomb_left v hv c (lincomb v c) hcont]
  unfold Matrix.dotProduct
  apply Finset.sum_congr rfl
  intro i _
  change c i * ((gramMatrix v).mulVec c i) =
    c i * ballInner (v i) (lincomb v c)
  congr 1
  unfold Matrix.mulVec gramMatrix
  dsimp only
  rw [ballInner_lincomb_right v hv c (v i) (hv i)]
  unfold Matrix.dotProduct
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-- A Gram matrix of a linearly independent homogeneous dictionary is a unit,
so its nonsingular inverse is an actual inverse. -/
theorem gramMatrix_isUnit [Nontrivial E] (v : ι → E → ℝ)
    (hv : ∀ i, IsPosHomContinuous (v i)) (hli : LinearIndependent ℝ v) :
    IsUnit (gramMatrix v) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro c d hcd
  have hz : (gramMatrix v).mulVec (c - d) = 0 := by
    funext i
    change Matrix.dotProduct (gramMatrix v i) (c - d) = 0
    rw [Matrix.dotProduct_sub]
    have hi := congrFun hcd i
    change Matrix.dotProduct (gramMatrix v i) c = Matrix.dotProduct (gramMatrix v i) d at hi
    rw [hi, sub_self]
  have hdot := congrArg (Matrix.dotProduct (c - d)) hz
  have hinner : ballInner (lincomb v (c - d)) (lincomb v (c - d)) = 0 := by
    rw [← dotProduct_gram_mulVec v (fun i ↦ (hv i).1)]
    simpa using hdot
  have hfun : lincomb v (c - d) = 0 :=
    (ballInner_self_eq_zero_iff (lincomb_posHomContinuous hv (c - d))).mp hinner
  have hcoef : c - d = 0 := by
    funext i
    apply Fintype.linearIndependent_iff.mp hli (c - d)
    have hs : (∑ j, (c j - d j) • v j) = 0 := by
      funext x
      simpa only [lincomb, Pi.zero_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        Finset.sum_apply] using congrFun hfun x
    exact hs
  exact sub_eq_zero.mp hcoef

/-- The Gram right-hand side against a target function. -/
noncomputable def gramRhs (v : ι → E → ℝ) (f : E → ℝ) : ι → ℝ :=
  fun i ↦ ballInner (v i) f

/-- Coefficients given by the displayed inverse-Gram formula. -/
noncomputable def gramCoeff (v : ι → E → ℝ) (f : E → ℝ) : ι → ℝ :=
  (gramMatrix v)⁻¹.mulVec (gramRhs v f)

theorem gramMatrix_mulVec (v : ι → E → ℝ)
    (hv : ∀ i, Continuous (v i)) (c : ι → ℝ) :
    (gramMatrix v).mulVec c = gramRhs v (lincomb v c) := by
  funext i
  unfold Matrix.mulVec gramMatrix gramRhs
  dsimp only
  rw [ballInner_lincomb_right v hv c (v i) (hv i)]
  unfold Matrix.dotProduct
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-- If an independent dictionary spans the target, its inverse-Gram
coefficients reconstruct the target exactly. -/
theorem lincomb_gramCoeff_eq [Nontrivial E] (v : ι → E → ℝ)
    (hv : ∀ i, IsPosHomContinuous (v i)) (hli : LinearIndependent ℝ v)
    {f : E → ℝ} (hf : ∃ c, f = lincomb v c) :
    lincomb v (gramCoeff v f) = f := by
  obtain ⟨c, rfl⟩ := hf
  have hu := gramMatrix_isUnit v hv hli
  have hudet : IsUnit (gramMatrix v).det :=
    (Matrix.isUnit_iff_isUnit_det (gramMatrix v)).mp hu
  have hrhs := (gramMatrix_mulVec v (fun i ↦ (hv i).1) c).symm
  have hc : gramCoeff v (lincomb v c) = c := by
    unfold gramCoeff
    rw [hrhs, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hudet,
      Matrix.one_mulVec]
  rw [hc]

end Finite

end MaxNN.Caterpillar.Corrections.Canonical
