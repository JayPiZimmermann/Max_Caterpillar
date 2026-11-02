import MaxCaterpillar.Fiber.Mixed65.FeatureSpace
import Mathlib.Topology.Homeomorph

/-!
# Physical coefficients and the actual mixed invariant function space

Four exact input evaluations recover the four coefficients. Both maps are
continuous in their ordinary finite-dimensional/subspace topologies; thus the
function-space head component theorem applies to physical readout coefficients.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.MixedFeatureTopology
open MaxCaterpillar.Fiber.Mixed65

noncomputable def coefficientReadout (t : ℝ) (a : Fin 4 → ℝ) : featureSpace t :=
  ⟨readout t (a 0) (a 1) (a 2) (a 3),readout_mem_featureSpace t _ _ _ _⟩

/-- These are actual inputs, with no finite-data identification assumption. -/
noncomputable def recoverReadout (t : ℝ) (f : featureSpace t) : Fin 4 → ℝ :=
  ![f.val (1,t,0)-t*f.val (0,1,0),f.val (0,1,0),f.val (0,0,1),f.val (0,-1,0)]

lemma recover_coefficientReadout {t : ℝ} (ht : 0 < t) (a : Fin 4 → ℝ) :
    recoverReadout t (coefficientReadout t a)=a := by
  funext i
  fin_cases i <;>
    simp only [recoverReadout,coefficientReadout,readout,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,
      Fin.succ_zero_eq_one,Fin.succ_one_eq_two,form_v,form_u,form_w,form_a ht.le]
  all_goals try ring
  all_goals rfl

lemma coefficientReadout_recover {t : ℝ} (ht : 0 < t) (f : featureSpace t) :
    coefficientReadout t (recoverReadout t f)=f := by
  rcases f with ⟨f,A,B,C,D,rfl⟩
  have h := recover_coefficientReadout ht ![A,B,C,D]
  have he : coefficientReadout t ![A,B,C,D]=
      (⟨readout t A B C D,A,B,C,D,rfl⟩ : featureSpace t) := rfl
  rw [← he,h]

lemma continuous_coefficientReadout (t : ℝ) : Continuous (coefficientReadout t) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro x
  have h (i : Fin 4) : Continuous (fun a : Fin 4 → ℝ => a i) := continuous_apply i
  exact ((((h 0).mul continuous_const).add ((h 1).mul continuous_const)).add
    ((h 2).mul continuous_const)).add ((h 3).mul continuous_const)

lemma continuous_recoverReadout (t : ℝ) : Continuous (recoverReadout t) := by
  have h (x : InvariantState) : Continuous (fun f : featureSpace t => f.val x) :=
    (continuous_apply x).comp continuous_subtype_val
  apply continuous_pi
  intro i
  fin_cases i
  · exact (h (1,t,0)).sub (continuous_const.mul (h (0,1,0)))
  · exact h (0,1,0)
  · exact h (0,0,1)
  · exact h (0,-1,0)

/-- The semantic and physical coefficient topologies agree, not just their sets. -/
noncomputable def coefficientReadoutHomeomorph {t : ℝ} (ht : 0 < t) :
    (Fin 4 → ℝ) ≃ₜ featureSpace t where
  toFun := coefficientReadout t
  invFun := recoverReadout t
  left_inv := recover_coefficientReadout ht
  right_inv := coefficientReadout_recover ht
  continuous_toFun := continuous_coefficientReadout t
  continuous_invFun := continuous_recoverReadout t

#print axioms coefficientReadoutHomeomorph
end MaxCaterpillar.Fiber.Count65.MixedFeatureTopology
