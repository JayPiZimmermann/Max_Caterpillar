import MaxCaterpillar.Fiber.Count65.ForkExclusion.Defs
import MaxCaterpillar.Fiber.Count65.ForkExclusion.Corner.HingeCertificate

/-! # The symmetric fork requires a negative-output residual gate

Eight exact input samples suffice. The five positive samples have target sum
60; the three negative samples have target sum 66. Their first-feature sums
agree, whereas the universal hinge certificate orders every nonnegative ReLU
sum in the opposite direction. This proves the sign obstruction without a
parameter search or a geometric spurious-wall case split.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion.Corner
open BigOperators MaxCaterpillar.Frontier

def positiveSamples : Fin 5 → Point 3 :=
  ![![0,-24,-12],![0,20,20],![8,-24,8],![20,0,20],![6,12,12]]

def negativeSamples : Fin 3 → Point 3 :=
  ![![-24,12,0],![10,20,30],![24,-36,12]]

noncomputable def positiveValues (d : Coeff) : Fin 5 → ℝ :=
  ![6*d.s,20*d.b+10*d.r,8*d.a+16*d.r+12*d.s,20*d.a+10*d.r,
    6*d.a+12*d.b+3*d.r]

noncomputable def negativeValues (d : Coeff) : Fin 3 → ℝ :=
  ![12*d.b+6*d.r+6*d.s,10*d.a+20*d.b+15*d.r,24*d.a+18*d.r+12*d.s]

noncomputable def sumP (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∑ j : Fin 5, f (positiveSamples j 0) (positiveSamples j 1) (positiveSamples j 2)

noncomputable def sumN (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∑ j : Fin 3, f (negativeSamples j 0) (negativeSamples j 1) (negativeSamples j 2)

lemma form_positive_sample (d : Coeff) (j : Fin 5) :
    form (1/2) (1/2) (1/2) d (positiveSamples j 0) (positiveSamples j 1)
      (positiveSamples j 2)=positiveValues d j := by
  fin_cases j <;> norm_num [positiveSamples,positiveValues,form,relu] <;> ring

lemma form_negative_sample (d : Coeff) (j : Fin 3) :
    form (1/2) (1/2) (1/2) d (negativeSamples j 0) (negativeSamples j 1)
      (negativeSamples j 2)=negativeValues d j := by
  fin_cases j <;> norm_num [negativeSamples,negativeValues,form,relu] <;> ring

lemma sample_base_balance (d : Coeff) :
    sumP (form (1/2) (1/2) (1/2) d)=sumN (form (1/2) (1/2) (1/2) d) := by
  unfold sumP sumN
  simp_rw [form_positive_sample,form_negative_sample]
  simp only [positiveValues,negativeValues,Fin.sum_univ_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,
    Fin.sum_univ_zero,add_zero]
  ring

lemma sample_hinge_dominance (d : Coeff) :
    sumN (fun u v w => relu (form (1/2) (1/2) (1/2) d u v w)) ≤
      sumP (fun u v w => relu (form (1/2) (1/2) (1/2) d u v w)) := by
  unfold sumP sumN
  simp_rw [form_positive_sample,form_negative_sample]
  simp only [positiveValues,negativeValues,Fin.sum_univ_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,
    Fin.sum_univ_zero,add_zero]
  convert symmetric_fork_hinge_certificate d.a d.b d.r d.s using 1 <;> ring

lemma sample_target_pos : sumP target=60 := by
  norm_num [sumP,positiveSamples,target,Fin.sum_univ_succ]

lemma sample_target_neg : sumN target=66 := by
  norm_num [sumN,negativeSamples,target,Fin.sum_univ_succ]

lemma sumP_eval {ι : Type*} [Fintype ι] (d : ResidualSystem ι) :
    sumP (d.eval (1/2) (1/2) (1/2)) =
      sumP (form (1/2) (1/2) (1/2) d.base)+
        ∑ i, d.out i*sumP (fun u v w => relu (form (1/2) (1/2) (1/2) (d.gate i) u v w)) := by
  unfold sumP ResidualSystem.eval
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

lemma sumN_eval {ι : Type*} [Fintype ι] (d : ResidualSystem ι) :
    sumN (d.eval (1/2) (1/2) (1/2)) =
      sumN (form (1/2) (1/2) (1/2) d.base)+
        ∑ i, d.out i*sumN (fun u v w => relu (form (1/2) (1/2) (1/2) (d.gate i) u v w)) := by
  unfold sumN ResidualSystem.eval
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- No finite nonnegative sum of residual ReLUs computes the symmetric fork.
The linear feature remainder and all preactivation coefficients are arbitrary. -/
theorem not_represents_corner_of_nonnegative {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (hn : ∀ i, 0 ≤ d.out i) :
    ¬ d.Represents (1/2) (1/2) (1/2) := by
  intro h
  have hp : 60=sumP (form (1/2) (1/2) (1/2) d.base)+
      ∑ i, d.out i*sumP (fun u v w => relu (form (1/2) (1/2) (1/2) (d.gate i) u v w)) := by
    calc
      60=sumP target := sample_target_pos.symm
      _=sumP (d.eval (1/2) (1/2) (1/2)) := by
        unfold sumP
        exact Finset.sum_congr rfl fun j _ => h _ _ _
      _=_ := sumP_eval d
  have hm : 66=sumN (form (1/2) (1/2) (1/2) d.base)+
      ∑ i, d.out i*sumN (fun u v w => relu (form (1/2) (1/2) (1/2) (d.gate i) u v w)) := by
    calc
      66=sumN target := sample_target_neg.symm
      _=sumN (d.eval (1/2) (1/2) (1/2)) := by
        unfold sumN
        exact Finset.sum_congr rfl fun j _ => h _ _ _
      _=_ := sumN_eval d
  have hle : (∑ i, d.out i*sumN (fun u v w => relu (form (1/2) (1/2) (1/2) (d.gate i) u v w))) ≤
      ∑ i, d.out i*sumP (fun u v w => relu (form (1/2) (1/2) (1/2) (d.gate i) u v w)) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (sample_hinge_dominance (d.gate i)) (hn i)
  have hb := sample_base_balance d.base
  linarith only [hp,hm,hle,hb]

/-- Every exact symmetric-corner residual identity has a negative-output gate. -/
theorem exists_negative_corner {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (h : d.Represents (1/2) (1/2) (1/2)) :
    ∃ i, d.out i < 0 := by
  by_contra hn
  apply not_represents_corner_of_nonnegative d _ h
  intro i
  exact le_of_not_gt (fun hi => hn ⟨i,hi⟩)

#check @exists_negative_corner
#print axioms not_represents_corner_of_nonnegative
#print axioms exists_negative_corner
end MaxCaterpillar.Fiber.Count65.ForkExclusion.Corner

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion

/-- Public method form of the finite eight-sample corner obstruction. -/
theorem ResidualSystem.exists_negative_corner {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (h : d.Represents (1/2) (1/2) (1/2)) :
    ∃ i, d.out i < 0 := Corner.exists_negative_corner d h

#print axioms ResidualSystem.exists_negative_corner
end MaxCaterpillar.Fiber.Count65.ForkExclusion
