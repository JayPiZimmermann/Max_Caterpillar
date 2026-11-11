import MaxCaterpillar.Fiber.Mixed65.ThreeGateOrdering
import MaxCaterpillar.Fiber.Mixed65.Residual

/-! # Nonvacuous canonical witnesses for both residual branches

The structures are actual coefficient systems on the original four features.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Mixed65
open BigOperators MaxCaterpillar.Frontier

noncomputable def canonicalResidualA (t k : ℝ) : ResidualSystem (Fin 3) where
  lU := 1
  lV := 1
  lW := 0
  lT := 0
  out := ![1,1,-1]
  U := ![-(1+t),-1,-(1+t)]
  V := ![0,-1,0]
  W := ![1,1,1]
  T := ![1,k,k+1]

noncomputable def canonicalResidualB (t r : ℝ) : ResidualSystem (Fin 3) where
  lU := 1+t
  lV := 0
  lW := 0
  lT := -1
  out := ![1,1,-1]
  U := ![-(1+t),-1,-1]
  V := ![r,-1,r-1]
  W := ![1,1,1]
  T := ![1,0,0]

lemma canonicalResidualA_represents (t k : ℝ) (ht : 0 < t) (hk : 1 ≤ t*k) :
    (canonicalResidualA t k).Represents t := by
  intro q b c
  have h := residualA t k q b (relu c) ht hk (relu_nonneg c)
  symm
  convert h using 1 <;>
    norm_num [ResidualSystem.base,ResidualSystem.gate,form,canonicalResidualA,
      Fin.sum_univ_succ] <;> ring

lemma canonicalResidualB_represents (t r : ℝ) (ht : 0 < t) (hr : 1+t ≤ t*r) :
    (canonicalResidualB t r).Represents t := by
  intro q b c
  have h := residualB t r q b (relu c) ht hr (relu_nonneg c)
  symm
  convert h using 1 <;>
    norm_num [ResidualSystem.base,ResidualSystem.gate,form,canonicalResidualB,
      Fin.sum_univ_succ] <;> ring

/-- Reverse any selected cores and absorb their linear parts in the remainder. -/
noncomputable def ResidualSystem.flip {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (bits : ι → Bool) : ResidualSystem ι where
  lU := d.lU + ∑ i, if bits i then d.out i*d.U i else 0
  lV := d.lV + ∑ i, if bits i then d.out i*d.V i else 0
  lW := d.lW + ∑ i, if bits i then d.out i*d.W i else 0
  lT := d.lT + ∑ i, if bits i then d.out i*d.T i else 0
  out := d.out
  U := fun i => if bits i then -d.U i else d.U i
  V := fun i => if bits i then -d.V i else d.V i
  W := fun i => if bits i then -d.W i else d.W i
  T := fun i => if bits i then -d.T i else d.T i

lemma ResidualSystem.flip_gate {ι : Type*} [Fintype ι] (d : ResidualSystem ι)
    (bits : ι → Bool) (t : ℝ) (i : ι) (q b c : ℝ) :
    (d.flip bits).gate t i q b c = if bits i then -d.gate t i q b c else d.gate t i q b c := by
  cases hb : bits i <;> simp [ResidualSystem.flip,ResidualSystem.gate,form,hb] <;> ring

lemma ResidualSystem.flip_base {ι : Type*} [Fintype ι] (d : ResidualSystem ι)
    (bits : ι → Bool) (t q b c : ℝ) :
    (d.flip bits).base t q b c = d.base t q b c +
      ∑ i, if bits i then d.out i*d.gate t i q b c else 0 := by
  have hs : (∑ i, if bits i then d.out i*d.gate t i q b c else 0) =
      (∑ i, if bits i then d.out i*d.U i else 0)*relu q +
      (∑ i, if bits i then d.out i*d.V i else 0)*relu b +
      (∑ i, if bits i then d.out i*d.W i else 0)*relu c +
      (∑ i, if bits i then d.out i*d.T i else 0)*relu (t*q-b) := by
    simp only [Finset.sum_mul]
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases hbi : bits i <;> simp [ResidualSystem.gate,form,hbi] <;> ring
  rw [hs]
  simp only [ResidualSystem.base,ResidualSystem.flip,form]
  ring

lemma ResidualSystem.flip_represents {ι : Type*} [Fintype ι] (d : ResidualSystem ι)
    (bits : ι → Bool) (t : ℝ) (h : d.Represents t) : (d.flip bits).Represents t := by
  intro q b c
  rw [d.flip_base bits t q b c]
  simp_rw [d.flip_gate bits t]
  have hsum : (∑ i, if bits i then d.out i*d.gate t i q b c else 0) +
      (∑ i, d.out i*relu (if bits i then -d.gate t i q b c else d.gate t i q b c)) =
      ∑ i, d.out i*relu (d.gate t i q b c) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hi := orientation_identity (d.gate t i q b c) (bits i)
    cases hb : bits i
    · simp [hb]
    · simp [hb] at hi ⊢
      linear_combination d.out i*hi
  change _ = (d.base t q b c +
    (∑ i, if bits i then d.out i*d.gate t i q b c else 0)) +
    ∑ i, d.out i*relu (if bits i then -d.gate t i q b c else d.gate t i q b c)
  rw [add_assoc,hsum]
  exact h q b c

/-- All eight orientation choices in each branch have all-input witnesses. -/
theorem canonical_residuals_all_orientations (bits : Fin 3 → Bool) :
    ((canonicalResidualA 1 1).flip bits).Represents 1 ∧
      ((canonicalResidualB 1 2).flip bits).Represents 1 := by
  constructor
  · exact (canonicalResidualA 1 1).flip_represents bits 1
      (canonicalResidualA_represents 1 1 (by norm_num) (by norm_num))
  · exact (canonicalResidualB 1 2).flip_represents bits 1
      (canonicalResidualB_represents 1 2 (by norm_num) (by norm_num))

end MaxCaterpillar.Fiber.Mixed65
