import research.sN.exponential_push_20261102.ridge_annihilator.NoRidgeSum
import Mathlib.LinearAlgebra.FreeModule.Finite.Rank

/-! A low-dimensional linear observation always has a non-diagonal kernel
direction. Consequently arbitrary functions of such observations cannot sum
to the actual maximum, even with an affine remainder. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.Ridge
open BigOperators

variable {N : ℕ} [NeZero N]

/-- The codomain may contain fewer than `N−1` observed real degrees of freedom.
Appending one input coordinate proves the kernel has a non-diagonal vector. -/
theorem exists_nondiagonal_ker_of_finrank
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (hN : 2 ≤ N) (A : Point N →ₗ[ℝ] E)
    (hA : FiniteDimensional.finrank ℝ E ≤ N - 2) :
    ∃ v : Point N, A v = 0 ∧ ∃ i j, v i ≠ v j := by
  classical
  let z : Fin N := ⟨0, by omega⟩
  let B : Point N →ₗ[ℝ] E × ℝ := A.prod (LinearMap.proj z)
  have hnot : ¬ Function.Injective B := by
    intro hi
    have hd := LinearMap.finrank_le_finrank_of_injective hi
    have hn : N ≤ FiniteDimensional.finrank ℝ E + 1 := by
      simpa only [Point,FiniteDimensional.finrank_fin_fun,
        FiniteDimensional.finrank_prod,FiniteDimensional.finrank_self] using hd
    omega
  unfold Function.Injective at hnot
  push_neg at hnot
  obtain ⟨x,y,hB,hxy⟩ := hnot
  have hAxy : A x = A y := congrArg Prod.fst hB
  have hz : x z = y z := congrArg Prod.snd hB
  refine ⟨x-y, ?_, ?_⟩
  · rw [map_sub,hAxy,sub_self]
  · by_contra h
    push_neg at h
    apply hxy
    apply sub_eq_zero.mp
    funext i
    have hi := h i z
    simp only [Pi.sub_apply] at hi
    change x i - y i = 0
    linarith

/-- A scalar observation vector with at most `N−2` entries is a special case. -/
theorem exists_nondiagonal_ker_of_row_count {K : ℕ}
    (hN : 2 ≤ N) (A : Point N →ₗ[ℝ] (Fin K → ℝ)) (hK : K ≤ N - 2) :
    ∃ v : Point N, A v = 0 ∧ ∃ i j, v i ≠ v j :=
  exists_nondiagonal_ker_of_finrank hN A
    (by simpa only [FiniteDimensional.finrank_fin_fun] using hK)

/-- Arbitrary functions of separate low-dimensional linear observations do
not represent the maximum. No regularity is required of the outer functions. -/
theorem maximum_ne_affine_sum_of_lowdim_observations
    {J : Type*} [Fintype J] (E : J → Type*)
    [∀ j, AddCommGroup (E j)] [∀ j, Module ℝ (E j)]
    [∀ j, FiniteDimensional ℝ (E j)]
    (hN : 2 ≤ N) (A : ∀ j, Point N →ₗ[ℝ] E j) (F : ∀ j, E j → ℝ)
    (hA : ∀ j, FiniteDimensional.finrank ℝ (E j) ≤ N - 2)
    (a : Point N →+ ℝ) (c : ℝ) :
    ¬ ∀ x, Maximum N x = a x + c + ∑ j, F j (A j x) := by
  apply maximum_ne_affine_sum_of_exists_periods hN (fun j x => F j (A j x))
    ?_ a c
  intro j
  obtain ⟨v,hv,hnd⟩ := exists_nondiagonal_ker_of_finrank hN (A j) (hA j)
  refine ⟨v,hnd,?_⟩
  intro x
  dsimp only
  rw [map_add,hv,add_zero]

/-- The actual rank of the observation map suffices; redundant output
coordinates impose no restriction. -/
theorem maximum_ne_affine_sum_of_lowrank_observations
    {J : Type*} [Fintype J] (E : J → Type*)
    [∀ j, AddCommGroup (E j)] [∀ j, Module ℝ (E j)]
    (hN : 2 ≤ N) (A : ∀ j, Point N →ₗ[ℝ] E j) (F : ∀ j, E j → ℝ)
    (hA : ∀ j, FiniteDimensional.finrank ℝ (LinearMap.range (A j)) ≤ N - 2)
    (a : Point N →+ ℝ) (c : ℝ) :
    ¬ ∀ x, Maximum N x = a x + c + ∑ j, F j (A j x) := by
  exact maximum_ne_affine_sum_of_lowdim_observations
    (fun j => LinearMap.range (A j)) hN (fun j => (A j).rangeRestrict)
    (fun j y => F j y) hA a c

/-- Every exact such representation contains an original observation map
whose rank is at least `N−1`. -/
theorem exists_highrank_observation_of_maximum
    {J : Type*} [Fintype J] (E : J → Type*)
    [∀ j, AddCommGroup (E j)] [∀ j, Module ℝ (E j)]
    (hN : 2 ≤ N) (A : ∀ j, Point N →ₗ[ℝ] E j) (F : ∀ j, E j → ℝ)
    (a : Point N →+ ℝ) (c : ℝ)
    (hmax : ∀ x, Maximum N x = a x + c + ∑ j, F j (A j x)) :
    ∃ j, N - 1 ≤ FiniteDimensional.finrank ℝ (LinearMap.range (A j)) := by
  by_contra! h
  apply maximum_ne_affine_sum_of_lowrank_observations E hN A F ?_ a c hmax
  intro j
  have hj := h j
  have hh := Nat.le_pred_of_lt hj
  simpa only [Nat.pred_eq_sub_one,Nat.sub_sub] using hh

#check @exists_nondiagonal_ker_of_finrank
#check @maximum_ne_affine_sum_of_lowrank_observations
#print axioms exists_nondiagonal_ker_of_finrank
#print axioms exists_nondiagonal_ker_of_row_count
#print axioms maximum_ne_affine_sum_of_lowdim_observations
#print axioms maximum_ne_affine_sum_of_lowrank_observations
#print axioms exists_highrank_observation_of_maximum
end MaxCaterpillar.ExponentialPush.Ridge
