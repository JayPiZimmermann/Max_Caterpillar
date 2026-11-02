import research.sN.exponential_push_20261102.ridge_annihilator.ContrastSupport
import research.sN.exponential_push_20261102.ridge_annihilator.MaxAnnihilator

/-! Exact maximum functions have no finite annihilator made from
non-diagonal translation differences. In particular they are not finite sums
of functions having non-diagonal periods, even with an affine remainder. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.Ridge
open BigOperators Frontier

variable {N : ℕ} [NeZero N]

theorem contrastBounded_maxCoordinateDifference :
    ContrastBounded (maxCoordinateDifference : Point N → ℝ) := by
  intro i j
  refine ⟨1, ?_⟩
  intro x hx
  exact maxCoordinateDifference_eq_zero_of_abs_contrast x i j hx.le

/-- Every finite product of non-diagonal translation differences is nonzero
on the actual maximum function, at some real input. -/
theorem iterDiff_maximum_ne_zero (vs : List (Point N))
    (hvs : ∀ v ∈ vs, ∃ i j, v i ≠ v j) :
    iterDiff vs (Maximum N) ≠ 0 := by
  intro h
  have hc := iterDiff_maxCoordinateDifference_eq_zero vs h
  have hz := (iterDiff_eq_zero_iff_of_contrastBounded
    (maxCoordinateDifference : Point N → ℝ) contrastBounded_maxCoordinateDifference
    vs hvs).mp hc
  exact maxCoordinateDifference_ne_zero (congrFun hz 0)

/-- Explicit periods and an arbitrary additive affine remainder are allowed.
No continuity, measurability, or diagonal invariance is assumed for a summand. -/
theorem maximum_ne_affine_sum_of_periods {J : Type*} [Fintype J]
    (hN : 2 ≤ N) (f : J → Point N → ℝ) (v : J → Point N)
    (hv : ∀ k, ∃ i j, v k i ≠ v k j)
    (hf : ∀ k x, f k (x + v k) = f k x)
    (a : Point N →+ ℝ) (c : ℝ) :
    ¬ ∀ x, Maximum N x = a x + c + ∑ k, f k x := by
  classical
  intro he
  let z : Fin N := ⟨0, by omega⟩
  let o : Fin N := ⟨1, by omega⟩
  let u : Point N := unitVec z
  have hoz : o ≠ z := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [o, z] at hval
    omega
  have hu : ∃ i j, u i ≠ u j := by
    refine ⟨z, o, ?_⟩
    simp [u, unitVec, hoz]
  let vs : List (Point N) := u :: u :: (Finset.univ.toList.map v)
  have hvs : ∀ w ∈ vs, ∃ i j, w i ≠ w j := by
    intro w hw
    rcases List.mem_cons.mp hw with hw | hw
    · simpa [hw] using hu
    rcases List.mem_cons.mp hw with hw | hw
    · simpa [hw] using hu
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    exact hv k
  have hm : ∀ k ∈ (Finset.univ : Finset J), v k ∈ vs := by
    intro k hk
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    exact ⟨k, by simpa using hk, rfl⟩
  have hsum : iterDiff vs (∑ k, f k) = 0 :=
    iterDiff_sum_eq_zero vs Finset.univ v f hm (fun k _ => hf k)
  have ha : iterDiff vs (fun x => a x + c) = 0 :=
    iterDiff_affine_of_two u u _ a c
  have hfun : Maximum N = (fun x => a x + c) + ∑ k, f k := by
    funext x
    simpa only [Pi.add_apply, Finset.sum_apply] using he x
  apply iterDiff_maximum_ne_zero vs hvs
  rw [hfun, iterDiff_add, ha, hsum, add_zero]

/-- Existential-period formulation: every summand may choose its own period. -/
theorem maximum_ne_affine_sum_of_exists_periods {J : Type*} [Fintype J]
    (hN : 2 ≤ N) (f : J → Point N → ℝ)
    (hf : ∀ k, ∃ v : Point N, (∃ i j, v i ≠ v j) ∧
      ∀ x, f k (x + v) = f k x)
    (a : Point N →+ ℝ) (c : ℝ) :
    ¬ ∀ x, Maximum N x = a x + c + ∑ k, f k x := by
  classical
  choose v hv hinv using hf
  exact maximum_ne_affine_sum_of_periods hN f v hv hinv a c

#check @iterDiff_maximum_ne_zero
#check @maximum_ne_affine_sum_of_exists_periods
#print axioms iterDiff_maximum_ne_zero
#print axioms maximum_ne_affine_sum_of_periods
#print axioms maximum_ne_affine_sum_of_exists_periods
end MaxCaterpillar.ExponentialPush.Ridge
