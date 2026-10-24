import MaxCaterpillar.Frontier.Basic

/-!
Scratch leaf: the analytic feature-fiber bridge used by overnight_general.md.
This does not assert or formalize the new network width bound.  The support
enumeration, leading-monomial signs, and finite contradictions are separate.
-/

namespace MaxCaterpillar.Frontier.OvernightGeneral

open Filter Topology BigOperators

variable {N m : ℕ} [NeZero N]

/-- If a maximum factors through ReLU features plus a fixed linear form, a
direction annihilating every active row at a strict cell point must have the
same slope under that linear form as under the winning coordinate.
No regularity whatsoever is assumed of `Phi`. -/
theorem feature_fiber_slope
    (rows : Fin m → Point N) (ell : Point N) (Phi : Point m → ℝ)
    (hrep : ∀ x, Maximum N x = lin ell x + Phi (fun j => relu (lin (rows j) x)))
    (q v : Point N) (a : Fin N)
    (hstrict : ∀ j, lin (rows j) q ≠ 0)
    (hactive : ∀ j, 0 < lin (rows j) q → lin (rows j) v = 0)
    (hwin : ∀ i, i ≠ a → q i < q a) : lin ell v = v a := by
  have hfeat : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ j, relu (lin (rows j) (q + ε • v)) = relu (lin (rows j) q) := by
    refine Filter.eventually_all.2 fun j => ?_
    rcases lt_or_gt_of_ne (hstrict j) with hj | hj
    · filter_upwards [eventually_small (lin (rows j) v) (neg_pos.2 hj)] with ε hε
      rw [lin_add_right, lin_smul_right,
        relu_of_nonpos (by linarith [(abs_lt.1 hε).2]), relu_of_nonpos hj.le]
    · exact Filter.eventually_of_forall fun ε => by
        rw [lin_add_right, lin_smul_right, hactive j hj, mul_zero, add_zero]
  have hmax : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ i, (q + ε • v) i ≤ (q + ε • v) a := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : i = a
    · subst i
      exact Filter.eventually_of_forall fun ε => le_rfl
    · filter_upwards [eventually_small (v i - v a) (sub_pos.2 (hwin i hi))] with ε hε
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [(abs_lt.1 hε).2]
  have hall := hfeat.and (hmax.and (self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε))
  obtain ⟨ε, hεfeat, hεmax, hε⟩ := hall.exists
  have hf : (fun j => relu (lin (rows j) (q + ε • v))) =
      (fun j => relu (lin (rows j) q)) := funext hεfeat
  have hq : Maximum N q = q a :=
    Maximum_eq_of q (q a) a rfl fun i => by
      by_cases hi : i = a
      · subst i; exact le_rfl
      · exact (hwin i hi).le
  have hqε : Maximum N (q + ε • v) = q a + ε * v a := by
    exact Maximum_eq_of _ _ a rfl hεmax
  have h0 := hrep q
  have h1 := hrep (q + ε • v)
  rw [hq] at h0
  rw [hqε, hf, lin_add_right, lin_smul_right] at h1
  nlinarith

#print axioms feature_fiber_slope

/-- The component equation checked by each finite certificate row. -/
theorem component_equation
    (rows : Fin m → Point N) (ell : Point N) (Phi : Point m → ℝ)
    (hrep : ∀ x, Maximum N x = lin ell x + Phi (fun j => relu (lin (rows j) x)))
    (q : Point N) (a : Fin N) (C : Finset (Fin N))
    (hstrict : ∀ j, lin (rows j) q ≠ 0)
    (hcomponent : ∀ j, 0 < lin (rows j) q → ∑ i in C, rows j i = 0)
    (hwin : ∀ i, i ≠ a → q i < q a) :
    ∑ i in C, ell i = if a ∈ C then 1 else 0 := by
  classical
  have hlin : ∀ r : Point N,
      lin r (fun i => if i ∈ C then 1 else 0) = ∑ i in C, r i := by
    intro r
    simp [lin, mul_ite]
  have h := feature_fiber_slope rows ell Phi hrep q
    (fun i => if i ∈ C then 1 else 0) a hstrict
    (fun j hj => by rw [hlin]; exact hcomponent j hj) hwin
  rwa [hlin] at h

#print axioms component_equation

end MaxCaterpillar.Frontier.OvernightGeneral
