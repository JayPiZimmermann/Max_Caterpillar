import MaxCaterpillar.Fiber.First65

/-! # Exact row-value image of a rank-three four-row circuit -/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.ZeroOneRoots
open BigOperators Frontier FiniteDimensional

noncomputable def rowValueMap (A : Fin 4 → Point 4) : Point 4 →ₗ[ℝ] Point 4 where
  toFun x := fun j => lin (A j) x
  map_add' x y := funext fun j => lin_add_right (A j) x y
  map_smul' t x := funext fun j => lin_smul_right (A j) x t

noncomputable def circuitFunctional (c : Point 4) : Point 4 →ₗ[ℝ] ℝ where
  toFun z := lin c z
  map_add' := lin_add_right c
  map_smul' t z := lin_smul_right c z t

noncomputable def rowCombinationMap (A : Fin 4 → Point 4) : Point 4 →ₗ[ℝ] Point 4 where
  toFun c := ∑ j, c j • A j
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' t c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

/-- Four zero-sum rows always have a genuine nonzero row relation. -/
theorem exists_circuit_relation (A : Fin 4 → Point 4)
    (hsum : ∀ j, ∑ i, A j i = 0) :
    ∃ c : Point 4, c ≠ 0 ∧ ∀ x, ∑ j, c j * lin (A j) x = 0 := by
  let T := rowCombinationMap A
  have ht : ∀ c, ∑ i, T c i = 0 := by
    intro c
    change (∑ i, ∑ j, c j * A j i) = 0
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hsum, mul_zero, Finset.sum_const_zero]
  have hns : ¬ Function.Surjective T := by
    intro hs
    obtain ⟨c, hc⟩ := hs (unitVec 0)
    have he := ht c
    rw [hc] at he
    norm_num [unitVec] at he
  have hni : ¬ Function.Injective T := by
    intro hi
    exact hns ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi)
  have hex : ∃ c, T c = 0 ∧ c ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hni (LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hn))
  obtain ⟨c, hc, hc0⟩ := hex
  refine ⟨c, hc0, fun x => ?_⟩
  calc
    (∑ j, c j * lin (A j) x) = lin (T c) x := by
      change (∑ j, c j * lin (A j) x) = lin (∑ j, c j • A j) x
      rw [lin_sum_left]
      simp only [lin_smul_left]
    _ = 0 := by rw [hc, lin_zero_left]

/-- The diagonal-kernel theorem is enough to identify the entire row-value
image with the hyperplane of any nonzero circuit relation. -/
theorem row_values_surjective_on_circuit (A : Fin 4 → Point 4) (c : Point 4)
    (hc : c ≠ 0)
    (hrel : ∀ x, ∑ j, c j * lin (A j) x = 0)
    (hkernel : ∀ x, (∀ j, lin (A j) x = 0) → ∃ t, x = diag t)
    (z : Point 4) (hz : ∑ j, c j * z j = 0) :
    ∃ x, ∀ j, lin (A j) x = z j := by
  let f := rowValueMap A
  let g := circuitFunctional c
  have hk : LinearMap.ker f ≤ Submodule.span ℝ {diag (1 : ℝ)} := by
    intro x hx
    have hfx : ∀ j, lin (A j) x = 0 := by
      intro j
      exact congr_fun hx j
    obtain ⟨t, rfl⟩ := hkernel x hfx
    apply Submodule.mem_span_singleton.mpr
    exact ⟨t, by ext i; simp [diag]⟩
  have hd : diag (1 : ℝ) ≠ (0 : Point 4) := by
    intro he
    have he0 := congr_fun he 0
    norm_num [diag] at he0
  have hkd : finrank ℝ (LinearMap.ker f) ≤ 1 := by
    have he := Submodule.finrank_mono hk
    simpa only [finrank_span_singleton hd] using he
  have hfd : 3 ≤ finrank ℝ (LinearMap.range f) := by
    have he := LinearMap.finrank_range_add_finrank_ker f
    rw [FiniteDimensional.finrank_fin_fun] at he
    linarith only [he, hkd]
  have hgs : Function.Surjective g := by
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hc (funext hn)
    intro t
    refine ⟨(t / c j) • unitVec j, ?_⟩
    change lin c ((t / c j) • unitVec j) = t
    rw [lin_smul_right, lin_unitVec, div_mul_cancel _ hj]
  have hgd : finrank ℝ (LinearMap.ker g) = 3 := by
    have he := LinearMap.finrank_range_add_finrank_ker g
    rw [LinearMap.range_eq_top.mpr hgs, finrank_top, finrank_self,
      FiniteDimensional.finrank_fin_fun] at he
    linarith only [he]
  have hsub : LinearMap.range f ≤ LinearMap.ker g := by
    rintro y ⟨x, rfl⟩
    exact hrel x
  have heq : LinearMap.range f = LinearMap.ker g :=
    FiniteDimensional.eq_of_le_of_finrank_le hsub (by linarith only [hgd, hfd])
  have hzm : z ∈ LinearMap.range f := by
    rw [heq]
    exact hz
  obtain ⟨x, hx⟩ := hzm
  exact ⟨x, fun j => congr_fun hx j⟩

end MaxCaterpillar.Fiber.Count65.ZeroOneRoots
