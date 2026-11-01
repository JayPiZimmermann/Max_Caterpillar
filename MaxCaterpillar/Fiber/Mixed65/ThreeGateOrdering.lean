import MaxCaterpillar.Fiber.Mixed65.CarrierForcing

/-! # Ordering three original residual gates without changing their weights

Reindexing is by an actual finite equivalence. The two positive facet carriers
and the negative gate exhaust any three-gate representation. No division,
orientation change, or normalization of incoming or output weights occurs.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open BigOperators

noncomputable def ResidualSystem.reindex {ι κ : Type*}
    (d : ResidualSystem ι) (e : κ ≃ ι) : ResidualSystem κ where
  lU := d.lU
  lV := d.lV
  lW := d.lW
  lT := d.lT
  out := d.out ∘ e
  U := d.U ∘ e
  V := d.V ∘ e
  W := d.W ∘ e
  T := d.T ∘ e

/-- Exactness is invariant under reindexing the original gate set. -/
theorem ResidualSystem.reindex_represents {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ResidualSystem ι) (e : κ ≃ ι) (t : ℝ) (h : d.Represents t) :
    (d.reindex e).Represents t := by
  intro q b c
  have hs := Fintype.sum_equiv e
    (fun j => (d.reindex e).out j * MaxCaterpillar.relu ((d.reindex e).gate t j q b c))
    (fun i => d.out i * MaxCaterpillar.relu (d.gate t i q b c)) (fun _ => rfl)
  change max (max (q + b) b) (MaxCaterpillar.relu c) = d.base t q b c + _
  rw [hs]
  exact h q b c

/-- Any sum of absolute effective coefficients is exactly preserved. -/
theorem ResidualSystem.reindex_effective_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ResidualSystem ι) (e : κ ≃ ι) :
    (∑ j, (|(d.reindex e).out j * (d.reindex e).U j| +
      |(d.reindex e).out j * (d.reindex e).V j| +
      |(d.reindex e).out j * (d.reindex e).W j| +
      |(d.reindex e).out j * (d.reindex e).T j|)) =
    ∑ i, (|d.out i * d.U i| + |d.out i * d.V i| +
      |d.out i * d.W i| + |d.out i * d.T i|) :=
  Fintype.sum_equiv e _ _ (fun _ => rfl)

private theorem three_index_equiv {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = 3) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ e : Fin 3 ≃ ι, e 0 = i ∧ e 1 = j ∧ e 2 = k := by
  let f : Fin 3 → ι := ![i, j, k]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [f, hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by simp [hcard]⟩
  exact ⟨Equiv.ofBijective f hbij, rfl, rfl, rfl⟩

/-- All three gates can be ordered as left positive, right positive, negative,
with both exact facet coefficient relations. This applies to any finite gate
index type of cardinality three, including a subset of physical neurons. -/
theorem ResidualSystem.exists_ordered_three_gate {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (hcard : Fintype.card ι = 3) :
    ∃ e : Fin 3 ≃ ι,
      (d.reindex e).Represents t ∧
      0 < (d.reindex e).out 0 ∧ 0 < (d.reindex e).out 1 ∧
      (d.reindex e).out 2 < 0 ∧
      (d.reindex e).W 0 ≠ 0 ∧ (d.reindex e).W 1 ≠ 0 ∧
      (d.reindex e).U 0 = -(1 + t) * (d.reindex e).W 0 ∧
      (d.reindex e).T 0 = (d.reindex e).W 0 ∧
      (d.reindex e).U 1 = -(d.reindex e).W 1 ∧
      (d.reindex e).V 1 = -(d.reindex e).W 1 := by
  obtain ⟨i, hi, hiW, hiU, hiT⟩ := d.exists_left_carrier t ht h
  obtain ⟨j, hj, hjW, hjU, hjV⟩ := d.exists_right_carrier t ht h
  obtain ⟨k, hk⟩ := d.exists_negative_gate t ht h
  have hij : i ≠ j := by
    intro he
    subst j
    have hz : t * d.W i = 0 := by nlinarith only [hiU, hjU]
    exact hiW ((mul_eq_zero.mp hz).resolve_left ht.ne')
  have hik : i ≠ k := by intro he; subst k; linarith only [hi, hk]
  have hjk : j ≠ k := by intro he; subst k; linarith only [hj, hk]
  obtain ⟨e, h0, h1, h2⟩ := three_index_equiv hcard i j k hij hik hjk
  refine ⟨e, d.reindex_represents e t h, ?_⟩
  simpa only [ResidualSystem.reindex, Function.comp_apply, h0, h1, h2] using
    And.intro hi (And.intro hj (And.intro hk (And.intro hiW
      (And.intro hjW (And.intro hiU (And.intro hiT (And.intro hjU hjV)))))))

end MaxCaterpillar.Fiber.Mixed65
