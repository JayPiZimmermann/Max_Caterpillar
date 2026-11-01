import MaxCaterpillar.Fiber.Mixed65.Clipping

/-! # The actual invariant function space of the mixed Max4 dictionary

The domain consists of the independent coordinates `(q,b,c)`. Membership in
`featureSpace t` means equality as a function on the entire real domain to a
linear combination of the four first-hidden-layer features. No observed-data
or formal coefficient-space quotient is used.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open MaxCaterpillar.Frontier

abbrev InvariantState := ℝ × ℝ × ℝ

/-- A readout of the actual four invariant first-hidden-layer activations. -/
noncomputable def readout (t A B C D : ℝ) (x : InvariantState) : ℝ :=
  form t A B C D x.1 x.2.1 x.2.2

lemma readout_zero (t : ℝ) : readout t 0 0 0 0 = 0 := by
  funext x
  simp [readout, form]

lemma readout_add (t A B C D E F G H : ℝ) :
    readout t (A + E) (B + F) (C + G) (D + H) =
      readout t A B C D + readout t E F G H := by
  funext x
  simp only [readout, form, Pi.add_apply]
  ring

lemma readout_smul (s t A B C D : ℝ) :
    readout t (s * A) (s * B) (s * C) (s * D) = s • readout t A B C D := by
  funext x
  simp only [readout, form, Pi.smul_apply, smul_eq_mul]
  ring

lemma readout_sub (t A B C D E F G H : ℝ) :
    readout t A B C D - readout t E F G H =
      readout t (A - E) (B - F) (C - G) (D - H) := by
  funext x
  simp only [readout, form, Pi.sub_apply]
  ring

lemma readout_nonneg_of_coeff_nonneg {t A B C D : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∀ x : InvariantState, 0 ≤ readout t A B C D x := by
  intro x
  exact add_nonneg
    (add_nonneg (add_nonneg (mul_nonneg hA (relu_nonneg x.1))
      (mul_nonneg hB (relu_nonneg x.2.1)))
      (mul_nonneg hC (relu_nonneg x.2.2)))
    (mul_nonneg hD (relu_nonneg (t * x.1 - x.2.1)))

/-- A continuous coefficientwise choice of the positive readout in a
nonnegative decomposition. This is not the pointwise positive part of the
readout, which usually leaves the feature space. -/
noncomputable def readoutPos (t A B C D : ℝ) : InvariantState → ℝ :=
  readout t (relu A) (relu B) (relu C) (relu D)

noncomputable def readoutNeg (t A B C D : ℝ) : InvariantState → ℝ :=
  readout t (relu (-A)) (relu (-B)) (relu (-C)) (relu (-D))

lemma readoutPos_nonneg (t A B C D : ℝ) :
    ∀ x, 0 ≤ readoutPos t A B C D x :=
  readout_nonneg_of_coeff_nonneg (relu_nonneg A) (relu_nonneg B)
    (relu_nonneg C) (relu_nonneg D)

lemma readoutNeg_nonneg (t A B C D : ℝ) :
    ∀ x, 0 ≤ readoutNeg t A B C D x :=
  readout_nonneg_of_coeff_nonneg (relu_nonneg (-A)) (relu_nonneg (-B))
    (relu_nonneg (-C)) (relu_nonneg (-D))

lemma readoutPos_sub_readoutNeg (t A B C D : ℝ) :
    readoutPos t A B C D - readoutNeg t A B C D = readout t A B C D := by
  rw [readoutPos, readoutNeg, readout_sub,
    relu_sub_relu_neg, relu_sub_relu_neg, relu_sub_relu_neg, relu_sub_relu_neg]

/-- The exact span of `relu q`, `relu b`, `relu c`, and `relu (t*q-b)`. -/
noncomputable def featureSpace (t : ℝ) : Submodule ℝ (InvariantState → ℝ) where
  carrier := {f | ∃ A B C D : ℝ, f = readout t A B C D}
  zero_mem' := ⟨0, 0, 0, 0, (readout_zero t).symm⟩
  add_mem' := by
    rintro f g ⟨A, B, C, D, rfl⟩ ⟨E, F, G, H, rfl⟩
    exact ⟨A + E, B + F, C + G, D + H, (readout_add t A B C D E F G H).symm⟩
  smul_mem' := by
    rintro s f ⟨A, B, C, D, rfl⟩
    exact ⟨s * A, s * B, s * C, s * D, (readout_smul s t A B C D).symm⟩

theorem mem_featureSpace_iff {t : ℝ} {f : InvariantState → ℝ} :
    f ∈ featureSpace t ↔ ∃ A B C D : ℝ, f = readout t A B C D := Iff.rfl

theorem readout_mem_featureSpace (t A B C D : ℝ) :
    readout t A B C D ∈ featureSpace t := ⟨A, B, C, D, rfl⟩

/-- Every actual feature-linear function has a nonnegative decomposition
inside the same actual feature space. -/
theorem exists_nonnegative_decomposition {t : ℝ} {L : InvariantState → ℝ}
    (hL : L ∈ featureSpace t) :
    ∃ A B : InvariantState → ℝ, A ∈ featureSpace t ∧ B ∈ featureSpace t ∧
      (∀ x, 0 ≤ A x) ∧ (∀ x, 0 ≤ B x) ∧ A - B = L := by
  rcases hL with ⟨a, b, c, d, rfl⟩
  exact ⟨readoutPos t a b c d, readoutNeg t a b c d,
    readout_mem_featureSpace t _ _ _ _, readout_mem_featureSpace t _ _ _ _,
    readoutPos_nonneg t a b c d, readoutNeg_nonneg t a b c d,
    readoutPos_sub_readoutNeg t a b c d⟩

/-- Readout parameters are unique whenever the dictionary parameter is positive. -/
theorem readout_eq_iff {t A B C D E F G H : ℝ} (ht : 0 < t) :
    readout t A B C D = readout t E F G H ↔
      A = E ∧ B = F ∧ C = G ∧ D = H := by
  constructor
  · intro h
    have hB : B = F := by
      have hx := congrFun h (0, 1, 0)
      simpa only [readout, form_v] using hx
    have hD : D = H := by
      have hx := congrFun h (0, -1, 0)
      simpa only [readout, form_u] using hx
    have hC : C = G := by
      have hx := congrFun h (0, 0, 1)
      simpa only [readout, form_w] using hx
    have hA : A = E := by
      have hx := congrFun h (1, t, 0)
      simp only [readout, form_a ht.le, hB] at hx
      linarith only [hx]
    exact ⟨hA, hB, hC, hD⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

/-- The five ray inequalities characterize nonnegativity on the whole input
domain, not only on the rays at which they are tested. -/
theorem readout_nonneg_iff {t A B C D : ℝ} (ht : 0 < t) :
    (∀ x : InvariantState, 0 ≤ readout t A B C D x) ↔
      0 ≤ B ∧ 0 ≤ D ∧ 0 ≤ C ∧ 0 ≤ A + t * B ∧ 0 ≤ A + t * D := by
  rw [← form_nonneg_iff ht]
  constructor
  · intro h q b c
    exact h (q, b, c)
  · intro h x
    exact h x.1 x.2.1 x.2.2

/-- Clipping rigidity stated directly for membership in the actual function
submodule. This is the hypothesis consumed by the two-head classification. -/
theorem featureSpace_clipping_rigid {t : ℝ} (ht : 0 < t)
    (f : InvariantState → ℝ) (hf : f ∈ featureSpace t)
    (hc : (fun x => relu (f x)) ∈ featureSpace t) :
    (∀ x, 0 ≤ f x) ∨ (∀ x, f x ≤ 0) := by
  rcases hf with ⟨A, B, C, D, rfl⟩
  rcases hc with ⟨E, F, G, H, h⟩
  have he : ∀ q b c : ℝ,
      relu (form t A B C D q b c) = form t E F G H q b c := by
    intro q b c
    exact congrFun h (q, b, c)
  rcases form_clipping_rigid ht he with hn | hn
  · exact Or.inl (fun x => hn x.1 x.2.1 x.2.2)
  · exact Or.inr (fun x => hn x.1 x.2.1 x.2.2)

end MaxCaterpillar.Fiber.Mixed65
