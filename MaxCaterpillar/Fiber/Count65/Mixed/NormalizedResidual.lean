import MaxCaterpillar.Fiber.Count65.Mixed.ResidualAmplitudes

/-! # Actual unit-output residuals have only orientation freedom

Positive rescaling of a physical gate normalizes its output magnitude. The
converse below then derives every core W coefficient as +1 or -1; it does not
postulate normalized core forms.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Mixed65

private lemma unit_output_of_positive {a : ℝ} (ha : 0 < a)
    (hu : a = 1 ∨ a = -1) : a = 1 := by
  rcases hu with hu | hu
  · exact hu
  · linarith only [ha,hu]

private lemma unit_output_of_negative {a : ℝ} (ha : a < 0)
    (hu : a = 1 ∨ a = -1) : a = -1 := by
  rcases hu with hu | hu
  · linarith only [ha,hu]
  · exact hu

/-- The original finite residual gates, after actual output normalization,
are exactly unit-oriented cores in one of the two projective branches. -/
theorem ResidualSystem.exists_unit_output_normal_form {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (hcard : Fintype.card ι = 3) (hunit : ∀ i, d.out i = 1 ∨ d.out i = -1) :
    ∃ e : Fin 3 ≃ ι, (d.reindex e).Represents t ∧
      (d.reindex e).out 0 = 1 ∧ (d.reindex e).out 1 = 1 ∧
      (d.reindex e).out 2 = -1 ∧
      (∀ i, (d.reindex e).W i = if (d.reindex e).W i < 0 then -1 else 1) ∧
      ((∃ k : ℝ, 1 ≤ t*k ∧ (d.reindex e).HasADirections t k) ∨
        (∃ r : ℝ, 1+t ≤ t*r ∧ (d.reindex e).HasBDirections t r)) := by
  classical
  obtain ⟨e,he,h0,h1,h2,hW0,hW1,hW2,hbranches⟩ :=
    d.exists_projective_normal_form t ht h hcard
  have ho0 : (d.reindex e).out 0 = 1 := unit_output_of_positive h0 (hunit (e 0))
  have ho1 : (d.reindex e).out 1 = 1 := unit_output_of_positive h1 (hunit (e 1))
  have ho2 : (d.reindex e).out 2 = -1 := unit_output_of_negative h2 (hunit (e 2))
  have hamps : (d.reindex e).out 0*|(d.reindex e).W 0| = 1 ∧
      (d.reindex e).out 1*|(d.reindex e).W 1| = 1 ∧
      (d.reindex e).out 2*|(d.reindex e).W 2| = -1 := by
    rcases hbranches with ⟨k,hk,hd⟩ | ⟨r,hr,hd⟩
    · exact (d.reindex e).amplitudes_A t k ht hk he hW0 hW1 hW2 hd
    · exact (d.reindex e).amplitudes_B t r ht hr he hW0 hW1 hW2 hd
  have habs : ∀ i, |(d.reindex e).W i| = 1 := by
    obtain ⟨ha0,ha1,ha2⟩ := hamps
    rw [ho0,one_mul] at ha0
    rw [ho1,one_mul] at ha1
    rw [ho2,neg_one_mul] at ha2
    intro i
    fin_cases i
    · exact ha0
    · exact ha1
    · exact neg_inj.mp ha2
  refine ⟨e,he,ho0,ho1,ho2,?_,hbranches⟩
  intro i
  split_ifs with hi
  · have hiabs := habs i
    rw [abs_of_neg hi] at hiabs
    linarith only [hiabs]
  · have hiabs := habs i
    rw [abs_of_nonneg (le_of_not_gt hi)] at hiabs
    exact hiabs

end MaxCaterpillar.Fiber.Mixed65
