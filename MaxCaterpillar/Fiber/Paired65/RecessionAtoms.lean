import MaxCaterpillar.Fiber.Paired65.Atoms
import MaxCaterpillar.Frontier.Basic

/-! # Extracting exact atom balance from scalar ReLU identities

Second finite differences recover each jump without distribution theory or
generic-position assumptions. Equal knots and zero knots are included.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Paired65

open BigOperators Frontier

private theorem exists_positive_gap (s : Finset ℝ) (z : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ s, a ≠ z → δ < |z-a| := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s _ ih =>
    obtain ⟨δ, hδ, hg⟩ := ih
    by_cases ha : a = z
    · refine ⟨δ, hδ, ?_⟩
      intro b hb hbz
      rcases Finset.mem_insert.mp hb with hb | hb
      · exact False.elim (hbz (hb.trans ha))
      · exact hg b hb hbz
    · have hp : 0 < |z-a| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm ha))
      refine ⟨min δ (|z-a|/2), lt_min hδ (half_pos hp), ?_⟩
      intro b hb hbz
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hp)
      · exact lt_of_le_of_lt (min_le_left _ _) (hg b hb hbz)

private theorem relu_second_difference (z a δ : ℝ) (hδ : 0 < δ)
    (hg : a ≠ z → δ < |z-a|) :
    relu (z+δ-a) + relu (z-δ-a) - 2*relu (z-a) = if a=z then δ else 0 := by
  by_cases ha : a = z
  · subst a
    rw [if_pos rfl]
    have hp : z+δ-z=δ := by ring
    have hn : z-δ-z= -δ := by ring
    rw [hp, hn, sub_self, relu_of_nonneg hδ.le, relu_of_nonpos (by linarith),
      relu_of_nonneg le_rfl]
    ring
  · rw [if_neg ha]
    have hd := hg ha
    rcases lt_or_gt_of_ne (sub_ne_zero.mpr (Ne.symm ha)) with hn | hp
    · rw [abs_of_neg hn] at hd
      rw [relu_of_nonpos (by linarith), relu_of_nonpos (by linarith),
        relu_of_nonpos hn.le]
      ring
    · rw [abs_of_pos hp] at hd
      rw [relu_of_nonneg (by linarith), relu_of_nonneg (by linarith),
        relu_of_nonneg hp.le]
      ring

/-- Every exact finite scalar hinge identity has exactly the corresponding
signed-atom balance. No distinctness of offsets or nonzero weights is needed. -/
theorem atomBalance_of_affine_relu_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j f : ι → ℝ) (A B : ℝ)
    (h : ∀ t : ℝ, (∑ i, j i * relu (t-f i)) = relu t + A*t + B) : AtomBalance j f := by
  classical
  intro z
  obtain ⟨δ, hδ, hg⟩ := exists_positive_gap (insert 0 (Finset.univ.image f)) z
  have hf : ∀ i, relu (z+δ-f i) + relu (z-δ-f i) - 2*relu (z-f i) =
      if f i=z then δ else 0 := by
    intro i
    exact relu_second_difference z (f i) δ hδ
      (hg (f i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)))
  have h0 : relu (z+δ) + relu (z-δ) - 2*relu z = if z=0 then δ else 0 := by
    have hh := relu_second_difference z 0 δ hδ (hg 0 (Finset.mem_insert_self _ _))
    simpa only [sub_zero, eq_comm] using hh
  have he : (∑ i, j i * (relu (z+δ-f i) + relu (z-δ-f i) - 2*relu (z-f i))) =
      if z=0 then δ else 0 := by
    calc
      _ = (∑ i, j i*relu (z+δ-f i)) + (∑ i, j i*relu (z-δ-f i)) -
          2*(∑ i, j i*relu (z-f i)) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = relu (z+δ)+relu (z-δ)-2*relu z := by rw [h, h, h]; ring
      _ = _ := h0
  have he' : δ * (∑ i in offsetClass f z, j i) = if z=0 then δ else 0 := by
    rw [← he]
    simp only [hf, offsetClass, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  by_cases hz : z=0
  · rw [if_pos hz] at he' ⊢
    apply (mul_left_cancel₀ (ne_of_gt hδ))
    simpa using he'
  · rw [if_neg hz] at he' ⊢
    exact (mul_eq_zero.mp he').resolve_left (ne_of_gt hδ)

/-- The normalized special case with no affine remainder. -/
theorem atomBalance_of_relu_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j f : ι → ℝ)
    (h : ∀ t : ℝ, (∑ i, j i * relu (t-f i)) = relu t) : AtomBalance j f :=
  atomBalance_of_affine_relu_identity j f 0 0 (by simpa using h)

/-- Conversely, exact atom balance reconstructs the whole scalar identity. -/
theorem relu_identity_of_atomBalance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j f : ι → ℝ) (h : AtomBalance j f) (t : ℝ) :
    (∑ i, j i * relu (t-f i)) = relu t := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ.image f) (g := f)
    (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    (fun i => j i * relu (t-f i))
  rw [← hfib]
  have hi : ∀ z, (∑ i in offsetClass f z, j i * relu (t-f i)) =
      (if z=0 then 1 else 0) * relu (t-z) := by
    intro z
    rw [← h z, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(mem_offsetClass f z i).mp hi]
  change (∑ z in Finset.univ.image f, ∑ i in offsetClass f z, j i * relu (t-f i)) = _
  simp_rw [hi]
  obtain ⟨i, hi0⟩ := atomBalance_has_zero j f h
  have hmem : (0:ℝ) ∈ Finset.univ.image f :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi0⟩
  simp [ite_mul, hmem]
  intro hn
  exact False.elim (hn i hi0)

theorem atomBalance_iff_relu_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j f : ι → ℝ) :
    AtomBalance j f ↔ ∀ t : ℝ, (∑ i, j i * relu (t-f i)) = relu t :=
  ⟨fun h t => relu_identity_of_atomBalance j f h t,
    atomBalance_of_relu_identity j f⟩

/-- The scalar four-gate recession identity permits only one canceled
off-target cluster. This is the exact analytic-to-finite bridge. -/
theorem four_relu_identity_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j f : ι → ℝ) (hj : ∀ i, j i ≠ 0) (hcard : Fintype.card ι ≤ 4)
    (h : ∀ t : ℝ, (∑ i, j i * relu (t-f i)) = relu t) :
    (∀ i, f i = 0) ∨
      ∃ z : ℝ, z ≠ 0 ∧ (∀ i, f i = 0 ∨ f i = z) ∧
        2 ≤ (offsetClass f z).card ∧ (offsetClass f z).card ≤ 3 ∧
        (∑ i in offsetClass f z, j i) = 0 :=
  atomBalance_support j f hj (atomBalance_of_relu_identity j f h) hcard

/-- The three-gate switching identity has precisely the disjoint-offset
normal form used in the paired-sector reduction. -/
theorem three_relu_offset_identity_iff (a b c : ℝ) :
    (∀ t : ℝ, relu (t-a)+relu (t-b)-relu (t-c)=relu t) ↔
      a*b=0 ∧ c=a+b := by
  constructor
  · intro h
    have hid : ∀ t : ℝ,
        (∑ i : Fin 3, (![1,1,-1] : Fin 3 → ℝ) i *
          relu (t-(![a,b,c] : Fin 3 → ℝ) i)) = relu t := by
      intro t
      simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using h t
    have hb := atomBalance_of_relu_identity (![1,1,-1] : Fin 3 → ℝ)
      (![a,b,c] : Fin 3 → ℝ) hid
    have he : ∀ z : ℝ,
        (if a=z then (1:ℝ) else 0)+(if b=z then 1 else 0)-
          (if c=z then 1 else 0) = if z=0 then 1 else 0 := by
      intro z
      have hh := hb z
      by_cases hc : c = z
      · simpa [offsetClass, Finset.sum_filter, Fin.sum_univ_succ,
          sub_eq_add_neg, add_assoc, hc] using hh
      · simpa [offsetClass, Finset.sum_filter, Fin.sum_univ_succ,
          sub_eq_add_neg, add_assoc, hc] using hh
    have hz := atomBalance_has_zero (![1,1,-1] : Fin 3 → ℝ)
      (![a,b,c] : Fin 3 → ℝ) hb
    have hab : a=0 ∨ b=0 := by
      by_contra hn
      push_neg at hn
      obtain ⟨i, hi⟩ := hz
      fin_cases i
      · exact hn.1 hi
      · exact hn.2 hi
      · have hc : c=0 := hi
        have hh := he a
        simp only [if_pos rfl, if_neg hn.1] at hh
        rw [hc, if_neg (Ne.symm hn.1)] at hh
        split_ifs at hh <;> linarith
    rcases hab with ha | hb0
    · subst a
      have hc : c=b := by
        by_cases hcb : c=b
        · exact hcb
        · have hh := he b
          rw [if_pos rfl, if_neg hcb] at hh
          by_cases hb0 : b=0
          · simp [hb0] at hh
          · simp [hb0, Ne.symm hb0] at hh
      exact ⟨by ring, by simpa using hc⟩
    · subst b
      have hc : c=a := by
        by_cases hca : c=a
        · exact hca
        · have hh := he a
          rw [if_pos rfl, if_neg hca] at hh
          by_cases ha : a=0
          · simp [ha] at hh
          · simp [ha, Ne.symm ha] at hh
      exact ⟨by ring, by simpa using hc⟩
  · rintro ⟨hab, rfl⟩ t
    rcases mul_eq_zero.mp hab with ha | hb
    · subst a
      simp
    · subst b
      simp

end MaxCaterpillar.Fiber.Paired65
