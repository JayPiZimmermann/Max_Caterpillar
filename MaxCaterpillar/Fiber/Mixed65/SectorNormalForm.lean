import MaxCaterpillar.Fiber.Separation
import MaxCaterpillar.Fiber.SymmetryHomeomorph

/-! # First-matrix normal form for the symmetry-saturated mixed sector

This is an equivalence between two definitions of the same subset of the full
exact fiber. It does not classify arbitrary exact first layers. It expresses
the allowed positive row scalings and finite permutations explicitly, without
restricting any second-layer or output parameters, or any biases.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

/-- Explicit row-scale and permutation form of a mixed first matrix. -/
def FirstMatrixForm (net : Network 4 6 5) : Prop :=
  ∃ t : ℝ, 0 < t ∧ ∃ c : Fin 6 → ℝ, (∀ j, 0 < c j) ∧
    ∃ p : Equiv.Perm (Fin 6), ∃ q : Equiv.Perm (Fin 4),
      ∀ j i, net.W₁ j i = c j * firstRows t (p j) (q i)

/-- Positive first-row scaling with the row and input labels fixed. -/
def labeledScaledSector : Set (ExactFiber 4 6 5) :=
  {net | ∃ t : ℝ, 0 < t ∧ ∃ s : Fin 6 → ℝ,
    (∀ j, 0 < s j) ∧ net.val.W₁ = fun j i => s j * firstRows t j i}

theorem firstMatrixForm_scaleFirst_forward (net : Network 4 6 5)
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j) (h : FirstMatrixForm net) :
    FirstMatrixForm (scaleFirst net s) := by
  obtain ⟨t, ht, c, hc, p, q, hrows⟩ := h
  refine ⟨t, ht, (fun j => s j * c j), (fun j => mul_pos (hs j) (hc j)), p, q, ?_⟩
  intro j i
  change s j * net.W₁ j i = _
  rw [hrows, mul_assoc]

theorem firstMatrixForm_scaleFirst (net : Network 4 6 5)
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j) :
    FirstMatrixForm (scaleFirst net s) ↔ FirstMatrixForm net := by
  constructor
  · intro h
    have hinv := firstMatrixForm_scaleFirst_forward (scaleFirst net s)
      (fun j => (s j)⁻¹) (fun j => inv_pos.mpr (hs j)) h
    rwa [scaleFirst_inv_scaleFirst net s hs] at hinv
  · exact firstMatrixForm_scaleFirst_forward net s hs

theorem firstMatrixForm_scaleSecond (net : Network 4 6 5) (s : Fin 5 → ℝ) :
    FirstMatrixForm (scaleSecond net s) ↔ FirstMatrixForm net := Iff.rfl

theorem firstMatrixForm_permuteHidden_forward (net : Network 4 6 5)
    (p₀ : Equiv.Perm (Fin 6)) (q₀ : Equiv.Perm (Fin 5)) (h : FirstMatrixForm net) :
    FirstMatrixForm (permuteHidden net p₀ q₀) := by
  obtain ⟨t, ht, c, hc, p, q, hrows⟩ := h
  exact ⟨t, ht, (fun j => c (p₀ j)), (fun j => hc (p₀ j)), p₀.trans p, q,
    fun j i => hrows (p₀ j) i⟩

theorem firstMatrixForm_permuteHidden (net : Network 4 6 5)
    (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 5)) :
    FirstMatrixForm (permuteHidden net p q) ↔ FirstMatrixForm net := by
  constructor
  · intro h
    have hinv := firstMatrixForm_permuteHidden_forward (permuteHidden net p q) p.symm q.symm h
    rwa [permuteHidden_inv_permuteHidden net p q] at hinv
  · exact firstMatrixForm_permuteHidden_forward net p q

theorem firstMatrixForm_permuteInputs_forward (net : Network 4 6 5)
    (q₀ : Equiv.Perm (Fin 4)) (h : FirstMatrixForm net) :
    FirstMatrixForm (permuteInputs net q₀) := by
  obtain ⟨t, ht, c, hc, p, q, hrows⟩ := h
  exact ⟨t, ht, c, hc, p, q₀.trans q, fun j i => hrows j (q₀ i)⟩

theorem firstMatrixForm_permuteInputs (net : Network 4 6 5)
    (p : Equiv.Perm (Fin 4)) :
    FirstMatrixForm (permuteInputs net p) ↔ FirstMatrixForm net := by
  constructor
  · intro h
    have hinv := firstMatrixForm_permuteInputs_forward (permuteInputs net p) p.symm h
    rwa [permuteInputs_inv_permuteInputs net p] at hinv
  · exact firstMatrixForm_permuteInputs_forward net p

theorem firstMatrixForm_of_symmetryStep {a b : ExactFiber 4 6 5}
    (h : SymmetryStep a b) : FirstMatrixForm a.val ↔ FirstMatrixForm b.val := by
  cases h with
  | first s hs => exact (firstMatrixForm_scaleFirst a.val s hs).symm
  | second s hs => exact (firstMatrixForm_scaleSecond a.val s).symm
  | hidden p q => exact (firstMatrixForm_permuteHidden a.val p q).symm
  | input p => exact (firstMatrixForm_permuteInputs a.val p).symm

theorem firstMatrixForm_of_symmetry {a b : ExactFiber 4 6 5}
    (h : EqvGen SymmetryStep a b) : FirstMatrixForm a.val ↔ FirstMatrixForm b.val := by
  induction h with
  | rel a b h => exact firstMatrixForm_of_symmetryStep h
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ hab hbc => exact hab.trans hbc

/-- The saturation definition imposes exactly the displayed first-matrix
condition and leaves the full exact suffix unrestricted. -/
theorem mem_sector_iff_firstMatrixForm (net : ExactFiber 4 6 5) :
    net ∈ sector ↔ FirstMatrixForm net.val := by
  constructor
  · rintro ⟨a, ⟨t, ht, hrows⟩, ha⟩
    apply (firstMatrixForm_of_symmetry ha).mp
    refine ⟨t, ht, (fun _ => 1), (fun _ => zero_lt_one), Equiv.refl _, Equiv.refl _, ?_⟩
    intro j i
    simp only [hrows, Equiv.refl_apply, one_mul]
  · rintro ⟨t, ht, c, hc, p, q, hrows⟩
    let b := scaleFirstFiber (fun j => (c j)⁻¹) (fun j => inv_pos.mpr (hc j)) net
    let d := permuteHiddenFiber p.symm (Equiv.refl _) b
    let a := permuteInputsFiber q.symm d
    have ha : a ∈ seed := by
      refine ⟨t, ht, ?_⟩
      funext j i
      change (c (p.symm j))⁻¹ * net.val.W₁ (p.symm j) (q.symm i) = firstRows t j i
      rw [hrows]
      simp only [Equiv.apply_symm_apply, ← mul_assoc,
        inv_mul_cancel (ne_of_gt (hc (p.symm j))), one_mul]
    have hnb : EqvGen SymmetryStep net b :=
      EqvGen.rel _ _ (SymmetryStep.first net _ _)
    have hbd : EqvGen SymmetryStep b d :=
      EqvGen.rel _ _ (SymmetryStep.hidden b _ _)
    have hda : EqvGen SymmetryStep d a :=
      EqvGen.rel _ _ (SymmetryStep.input d _)
    exact ⟨a, ha, EqvGen.symm _ _ (EqvGen.trans _ _ _ hnb (EqvGen.trans _ _ _ hbd hda))⟩

/-- A finite permutation action; the positive row scales remain in the
continuously parameterized labeled sector. -/
def permutationHomeomorph (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 4)) :
    ExactFiber 4 6 5 ≃ₜ ExactFiber 4 6 5 :=
  (permuteHiddenHomeomorph p (Equiv.refl _)).trans (permuteInputsHomeomorph q)

@[simp] theorem permutationHomeomorph_W₁ (p : Equiv.Perm (Fin 6))
    (q : Equiv.Perm (Fin 4)) (net : ExactFiber 4 6 5) (j : Fin 6) (i : Fin 4) :
    (permutationHomeomorph p q net).val.W₁ j i = net.val.W₁ (p j) (q i) := rfl

@[simp] theorem permutationHomeomorph_symm_W₁ (p : Equiv.Perm (Fin 6))
    (q : Equiv.Perm (Fin 4)) (net : ExactFiber 4 6 5) (j : Fin 6) (i : Fin 4) :
    ((permutationHomeomorph p q).symm net).val.W₁ j i =
      net.val.W₁ (p.symm j) (q.symm i) := rfl

/-- A finite union formula for the full mixed first-layer sector. This does
not add second-hidden-layer normalization or restrictions on its completions. -/
theorem sector_eq_iUnion_permutationImage :
    sector = ⋃ p : Equiv.Perm (Fin 6), ⋃ q : Equiv.Perm (Fin 4),
      permutationHomeomorph p q '' labeledScaledSector := by
  ext net
  constructor
  · intro hn
    obtain ⟨t, ht, c, hc, p, q, hrows⟩ := (mem_sector_iff_firstMatrixForm net).mp hn
    apply Set.mem_iUnion.mpr
    refine ⟨p, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
    refine ⟨(permutationHomeomorph p q).symm net, ?_,
      (permutationHomeomorph p q).apply_symm_apply net⟩
    refine ⟨t, ht, (fun j => c (p.symm j)), (fun j => hc (p.symm j)), ?_⟩
    funext j i
    rw [permutationHomeomorph_symm_W₁, hrows]
    simp only [Equiv.apply_symm_apply]
  · intro hn
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hn
    obtain ⟨q, b, ⟨t, ht, c, hc, hrows⟩, hb⟩ := Set.mem_iUnion.mp hp
    subst net
    apply (mem_sector_iff_firstMatrixForm _).mpr
    refine ⟨t, ht, (fun j => c (p j)), (fun j => hc (p j)), p, q, ?_⟩
    intro j i
    rw [permutationHomeomorph_W₁, hrows]

/-- Closedness of the labeled, positively scaled sector transfers through the
finite input/first-neuron permutation action. The hypothesis remains explicit. -/
theorem isClosed_sector_of_labeledScaledSector (h : IsClosed labeledScaledSector) :
    IsClosed sector := by
  rw [sector_eq_iUnion_permutationImage]
  apply isClosed_iUnion_of_finite
  intro p
  apply isClosed_iUnion_of_finite
  intro q
  exact (permutationHomeomorph p q).isClosedMap _ h

end MaxCaterpillar.Fiber.Mixed65
