import MaxCaterpillar.Fiber.Paired65.Atoms

/-!
# The small scalar atom cases

At most two effective atoms all sit at the target. At most three effective
atoms either all sit there, have one globally fixed unit target atom, or have
two distinct unit-weight labels. These are the first branches in the paired
completion reduction, derived from the actual atom equations.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma zero_class_nonempty (j f : ι → ℝ) (h : Paired65.AtomBalance j f) :
    1 ≤ (Paired65.offsetClass f 0).card := by
  obtain ⟨i, hi⟩ := Paired65.atomBalance_has_zero j f h
  exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr
    ⟨i, (Paired65.mem_offsetClass f 0 i).mpr hi⟩)

/-- One or two nonzero-weight atoms can only occur at zero. -/
theorem offsets_zero_of_card_le_two (j f : ι → ℝ)
    (hj : ∀ i, j i ≠ 0) (h : Paired65.AtomBalance j f)
    (hcard : Fintype.card ι ≤ 2) : ∀ i, f i=0 := by
  intro i
  by_contra hi
  have hc0 := zero_class_nonempty j f h
  have hcz := Paired65.atomBalance_nonzero_class_card j f hj h hi ⟨i,rfl⟩
  have hc := Finset.card_le_of_subset
    (Finset.subset_univ (Paired65.offsetClass f 0 ∪ Paired65.offsetClass f (f i)))
  rw [Finset.card_union_eq (Paired65.offsetClass_disjoint f (Ne.symm hi)),
    Finset.card_univ] at hc
  linarith only [hc0, hcz, hc, hcard]

/-- With at most three effective atoms, an off-target pair leaves one unit
atom at zero. No generic distinctness hypothesis is used. -/
theorem unit_zero_atom_of_card_le_three (j f : ι → ℝ)
    (hj : ∀ i, j i ≠ 0) (h : Paired65.AtomBalance j f)
    (hcard : Fintype.card ι ≤ 3) (hoff : ∃ i, f i≠0) :
    ∃ k, j k=1 ∧ f k=0 := by
  classical
  obtain ⟨i, hi⟩ := hoff
  obtain ⟨k, hk⟩ := Paired65.atomBalance_has_zero j f h
  have hkm : k ∈ Paired65.offsetClass f 0 :=
    (Paired65.mem_offsetClass f 0 k).mpr hk
  have hcz := Paired65.atomBalance_nonzero_class_card j f hj h hi ⟨i,rfl⟩
  have hc := Finset.card_le_of_subset
    (Finset.subset_univ (Paired65.offsetClass f 0 ∪ Paired65.offsetClass f (f i)))
  rw [Finset.card_union_eq (Paired65.offsetClass_disjoint f (Ne.symm hi)),
    Finset.card_univ] at hc
  have hzero : (Paired65.offsetClass f 0).card ≤ 1 := by
    linarith only [hcz, hc, hcard]
  have he : Paired65.offsetClass f 0 = {k} := by
    ext l
    constructor
    · intro hl
      have hlk := (Finset.card_le_one.mp hzero) l hl k hkm
      exact Finset.mem_singleton.mpr hlk
    · intro hl
      have hlk := Finset.mem_singleton.mp hl
      simpa only [hlk] using hkm
  have hw := h 0
  simp only [he, Finset.sum_singleton, if_pos rfl] at hw
  exact ⟨k,hw,hk⟩

/-- This is the exhaustive global switching alternative for three knots.
The last case is the precursor of the jump pattern (1,1,-1). -/
theorem three_atom_global_cases {X : Type*} (j : ι → ℝ) (f : X → ι → ℝ)
    (hj : ∀ i, j i ≠ 0) (h : ∀ x, Paired65.AtomBalance j (f x))
    (hcard : Fintype.card ι ≤ 3) :
    (∀ x i, f x i=0) ∨ (∃ i, j i=1 ∧ ∀ x, f x i=0) ∨
      (∃ i k, i≠k ∧ j i=1 ∧ j k=1) := by
  classical
  by_cases hzero : ∀ x i, f x i=0
  · exact Or.inl hzero
  · by_cases hglobal : ∃ i, j i=1 ∧ ∀ x, f x i=0
    · exact Or.inr (Or.inl hglobal)
    · push_neg at hzero
      obtain ⟨x,i,hi⟩ := hzero
      obtain ⟨k,hk,hfk⟩ := unit_zero_atom_of_card_le_three j (f x) hj (h x)
        hcard ⟨i,hi⟩
      have hnot : ¬ ∀ y, f y k=0 := by
        intro hh
        exact hglobal ⟨k,hk,hh⟩
      push_neg at hnot
      obtain ⟨y,hy⟩ := hnot
      obtain ⟨l,hl,hfl⟩ := unit_zero_atom_of_card_le_three j (f y) hj (h y)
        hcard ⟨k,hy⟩
      refine Or.inr (Or.inr ⟨k,l,?_,hk,hl⟩)
      intro hkl
      subst l
      exact hy hfl

end MaxCaterpillar.Fiber.Count65.Paired
