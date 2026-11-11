import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! # The four-atom support lemma

This is the finite combinatorial step in the four-recession-gate proof.  It
starts from the signed-atom balance equations themselves; extraction of those
equations from an arbitrary ReLU completion is a separate obligation.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Paired65

open BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Indices whose scalar offset equals the specified value. -/
noncomputable def offsetClass (f : ι → ℝ) (z : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => f i = z)

@[simp] theorem mem_offsetClass (f : ι → ℝ) (z : ℝ) (i : ι) :
    i ∈ offsetClass f z ↔ f i = z := by
  classical
  simp [offsetClass]

/-- The signed atom sum is one unit atom at zero. -/
def AtomBalance (j f : ι → ℝ) : Prop :=
  ∀ z : ℝ, (∑ i in offsetClass f z, j i) = if z = 0 then 1 else 0

theorem atomBalance_has_zero (j f : ι → ℝ) (h : AtomBalance j f) :
    ∃ i, f i = 0 := by
  classical
  by_contra hn
  have hs : offsetClass f 0 = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro i hi
    exact hn ⟨i, (mem_offsetClass f 0 i).mp hi⟩
  have h0 := h 0
  simp [hs] at h0

theorem offsetClass_disjoint (f : ι → ℝ) {u v : ℝ} (huv : u ≠ v) :
    Disjoint (offsetClass f u) (offsetClass f v) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hiu hiv
  exact huv (((mem_offsetClass f u i).mp hiu).symm.trans
    ((mem_offsetClass f v i).mp hiv))

/-- A nonzero offset cannot carry a single nonzero-weight atom. -/
theorem atomBalance_nonzero_class_card (j f : ι → ℝ)
    (hj : ∀ i, j i ≠ 0) (h : AtomBalance j f)
    {z : ℝ} (hz : z ≠ 0) (he : ∃ i, f i = z) :
    2 ≤ (offsetClass f z).card := by
  classical
  obtain ⟨i, hi⟩ := he
  have him : i ∈ offsetClass f z := (mem_offsetClass f z i).mpr hi
  by_contra hn
  have hcard : (offsetClass f z).card ≤ 1 := Nat.le_of_lt_succ (lt_of_not_ge hn)
  have hs : offsetClass f z = {i} := by
    apply Finset.ext
    intro k
    constructor
    · intro hk
      have hki : k = i := (Finset.card_le_one.mp hcard) k hk i him
      simpa [hki]
    · intro hk
      have hki := Finset.mem_singleton.mp hk
      subst k
      exact him
  have hb := h z
  simp only [hs, Finset.sum_singleton, if_neg hz] at hb
  exact hj i hb

/-- With at most four nonzero-weight atoms, all nonzero offsets coincide.
The remaining atom at zero prevents two separate canceled off-zero clusters. -/
theorem atomBalance_nonzero_offsets_equal (j f : ι → ℝ)
    (hj : ∀ i, j i ≠ 0) (h : AtomBalance j f) (hcard : Fintype.card ι ≤ 4)
    {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0)
    (heu : ∃ i, f i = u) (hev : ∃ i, f i = v) : u = v := by
  classical
  by_contra huv
  have hc0 : 1 ≤ (offsetClass f 0).card := by
    obtain ⟨i, hi⟩ := atomBalance_has_zero j f h
    exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨i, (mem_offsetClass f 0 i).mpr hi⟩)
  have hcu := atomBalance_nonzero_class_card j f hj h hu heu
  have hcv := atomBalance_nonzero_class_card j f hj h hv hev
  have hduv := offsetClass_disjoint f huv
  have hd0u := offsetClass_disjoint f (Ne.symm hu)
  have hd0v := offsetClass_disjoint f (Ne.symm hv)
  have hd0uv : Disjoint (offsetClass f 0) (offsetClass f u ∪ offsetClass f v) :=
    Finset.disjoint_union_right.mpr ⟨hd0u, hd0v⟩
  have hc := Finset.card_le_of_subset
    (Finset.subset_univ (offsetClass f 0 ∪ (offsetClass f u ∪ offsetClass f v)))
  rw [Finset.card_union_eq hd0uv, Finset.card_union_eq hduv,
    Finset.card_univ] at hc
  omega

/-- Thus every offset vector has a fixed nonzero value on a zero-sum subset
and vanishes elsewhere (or is identically zero). -/
theorem atomBalance_support (j f : ι → ℝ)
    (hj : ∀ i, j i ≠ 0) (h : AtomBalance j f) (hcard : Fintype.card ι ≤ 4) :
    (∀ i, f i = 0) ∨
      ∃ z : ℝ, z ≠ 0 ∧
        (∀ i, f i = 0 ∨ f i = z) ∧
        2 ≤ (offsetClass f z).card ∧
        (offsetClass f z).card ≤ 3 ∧
        (∑ i in offsetClass f z, j i) = 0 := by
  classical
  by_cases hf : ∀ i, f i = 0
  · exact Or.inl hf
  · right
    push_neg at hf
    obtain ⟨i, hi⟩ := hf
    refine ⟨f i, hi, ?_, atomBalance_nonzero_class_card j f hj h hi ⟨i,rfl⟩, ?_, ?_⟩
    · intro k
      by_cases hk : f k = 0
      · exact Or.inl hk
      · exact Or.inr (atomBalance_nonzero_offsets_equal j f hj h hcard hk hi
          ⟨k,rfl⟩ ⟨i,rfl⟩)
    · have hc0 : 1 ≤ (offsetClass f 0).card := by
        obtain ⟨k, hk⟩ := atomBalance_has_zero j f h
        exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨k, (mem_offsetClass f 0 k).mpr hk⟩)
      have hc := Finset.card_le_of_subset
        (Finset.subset_univ (offsetClass f 0 ∪ offsetClass f (f i)))
      rw [Finset.card_union_eq (offsetClass_disjoint f (Ne.symm hi)),
        Finset.card_univ] at hc
      linarith only [hc0, hc, hcard]
    · simpa [hi] using h (f i)

end MaxCaterpillar.Fiber.Paired65
