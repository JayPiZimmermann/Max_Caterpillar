import MaxCaterpillar.Fiber.Count65.ZeroOneRoots.Actual
import MaxCaterpillar.Fiber.First65.Irredundancy

/-! # Selecting the actual root rows before any frame classification

The root indices are defined by the support of the actual weight rows. The
network theorem proves their cardinality is two, three, or four. A general
finite permutation places exactly these indices first; no row classification
or ordering is assumed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open BigOperators Frontier

noncomputable def enumeratedRows (net : Network 4 6 5)
    (e : Fin 4 ≃ invariantRows net) : Fin 4 → Point 4 :=
  fun j => net.W₁ (e j).val

noncomputable def rootIndices (A : Fin 4 → Point 4) : Finset (Fin 4) :=
  Finset.univ.filter fun j => (nonzeroCoordinates (A j)).card = 2

@[simp] theorem mem_rootIndices (A : Fin 4 → Point 4) (j : Fin 4) :
    j ∈ rootIndices A ↔ (nonzeroCoordinates (A j)).card = 2 := by
  classical
  simp [rootIndices]

theorem enumerated_rows_zero_sum (net : Network 4 6 5)
    (e : Fin 4 ≃ invariantRows net) (j : Fin 4) :
    ∑ i, enumeratedRows net e j i = 0 :=
  (Finset.mem_filter.mp (e j).property).2

theorem enumerated_rows_nonzero (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (e : Fin 4 ≃ invariantRows net) (j : Fin 4) :
    enumeratedRows net e j ≠ 0 := by
  intro hz
  obtain ⟨i,hi⟩ := net.first_row_ne_zero_of_max4_six hnet (e j).val
  exact hi (congr_fun hz i)

theorem enumerated_rows_not_pos_proportional (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (e : Fin 4 ≃ invariantRows net) (j k : Fin 4) (hjk : j ≠ k)
    (c : ℝ) (hc : 0 < c) :
    enumeratedRows net e j ≠ c • enumeratedRows net e k := by
  apply net.first_rows_not_pos_proportional_of_max4_six hnet _ hc
  intro he
  exact hjk (e.injective (Subtype.ext he))

theorem enumerated_rows_cover (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (e : Fin 4 ≃ invariantRows net) :
    ∀ i, ∃ j, enumeratedRows net e j i = 0 := by
  intro i
  obtain ⟨j,hj,hji⟩ := max4_invariant_row_at_top_tie net hnet i
  have hjm : j ∈ invariantRows net := by simp [invariantRows,hj]
  refine ⟨e.symm ⟨j,hjm⟩,?_⟩
  simpa only [enumeratedRows,Equiv.apply_symm_apply] using hji

/-- The actual lower bound survives every bijective enumeration of J0. -/
theorem enumerated_root_card_bounds (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (invariantRows net).card = 4)
    (e : Fin 4 ≃ invariantRows net) :
    2 ≤ (rootIndices (enumeratedRows net e)).card ∧
      (rootIndices (enumeratedRows net e)).card ≤ 4 := by
  classical
  obtain ⟨j,k,hjk,hj,hk,hjs,hks⟩ :=
    ZeroOneRoots.max4_four_invariant_rows_have_two_roots net hnet hcard
  have hjm : j ∈ invariantRows net := by simp [invariantRows,hj]
  have hkm : k ∈ invariantRows net := by simp [invariantRows,hk]
  let p := e.symm ⟨j,hjm⟩
  let q := e.symm ⟨k,hkm⟩
  have hp : p ∈ rootIndices (enumeratedRows net e) := by
    rw [mem_rootIndices]
    simpa [enumeratedRows,p] using hjs
  have hq : q ∈ rootIndices (enumeratedRows net e) := by
    rw [mem_rootIndices]
    simpa [enumeratedRows,q] using hks
  have hpq : p ≠ q := by
    intro he
    have he' := congr_arg (fun v => (e v).val) he
    exact hjk (by simpa [p,q] using he')
  constructor
  · exact Finset.one_lt_card_iff.mpr ⟨p,q,hp,hq,hpq⟩
  · simpa using (rootIndices (enumeratedRows net e)).card_le_univ

/-- An unconditional split of the actual four invariant rows. -/
theorem enumerated_root_card_cases (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (invariantRows net).card = 4)
    (e : Fin 4 ≃ invariantRows net) :
    (rootIndices (enumeratedRows net e)).card = 2 ∨
      (rootIndices (enumeratedRows net e)).card = 3 ∨
      (rootIndices (enumeratedRows net e)).card = 4 := by
  obtain ⟨hlo,hhi⟩ := enumerated_root_card_bounds net hnet hcard e
  interval_cases h : (rootIndices (enumeratedRows net e)).card <;> tauto

/-- The selected index and its complement have explicit finite enumerations. -/
noncomputable def rootEnumerationOfCard (R : Finset (Fin 4)) {k : ℕ}
    (hk : R.card = k) : Fin k ≃ R :=
  (R.equivFinOfCardEq hk).symm

noncomputable def nonrootEnumerationOfCard (R : Finset (Fin 4)) {k : ℕ}
    (hk : R.card = k) : Fin (4-k) ≃ (Rᶜ : Finset (Fin 4)) := by
  classical
  exact (Rᶜ.equivFinOfCardEq (by simpa [hk] using R.card_compl)).symm

/-- Split a finite index into membership and nonmembership without losing
its identity. This is independent of the network and its real coefficients. -/
noncomputable def partitionIndices (R : Finset (Fin 4)) :
    Sum R (Rᶜ : Finset (Fin 4)) ≃ Fin 4 := by
  classical
  exact
    { toFun := Sum.elim Subtype.val Subtype.val
      invFun := fun i => if h : i ∈ R then Sum.inl ⟨i,h⟩
        else Sum.inr ⟨i,Finset.mem_compl.mpr h⟩
      left_inv := by
        intro i
        cases i with
        | inl i => simp [i.property]
        | inr i => simp [(Finset.mem_compl.mp i.property)]
      right_inv := by intro i; dsimp; split_ifs <;> rfl }

/-- A genuine permutation of all four slots, roots first and complement last. -/
noncomputable def rootFirstPermutation (R : Finset (Fin 4)) :
    Equiv.Perm (Fin 4) := by
  classical
  let h : R.card + Rᶜ.card = 4 := by simpa using R.card_add_card_compl
  exact (finCongr h.symm).trans (finSumFinEquiv.symm.trans
    ((Equiv.sumCongr R.equivFin.symm Rᶜ.equivFin.symm).trans (partitionIndices R)))

/-- Exactly the first `R.card` positions are roots after this permutation. -/
theorem rootFirstPermutation_spec (R : Finset (Fin 4)) (i : Fin 4) :
    rootFirstPermutation R i ∈ R ↔ i.val < R.card := by
  classical
  let h : R.card + Rᶜ.card = 4 := by simpa using R.card_add_card_compl
  have hleft (j : Fin R.card) :
      rootFirstPermutation R (finCongr h (Fin.castAdd Rᶜ.card j)) =
        (R.equivFin.symm j).val := by
    change (partitionIndices R) ((Equiv.sumCongr R.equivFin.symm Rᶜ.equivFin.symm)
      (finSumFinEquiv.symm ((finCongr h).symm
        ((finCongr h) (Fin.castAdd Rᶜ.card j))))) = _
    rw [Equiv.symm_apply_apply,finSumFinEquiv_symm_apply_castAdd]
    rfl
  have hright (j : Fin Rᶜ.card) :
      rootFirstPermutation R (finCongr h (Fin.natAdd R.card j)) =
        (Rᶜ.equivFin.symm j).val := by
    change (partitionIndices R) ((Equiv.sumCongr R.equivFin.symm Rᶜ.equivFin.symm)
      (finSumFinEquiv.symm ((finCongr h).symm
        ((finCongr h) (Fin.natAdd R.card j))))) = _
    rw [Equiv.symm_apply_apply,finSumFinEquiv_symm_apply_natAdd]
    rfl
  have hparts : ∀ j : Fin (R.card + Rᶜ.card),
      rootFirstPermutation R (finCongr h j) ∈ R ↔ j.val < R.card := by
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [hleft]
      exact iff_of_true (R.equivFin.symm j).property j.isLt
    · rw [hright]
      exact iff_of_false (Finset.mem_compl.mp (Rᶜ.equivFin.symm j).property)
        (Nat.not_lt.mpr (Nat.le_add_right _ _))
  have hh := hparts ((finCongr h).symm i)
  simpa using hh

/-- The actual network supplies both the root-count split and the full
root-first enumeration. Nothing about a normalized frame is a premise. -/
theorem actual_root_first_selection (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (invariantRows net).card = 4) :
    ∃ e : Fin 4 ≃ invariantRows net, ∃ σ : Equiv.Perm (Fin 4),
      ((rootIndices (enumeratedRows net e)).card = 2 ∨
        (rootIndices (enumeratedRows net e)).card = 3 ∨
        (rootIndices (enumeratedRows net e)).card = 4) ∧
      (∀ i, (nonzeroCoordinates (enumeratedRows net e (σ i))).card = 2 ↔
        i.val < (rootIndices (enumeratedRows net e)).card) := by
  obtain ⟨e,_,_,_⟩ := four_feature_factorization net hnet hcard
  refine ⟨e,rootFirstPermutation (rootIndices (enumeratedRows net e)),
    enumerated_root_card_cases net hnet hcard e,fun i => ?_⟩
  rw [← mem_rootIndices]
  exact rootFirstPermutation_spec _ i

#print axioms actual_root_first_selection
#print axioms enumerated_root_card_cases
#print axioms rootFirstPermutation_spec
end MaxCaterpillar.Fiber.Count65.FrameTransport
