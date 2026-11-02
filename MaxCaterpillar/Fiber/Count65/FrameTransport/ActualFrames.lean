import MaxCaterpillar.Fiber.Count65.FrameTransport.NormalizedFeatureFrame
import MaxCaterpillar.Fiber.Count65.FrameTransport.EnumeratedRepresentation

/-! # Actual invariant frames before the finite graph case split

Every condition of the normalized frame and every root-count alternative is
derived from the all-input equation of the original biased network.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open MaxCaterpillar.Frontier BigOperators TwoRoots

/-- All frame hypotheses follow from the actual network equation and the
chosen enumeration; this constructor assumes no geometric branch. -/
noncomputable def normalizedActualFrame (net : Network 4 6 5)
    (hnet : ∀ x,net.eval x=Maximum 4 x) (e : Fin 4 ≃ invariantRows net) :
    NormalizedFeatureFrame (enumeratedRows net e) :=
  normalizeFeatureFrame (enumeratedRows net e)
    (enumerated_rows_zero_sum net e) (enumerated_rows_nonzero net hnet e)
    (enumerated_rows_not_pos_proportional net hnet e)
    (enumerated_represents net hnet e) (enumerated_rows_cover net hnet e)

/-- A permutation of the normalized feature slots changes only the actual
invariant-row enumeration. The original physical rows are retained. -/
theorem reorder_invariant_frame (net : Network 4 6 5)
    (e : Fin 4 ≃ invariantRows net) (B : Fin 4→Point 4)
    (p : Equiv.Perm (Fin 4)) (c : Fin 4→ℝ) (q : Equiv.Perm (Fin 4))
    (hrows : ∀ j,net.W₁ (e j).val=c j • (fun i => B (p j) (q i))) :
    ∃ e' : Fin 4 ≃ invariantRows net,
      ∀ j,net.W₁ (e' j).val=c (p.symm j) • (fun i => B j (q i)) := by
  refine ⟨p.symm.trans e,fun j => ?_⟩
  simpa only [Equiv.trans_apply,p.apply_symm_apply] using hrows (p.symm j)

/-- The genuine support-selected normalization exists for every original
exact network in the four-invariant-row stratum, with root count 2,3,or4. -/
theorem actual_normalized_feature_frame (net : Network 4 6 5)
    (hnet : ∀ x,net.eval x=Maximum 4 x)
    (hcard : (invariantRows net).card=4) :
    ∃ e : Fin 4 ≃ invariantRows net,
      ∃ nf : NormalizedFeatureFrame (enumeratedRows net e),
        (rootIndices (enumeratedRows net e)).card=2 ∨
        (rootIndices (enumeratedRows net e)).card=3 ∨
        (rootIndices (enumeratedRows net e)).card=4 := by
  classical
  let e : Fin 4 ≃ invariantRows net := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin,Fintype.card_coe,hcard])
  let nf := normalizedActualFrame net hnet e
  exact ⟨e,nf,enumerated_root_card_cases net hnet hcard e⟩

/-- The four-root cardinality alternative refers to all and only the
actual invariant first rows, not to a selected subframe. -/
theorem all_invariant_roots_of_card_four (net : Network 4 6 5)
    (e : Fin 4 ≃ invariantRows net)
    (hc : (rootIndices (enumeratedRows net e)).card=4) :
    ∀ j,(∑ i,net.W₁ j i)=0 → (nonzeroCoordinates (net.W₁ j)).card=2 := by
  classical
  intro j hj
  have hjm : j∈invariantRows net := by
    simp only [invariantRows,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hj
  let k : Fin 4 := e.symm ⟨j,hjm⟩
  have hk : k∈rootIndices (enumeratedRows net e) := by
    by_contra hnot
    have hsub : rootIndices (enumeratedRows net e) ⊆
        (Finset.univ : Finset (Fin 4)).erase k := by
      intro l hl
      refine Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩
      intro he
      exact hnot (he ▸ hl)
    have hle := Finset.card_le_of_subset hsub
    rw [hc] at hle
    have he : ((Finset.univ : Finset (Fin 4)).erase k).card=3 := by simp
    rw [he] at hle
    linarith only [hle]
  have hroot := (mem_rootIndices (enumeratedRows net e) k).mp hk
  simpa only [enumeratedRows,k,e.apply_symm_apply] using hroot

#print axioms reorder_invariant_frame
#print axioms actual_normalized_feature_frame
#print axioms all_invariant_roots_of_card_four
end MaxCaterpillar.Fiber.Count65.FrameTransport
