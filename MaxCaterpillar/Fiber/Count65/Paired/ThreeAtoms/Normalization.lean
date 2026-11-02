import MaxCaterpillar.Fiber.Count65.Paired.ThreeAtoms
import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointNetwork

/-! Actual selected-slot normalization and natural-input atom offsets. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Frontier PairNormalization
variable {m : ℕ}

noncomputable def networkAtomSlots (net : Network 4 6 m) : Finset (Fin m) :=
  activeAtoms net.w₃ (fun k => net.W₂ k 0) (fun k => net.W₂ k 1)

lemma networkAtom_mem (net : Network 4 6 m) (i : NetworkAtoms net) :
    i.val ∈ networkAtomSlots net := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (jumpWeights_ne_zero_iff _ _ _ _).mp i.property⟩

lemma networkAtom_comparison_ne_zero (net : Network 4 6 m) (i : NetworkAtoms net) :
    net.W₂ i.val 0 ≠ 0 := ((jumpWeights_ne_zero_iff _ _ _ _).mp i.property).2.1

lemma networkAtom_common_zero (net : Network 4 6 m) (i : NetworkAtoms net) :
    net.W₂ i.val 0 + net.W₂ i.val 1 = 0 :=
  ((jumpWeights_ne_zero_iff _ _ _ _).mp i.property).1

noncomputable def normalizedAtomNetwork (net : Network 4 6 m) : Network 4 6 m :=
  normalizeAtoms net 0 (networkAtomSlots net)

lemma normalizedAtomNetwork_output (net : Network 4 6 m) (i : NetworkAtoms net) :
    (normalizedAtomNetwork net).w₃ i.val = networkAtomJump net i := by
  rw [normalizedAtomNetwork,normalizeAtoms_selected_output net 0 _ i.val (networkAtom_mem net i)]
  simp [networkAtomJump,jumpWeights,networkAtom_common_zero net i]

lemma normalizedAtomNetwork_joinedIn_exact (net : Network 4 6 m)
    (hnet : ∀ x, net.eval x = Maximum 4 x) :
    JoinedIn (ExactSet 4 6 m) net (normalizedAtomNetwork net) := by
  apply normalizeAtoms_joinedIn_exact (⟨net,hnet⟩ : ExactFiber 4 6 m) 0
  intro i hi
  exact (Finset.mem_filter.mp hi).2.2.1

/-- The row oriented to have comparison coefficient `+1`. Its negative is
used physically when the original comparison coefficient is negative. -/
noncomputable def unitAtomRow (net : Network 4 6 m) (i : NetworkAtoms net) : Fin 6 → ℝ :=
  fun j => net.W₂ i.val j / net.W₂ i.val 0

lemma normalizedAtomNetwork_row_pos (net : Network 4 6 m) (i : NetworkAtoms net)
    (hp : 0 < net.W₂ i.val 0) : (normalizedAtomNetwork net).W₂ i.val = unitAtomRow net i := by
  funext j
  rw [normalizedAtomNetwork,normalizeAtoms_selected_row net 0 _ i.val (networkAtom_mem net i),
    abs_of_pos hp]
  rfl

lemma normalizedAtomNetwork_row_neg (net : Network 4 6 m) (i : NetworkAtoms net)
    (hn : net.W₂ i.val 0 < 0) : (normalizedAtomNetwork net).W₂ i.val = -unitAtomRow net i := by
  funext j
  rw [normalizedAtomNetwork,normalizeAtoms_selected_row net 0 _ i.val (networkAtom_mem net i),
    abs_of_neg hn]
  simp only [unitAtomRow,Pi.neg_apply,div_neg_eq_neg_div]

/-- A physical atom's scalar offset is its deficit from the natural comparison
function, on every real input (including negative comparison increments). -/
theorem unitAtomRow_natural_offset (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (hcode : codeDet U ≠ 0) (i : NetworkAtoms net) (x : Point 4) :
    endpointForm U (unitAtomRow net i) x = endpointForm U (comparisonRow U) x -
      networkAtomOffset net U (x 1) (x 3) i := by
  have hα := networkAtom_comparison_ne_zero net i
  have hβ : net.W₂ i.val 1 = -net.W₂ i.val 0 := by
    linarith only [networkAtom_common_zero net i]
  have hl := relu_sub_add (x 1) (x 0)
  have hr := relu_sub_add (x 3) (x 2)
  rw [max_comm] at hl hr
  rw [comparisonRow_form U hcode]
  rw [← hl,← hr]
  simp only [endpointForm,endpointFeature_eq,unitAtomRow,networkAtomOffset,codeIntercept,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.tail_cons,add_zero]
  simp only [anchorCodeValue,Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  simp only [show (Fin.succ (2 : Fin 5) : Fin 6) = 3 from rfl,
    show (Fin.succ (Fin.succ (2 : Fin 4)) : Fin 6) = 4 from rfl,
    show (Fin.succ (Fin.succ (Fin.succ (2 : Fin 3))) : Fin 6) = 5 from rfl]
  rw [hβ]
  field_simp [hα]
  ring

noncomputable def atomOffsetRow (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (i : NetworkAtoms net) : Fin 6 → ℝ :=
  comparisonRow U-unitAtomRow net i

theorem atomOffsetRow_form (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (hcode : codeDet U ≠ 0) (i : NetworkAtoms net) (x : Point 4) :
    endpointForm U (atomOffsetRow net U i) x = networkAtomOffset net U (x 1) (x 3) i := by
  have he : endpointForm U (atomOffsetRow net U i) x =
      endpointForm U (comparisonRow U) x-endpointForm U (unitAtomRow net i) x := by
    simp [atomOffsetRow,endpointForm,sub_mul,Finset.sum_sub_distrib]
  rw [he,unitAtomRow_natural_offset net U hcode i x]
  ring

end MaxCaterpillar.Fiber.Count65.Paired
