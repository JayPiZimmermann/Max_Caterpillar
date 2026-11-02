import MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment.Cluster

/-! All actual paired completions with at most two effective comparison atoms attach. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment
open BigOperators Absorption

/-- Exactness itself supplies the target offsets and unit total jump. Positive
physical normalization and the actual baseline paths then give attachment in
the genuine quotient, including all zero/dormant source gates. -/
theorem low_atoms_quotient_joined (a : ExactFiber 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U ≠ 0)
    (hU : a.val.W₁ = pairedRows U) (hb : a.val.HasZeroBiases)
    (hc : (activeAtoms a.val.w₃ (fun k => a.val.W₂ k 0) (fun k => a.val.W₂ k 1)).card ≤ 2) :
    Joined (quotientMk a) (quotientMk (pairedMinimalPoint U hdet)) := by
  classical
  let C := networkAtomSlots a.val
  have hcard : Fintype.card (NetworkAtoms a.val) ≤ 2 :=
    (effectiveAtoms_card _ _ _).trans_le hc
  have hoff : ∀ u v i, networkAtomOffset a.val U u v i=0 := by
    intro u v
    exact offsets_zero_of_card_le_two (networkAtomJump a.val) (networkAtomOffset a.val U u v)
      (fun i => i.property) (network_effective_atomBalance a.val U hU hb a.property u v) hcard
  have hn := normalizedAtomNetwork_joinedIn_exact a.val a.property
  let n : ExactFiber 4 6 5 := ⟨normalizedAtomNetwork a.val,hn.target_mem⟩
  have hnb : n.val.HasZeroBiases := PairNormalization.normalizeAtoms_zeroBiases a.val 0 C hb
  let flip : Fin 5 → Bool := fun i => decide (a.val.W₂ i 0<0)
  have hmem : ∀ i, i∈C ↔
      jumpWeights a.val.w₃ (fun k => a.val.W₂ k 0) (fun k => a.val.W₂ k 1) i≠0 := by
    intro i
    change i∈activeAtoms _ _ _ ↔ _
    simp only [activeAtoms,Finset.mem_filter,Finset.mem_univ,true_and]
    exact (jumpWeights_ne_zero_iff a.val.w₃ (fun k => a.val.W₂ k 0)
      (fun k => a.val.W₂ k 1) i).symm
  have hsum : (∑ i in C,n.val.w₃ i)=1 := by
    calc
      _ = ∑ i : NetworkAtoms a.val,n.val.w₃ i.val := Finset.sum_subtype C hmem n.val.w₃
      _ = ∑ i : NetworkAtoms a.val,networkAtomJump a.val i := by
        apply Finset.sum_congr rfl
        intro i _
        exact normalizedAtomNetwork_output a.val i
      _ = 1 := atomBalance_sum_weights _ _
        (network_effective_atomBalance a.val U hU hb a.property 0 0)
  have hnatural : ∀ i∈C,∀ x,endpointForm U (n.val.W₂ i) x=
      if flip i then -endpointForm U (comparisonRow U) x else endpointForm U (comparisonRow U) x := by
    intro i hi x
    let j : NetworkAtoms a.val := ⟨i,(hmem i).mp hi⟩
    have hu : endpointForm U (unitAtomRow a.val j) x=endpointForm U (comparisonRow U) x := by
      rw [unitAtomRow_natural_offset a.val U hdet j x,hoff (x 1) (x 3) j,sub_zero]
    change endpointForm U ((normalizedAtomNetwork a.val).W₂ j.val) x=
      if networkAtomFlip a.val j then -endpointForm U (comparisonRow U) x
        else endpointForm U (comparisonRow U) x
    rw [normalizedAtomNetwork_row_oriented]
    cases hflip : networkAtomFlip a.val j <;> simp only [hflip,if_true,if_false]
    · exact hu
    · rw [endpointForm_neg,hu]
  have hfinal := target_cluster_quotient_joined n U hdet hU hnb C hc flip hsum hnatural
  exact (quotient_joined_of_joinedIn a n hn).trans hfinal

end MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment
