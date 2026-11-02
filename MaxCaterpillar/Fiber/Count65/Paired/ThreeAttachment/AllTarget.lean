import MaxCaterpillar.Fiber.Count65.Paired.ThreeAtoms.SwitchingRows
import MaxCaterpillar.Fiber.Count65.Paired.FeatureInjectivity
import MaxCaterpillar.Fiber.Connected64.OutputMoves

/-! # Three target-offset atoms reduce to at most two actual atoms

The code is arbitrary and invertible; every physical spectator and every
output coefficient is retained. Exactness and all-target offsets are the
only analytic hypotheses. Positive atom normalization followed by one
actual duplicate-row output transfer removes an atom.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment
open BigOperators Frontier Absorption PairNormalization
variable {m : ℕ}

/-- Invertibility makes equality on every natural input faithful to all six
physical coefficients, so a target-offset atom is literally the comparison. -/
lemma allTarget_unitAtomRow (net : Network 4 6 m) (U : Fin 2 → Fin 2 → ℝ)
    (hcode : codeDet U≠0) (i : NetworkAtoms net)
    (hoff : ∀ a b,networkAtomOffset net U a b i=0) :
    unitAtomRow net i=comparisonRow U := by
  apply paired_feature_injective U (inverseCode U) (inverseCode_rightInverse U hcode)
  intro x
  rw [preact_pairedRows_zero,preact_pairedRows_zero,unitAtomRow_natural_offset net U hcode,
    hoff,sub_zero]

lemma allTarget_normalized_row (net : Network 4 6 m) (U : Fin 2 → Fin 2 → ℝ)
    (hcode : codeDet U≠0) (hoff : ∀ a b i,networkAtomOffset net U a b i=0)
    (i : NetworkAtoms net) :
    (normalizedAtomNetwork net).W₂ i.val=
      if networkAtomFlip net i then -comparisonRow U else comparisonRow U := by
  rw [normalizedAtomNetwork_row_oriented,allTarget_unitAtomRow net U hcode i
    (fun a b => hoff a b i)]

/-- Transfer one physical atom output to another original atom. All original
nonatoms remain untouched, so no new atom can appear outside the old support. -/
lemma transfer_normalized_atoms_subset (net : Network 4 6 m)
    (i j : NetworkAtoms net) (hij : i≠j) :
    activeAtoms
      (withOutput (normalizedAtomNetwork net)
        (transferOutput (normalizedAtomNetwork net).w₃ i.val j.val)
          (normalizedAtomNetwork net).b₃).w₃
      (fun k => (normalizedAtomNetwork net).W₂ k 0)
      (fun k => (normalizedAtomNetwork net).W₂ k 1) ⊆
        (networkAtomSlots net).erase i.val := by
  classical
  have hval : i.val≠j.val := fun h => hij (Subtype.ext h)
  intro k hk
  have hkactive := (Finset.mem_filter.mp hk).2
  have hki : k≠i.val := by
    intro he
    subst k
    have ho := transferOutput_source (normalizedAtomNetwork net).w₃ i.val j.val hval
    exact hkactive.2.2 ho
  refine Finset.mem_erase.mpr ⟨hki,?_⟩
  by_contra hkold
  have hkj : k≠j.val := by
    intro he
    exact hkold (he ▸ networkAtom_mem net j)
  have hun := normalizeAtoms_unselected net 0 (networkAtomSlots net) k hkold
  change (normalizedAtomNetwork net).W₂ k=net.W₂ k ∧
    (normalizedAtomNetwork net).b₂ k=net.b₂ k ∧
    (normalizedAtomNetwork net).w₃ k=net.w₃ k at hun
  have hout : (withOutput (normalizedAtomNetwork net)
      (transferOutput (normalizedAtomNetwork net).w₃ i.val j.val)
        (normalizedAtomNetwork net).b₃).w₃ k=net.w₃ k := by
    simp only [withOutput,transferOutput,if_neg hkj,if_neg hki,add_zero,sub_zero,hun.2.2]
  have h0 : (normalizedAtomNetwork net).W₂ k 0=net.W₂ k 0 := congrFun hun.1 0
  have h1 : (normalizedAtomNetwork net).W₂ k 1=net.W₂ k 1 := congrFun hun.1 1
  dsimp only at hkactive
  rw [hout,h0,h1] at hkactive
  exact hkold (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkactive⟩)

/-- An actual three-atom completion whose every offset is the target offset
joins an exact zero-bias completion with at most two active physical atoms.
There is no baseline or assumed normal-form hypothesis. -/
theorem allTarget_reduces_activeAtoms (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (hcode : codeDet U≠0)
    (hU : net.W₁=pairedRows U) (hb : net.HasZeroBiases)
    (hnet : ∀ x,net.eval x=Maximum 4 x)
    (hcard : (activeAtoms net.w₃ (fun k => net.W₂ k 0) (fun k => net.W₂ k 1)).card=3)
    (hoff : ∀ a b i,networkAtomOffset net U a b i=0) :
    ∃ endpoint : Network 4 6 m,
      endpoint.W₁=pairedRows U ∧ endpoint.HasZeroBiases ∧
      (∀ x,endpoint.eval x=Maximum 4 x) ∧
      (activeAtoms endpoint.w₃ (fun k => endpoint.W₂ k 0) (fun k => endpoint.W₂ k 1)).card≤2 ∧
      JoinedIn (ExactSet 4 6 m) net endpoint := by
  classical
  have hc : Fintype.card (NetworkAtoms net)=3 := (effectiveAtoms_card _ _ _).trans hcard
  obtain ⟨i,j,hij,hflip⟩ := Fintype.exists_ne_map_eq_of_card_lt (networkAtomFlip net)
    (show Fintype.card Bool<Fintype.card (NetworkAtoms net) by rw [hc];decide)
  have hn := normalizedAtomNetwork_joinedIn_exact net hnet
  let normalized := normalizedAtomNetwork net
  have hnb : normalized.HasZeroBiases := normalizeAtoms_zeroBiases net 0 (networkAtomSlots net) hb
  have hrow : normalized.W₂ i.val=normalized.W₂ j.val := by
    rw [allTarget_normalized_row net U hcode hoff i,
      allTarget_normalized_row net U hcode hoff j,hflip]
  have hbias : normalized.b₂ i.val=normalized.b₂ j.val := by rw [hnb.2.1];rfl
  let endpoint := withOutput normalized (transferOutput normalized.w₃ i.val j.val) normalized.b₃
  have heval : ∀ x,endpoint.eval x=Maximum 4 x := fun x =>
    (transferOutput_eval normalized i.val j.val hrow hbias x).trans (hn.target_mem x)
  have hp := duplicateTransferPath (⟨normalized,hn.target_mem⟩ : ExactFiber 4 6 m)
    i.val j.val hrow hbias
  have hj : JoinedIn (ExactSet 4 6 m) normalized endpoint :=
    ⟨hp.map continuous_subtype_val,fun t => (hp t).property⟩
  have hsub := transfer_normalized_atoms_subset net i j hij
  have hle := Finset.card_le_of_subset hsub
  have hslot : (networkAtomSlots net).card=3 := hcard
  rw [Finset.card_erase_of_mem (networkAtom_mem net i),hslot] at hle
  refine ⟨endpoint,hU,?_,heval,hle,hn.trans hj⟩
  exact ⟨hnb.1,hnb.2.1,hnb.2.2⟩

#print axioms allTarget_unitAtomRow
#print axioms allTarget_reduces_activeAtoms
end MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment
