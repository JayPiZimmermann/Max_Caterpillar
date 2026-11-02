import MaxCaterpillar.Fiber.Count65.Paired.ThreeAtoms.Normalization
import MaxCaterpillar.Fiber.Count65.Paired.RowInterpolation

/-! Natural-input switching row identities and a physical literal-row replacement. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Frontier Absorption PairNormalization
variable {m : ℕ}

noncomputable def networkAtomFlip (net : Network 4 6 m) (i : NetworkAtoms net) : Bool :=
  decide (net.W₂ i.val 0 < 0)

theorem normalizedAtomNetwork_row_oriented (net : Network 4 6 m) (i : NetworkAtoms net) :
    (normalizedAtomNetwork net).W₂ i.val =
      if networkAtomFlip net i then -unitAtomRow net i else unitAtomRow net i := by
  by_cases hn : net.W₂ i.val 0 < 0
  · simpa [networkAtomFlip,hn] using normalizedAtomNetwork_row_neg net i hn
  · have hp : 0 < net.W₂ i.val 0 :=
      lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (networkAtom_comparison_ne_zero net i))
    simpa [networkAtomFlip,hn] using normalizedAtomNetwork_row_pos net i hp

lemma preact_pairedRows_zero (U : Fin 2 → Fin 2 → ℝ) (H : Fin 6 → ℝ) (x : Point 4) :
    preact (pairedRows U) 0 H 0 x = endpointForm U H x := by
  simp [preact,endpointForm,endpointFeature]

theorem three_atom_switching_offset_rows (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (hcode : codeDet U ≠ 0) (e : Fin 3 ≃ NetworkAtoms net)
    (hoff : ∀ a b, networkAtomOffset net U a b (e 0)*networkAtomOffset net U a b (e 1)=0 ∧
      networkAtomOffset net U a b (e 2)=
        networkAtomOffset net U a b (e 0)+networkAtomOffset net U a b (e 1)) :
    (∀ x, endpointForm U (atomOffsetRow net U (e 0)) x *
      endpointForm U (atomOffsetRow net U (e 1)) x = 0) ∧
    (∀ x, endpointForm U (unitAtomRow net (e 2)) x =
      endpointForm U (comparisonRow U-atomOffsetRow net U (e 0)-atomOffsetRow net U (e 1)) x) := by
  constructor
  · intro x
    rw [atomOffsetRow_form net U hcode,atomOffsetRow_form net U hcode]
    exact (hoff (x 1) (x 3)).1
  · intro x
    have hlin : endpointForm U (comparisonRow U-atomOffsetRow net U (e 0)-
        atomOffsetRow net U (e 1)) x = endpointForm U (comparisonRow U) x-
        endpointForm U (atomOffsetRow net U (e 0)) x-
        endpointForm U (atomOffsetRow net U (e 1)) x := by
      simp [endpointForm,sub_mul,Finset.sum_sub_distrib]
    rw [hlin,unitAtomRow_natural_offset net U hcode,
      atomOffsetRow_form net U hcode,atomOffsetRow_form net U hcode,
      (hoff (x 1) (x 3)).2]
    ring

noncomputable def switchingThirdRow (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (e : Fin 3 ≃ NetworkAtoms net) : Fin 6 → ℝ :=
  if networkAtomFlip net (e 2) then
    -(comparisonRow U-atomOffsetRow net U (e 0)-atomOffsetRow net U (e 1))
  else comparisonRow U-atomOffsetRow net U (e 0)-atomOffsetRow net U (e 1)

theorem switchingThirdRow_preact (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (hcode : codeDet U ≠ 0)
    (hU : net.W₁ = pairedRows U) (hb : net.HasZeroBiases) (e : Fin 3 ≃ NetworkAtoms net)
    (hoff : ∀ a b, networkAtomOffset net U a b (e 0)*networkAtomOffset net U a b (e 1)=0 ∧
      networkAtomOffset net U a b (e 2)=
        networkAtomOffset net U a b (e 0)+networkAtomOffset net U a b (e 1)) (x : Point 4) :
    preact (normalizedAtomNetwork net).W₁ (normalizedAtomNetwork net).b₁
      (switchingThirdRow net U e) ((normalizedAtomNetwork net).b₂ (e 2).val) x =
    preact (normalizedAtomNetwork net).W₁ (normalizedAtomNetwork net).b₁
      ((normalizedAtomNetwork net).W₂ (e 2).val) ((normalizedAtomNetwork net).b₂ (e 2).val) x := by
  have hnb := normalizeAtoms_zeroBiases net 0 (networkAtomSlots net) hb
  change (normalizedAtomNetwork net).HasZeroBiases at hnb
  rw [hnb.1,hnb.2.1]
  change preact net.W₁ 0 (switchingThirdRow net U e) 0 x =
    preact net.W₁ 0 ((normalizedAtomNetwork net).W₂ (e 2).val) 0 x
  rw [hU,preact_pairedRows_zero,preact_pairedRows_zero,normalizedAtomNetwork_row_oriented]
  have hh := (three_atom_switching_offset_rows net U hcode e hoff).2 x
  unfold switchingThirdRow
  cases hflip : networkAtomFlip net (e 2) <;> simp only [hflip,if_true,if_false]
  · exact hh.symm
  · rw [endpointForm_neg,endpointForm_neg,hh]

noncomputable def switchingLiteralRows (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (e : Fin 3 ≃ NetworkAtoms net) : Fin m → Fin 6 → ℝ :=
  Function.update (normalizedAtomNetwork net).W₂ (e 2).val (switchingThirdRow net U e)

lemma comparison_sub_atomOffsetRow (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (i : NetworkAtoms net) :
    comparisonRow U-atomOffsetRow net U i = unitAtomRow net i := by
  funext j
  simp only [atomOffsetRow,Pi.sub_apply]
  ring

lemma switchingLiteralRows_first (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (e : Fin 3 ≃ NetworkAtoms net)
    (i : Fin 3) (hi : i ≠ 2) :
    switchingLiteralRows net U e (e i).val =
      if networkAtomFlip net (e i) then -(comparisonRow U-atomOffsetRow net U (e i))
      else comparisonRow U-atomOffsetRow net U (e i) := by
  have hne : (e i).val ≠ (e 2).val := by
    intro hh
    exact hi (e.injective (Subtype.ext hh))
  simp only [switchingLiteralRows,Function.update_noteq hne,
    comparison_sub_atomOffsetRow,normalizedAtomNetwork_row_oriented]

lemma switchingLiteralRows_third (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (e : Fin 3 ≃ NetworkAtoms net) :
    switchingLiteralRows net U e (e 2).val = switchingThirdRow net U e :=
  Function.update_same _ _ _

lemma switchingLiteralRows_spectator (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (e : Fin 3 ≃ NetworkAtoms net)
    (k : Fin m) (hk : k ∉ networkAtomSlots net) :
    switchingLiteralRows net U e k = net.W₂ k := by
  have hne : k ≠ (e 2).val := by
    intro hh
    exact hk (hh ▸ networkAtom_mem net (e 2))
  simp only [switchingLiteralRows,Function.update_noteq hne]
  exact (normalizeAtoms_unselected net 0 _ k hk).1

/-- The functional third row is replaced by the literal switching row through
an actual exact-fiber path. Both other atoms and all spectators stay fixed. -/
theorem switchingLiteralRows_joinedIn_exact (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (hcode : codeDet U ≠ 0)
    (hU : net.W₁ = pairedRows U) (hb : net.HasZeroBiases)
    (hnet : ∀ x, net.eval x = Maximum 4 x) (e : Fin 3 ≃ NetworkAtoms net)
    (hoff : ∀ a b, networkAtomOffset net U a b (e 0)*networkAtomOffset net U a b (e 1)=0 ∧
      networkAtomOffset net U a b (e 2)=
        networkAtomOffset net U a b (e 0)+networkAtomOffset net U a b (e 1)) :
    JoinedIn (ExactSet 4 6 m) net
      (withSecondRows (normalizedAtomNetwork net) (switchingLiteralRows net U e)
        (normalizedAtomNetwork net).b₂) := by
  have hn := normalizedAtomNetwork_joinedIn_exact net hnet
  let a : ExactFiber 4 6 m := ⟨normalizedAtomNetwork net,hn.target_mem⟩
  have hrows : ∀ k, a.val.w₃ k ≠ 0 → ∀ x,
      preact a.val.W₁ a.val.b₁ (switchingLiteralRows net U e k) (a.val.b₂ k) x =
        preact a.val.W₁ a.val.b₁ (a.val.W₂ k) (a.val.b₂ k) x := by
    intro k _ x
    by_cases hk : k = (e 2).val
    · subst k
      simp only [switchingLiteralRows,Function.update_same]
      exact switchingThirdRow_preact net U hcode hU hb e hoff x
    · simp only [switchingLiteralRows,Function.update_noteq hk]
  have hp := rowInterpolationPath a (switchingLiteralRows net U e) a.val.b₂ hrows
  exact hn.trans ⟨hp.map continuous_subtype_val,fun t => (hp t).property⟩

end MaxCaterpillar.Fiber.Count65.Paired
