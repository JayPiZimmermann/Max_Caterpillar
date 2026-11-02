import MaxCaterpillar.Fiber.Count65.Paired.PhysicalCarrier
import MaxCaterpillar.Fiber.Count65.Paired.ThreeAtoms.Normalization

/-! # Normalize every actual four-atom completion, including its carrier -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators Absorption PairNormalization

noncomputable def fourCarrierScales (net : Network 4 6 5) (c : Fin 5) (i : Fin 5) : ℝ :=
  if i=c then net.w₃ c else 1/|net.W₂ i 0|

noncomputable def normalizeFourCarrier (net : Network 4 6 5) (c : Fin 5) : Network 4 6 5 :=
  scaleSecond net (fourCarrierScales net c)

lemma fourCarrierScales_pos (net : Network 4 6 5) (c : Fin 5)
    (hc : 0<net.w₃ c) (hrest : ∀ i,i≠c → net.W₂ i 0≠0) :
    ∀ i,0<fourCarrierScales net c i := by
  intro i
  by_cases hi : i=c
  · simp [fourCarrierScales,hi,hc]
  · simp only [fourCarrierScales,if_neg hi]
    exact one_div_pos.mpr (abs_pos.mpr (hrest i hi))

lemma normalizeFourCarrier_output (net : Network 4 6 5) (c : Fin 5) (hc : 0<net.w₃ c) :
    (normalizeFourCarrier net c).w₃ c=1 := by
  simp [normalizeFourCarrier,scaleSecond,fourCarrierScales,ne_of_gt hc]

lemma normalizeFourCarrier_atom_row (net : Network 4 6 5) (c : Fin 5)
    (i : NetworkAtoms net) (hic : i.val≠c) :
    (normalizeFourCarrier net c).W₂ i.val=(normalizedAtomNetwork net).W₂ i.val := by
  funext l
  rw [normalizedAtomNetwork,normalizeAtoms_selected_row net 0 _ i.val (networkAtom_mem net i)]
  simp [normalizeFourCarrier,scaleSecond,fourCarrierScales,hic,div_eq_mul_inv,mul_comm]

lemma normalizeFourCarrier_atom_output (net : Network 4 6 5) (c : Fin 5)
    (i : NetworkAtoms net) (hic : i.val≠c) :
    (normalizeFourCarrier net c).w₃ i.val=networkAtomJump net i := by
  rw [← normalizedAtomNetwork_output net i]
  change net.w₃ i.val/fourCarrierScales net c i.val=
    (normalizedAtomNetwork net).w₃ i.val
  rw [normalizedAtomNetwork_output]
  simp [fourCarrierScales,hic,networkAtomJump,jumpWeights,networkAtom_common_zero net i,div_div]

lemma normalizeFourCarrier_zeroBias (net : Network 4 6 5) (c : Fin 5)
    (hb : net.HasZeroBiases) : (normalizeFourCarrier net c).HasZeroBiases := by
  rcases hb with ⟨hb₁,hb₂,hb₃⟩
  refine ⟨hb₁,?_,hb₃⟩
  funext i
  simp [normalizeFourCarrier,scaleSecond,hb₂]

lemma normalizeFourCarrier_eval (net : Network 4 6 5) (c : Fin 5)
    (hc : 0<net.w₃ c) (hrest : ∀ i,i≠c → net.W₂ i 0≠0) (x : Point 4) :
    (normalizeFourCarrier net c).eval x=net.eval x :=
  scaleSecond_eval net _ (fourCarrierScales_pos net c hc hrest) x

lemma normalizeFourCarrier_joinedIn_exact (net : Network 4 6 5)
    (hnet : ∀ x,net.eval x=Maximum 4 x) (c : Fin 5)
    (hc : 0<net.w₃ c) (hrest : ∀ i,i≠c → net.W₂ i 0≠0) :
    JoinedIn (ExactSet 4 6 5) net (normalizeFourCarrier net c) := by
  let a : ExactFiber 4 6 5 := ⟨net,hnet⟩
  have p := scaleSecondPath (fourCarrierScales net c) (fourCarrierScales_pos net c hc hrest) a
  exact ⟨p.map continuous_subtype_val,fun t => (p t).property⟩

/-- Arbitrary all-real exact four-atom completions admit an actual positive
normalization path. The unique carrier's output becomes one, and every local
atom becomes the usual absolute-slope normalized physical atom. -/
theorem network_four_normalization (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁=pairedRows U)
    (hb : net.HasZeroBiases) (hnet : ∀ x,net.eval x=Maximum 4 x)
    (hfour : (activeAtoms net.w₃ (fun i => net.W₂ i 0) (fun i => net.W₂ i 1)).card=4) :
    ∃ c : Fin 5,
      (∀ i : NetworkAtoms net,i.val≠c) ∧
      JoinedIn (ExactSet 4 6 5) net (normalizeFourCarrier net c) ∧
      (normalizeFourCarrier net c).W₁=pairedRows U ∧
      (normalizeFourCarrier net c).HasZeroBiases ∧
      (normalizeFourCarrier net c).w₃ c=1 ∧
      (∀ i : NetworkAtoms net,(normalizeFourCarrier net c).W₂ i.val=(normalizedAtomNetwork net).W₂ i.val ∧
        (normalizeFourCarrier net c).w₃ i.val=networkAtomJump net i) ∧
      (∀ x,0≤preact (normalizeFourCarrier net c).W₁ (normalizeFourCarrier net c).b₁
        ((normalizeFourCarrier net c).W₂ c) ((normalizeFourCarrier net c).b₂ c) x) := by
  obtain ⟨c,hcs,hcd,hrest,hg⟩ := network_four_atoms_unique_carrier net U hU hb hnet hfour
  have hlocal : ∀ i : NetworkAtoms net,i.val≠c := by
    intro i hic
    have hc0 := networkAtom_common_zero net i
    rw [hic] at hc0
    linarith only [hcs,hc0]
  refine ⟨c,hlocal,normalizeFourCarrier_joinedIn_exact net hnet c hcd (fun i hi => (hrest i hi).2.1),
    hU,normalizeFourCarrier_zeroBias net c hb,normalizeFourCarrier_output net c hcd,?_,?_⟩
  · intro i
    exact ⟨normalizeFourCarrier_atom_row net c i (hlocal i),normalizeFourCarrier_atom_output net c i (hlocal i)⟩
  · intro x
    rw [normalizeFourCarrier,scaleSecond_preact]
    exact mul_nonneg (by simpa [fourCarrierScales] using hcd.le) (hg x)

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
