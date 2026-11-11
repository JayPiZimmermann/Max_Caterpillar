import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.Reindex
import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.Representation
import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.SupportExtraction

/-! # Actual four-atom completions reach their extracted oriented family

Only a genuine physical hidden permutation separates the two displayed exact
parameter paths. No path or attachment conclusion is assumed in extraction.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators Frontier Absorption

noncomputable def fourAtomFlip (net : Network 4 6 5) (e : Fin 4 ≃ NetworkAtoms net)
    (i : Fin 4) : Bool := decide (net.W₂ (e i).val 0<0)

lemma codeOffsetRow_balance (net : Network 4 6 5) (U : Fin 2 → Fin 2 → ℝ)
    (hU : net.W₁=pairedRows U) (hcode : codeDet U≠0) (hb : net.HasZeroBiases)
    (hnet : ∀ x,net.eval x=Maximum 4 x) (e : Fin 4 ≃ NetworkAtoms net) (x : Point 4) :
    Paired65.AtomBalance (fun i => networkAtomJump net (e i))
      (fun i => preact (pairedRows U) 0 (codeOffsetRow net U (e i)) 0 x) := by
  apply Paired65.atomBalance_of_relu_identity
  intro z
  simp_rw [paired_preact_eq_endpointForm,codeOffsetRow_form net U hcode]
  have hr := Fintype.sum_equiv e
    (fun i : Fin 4 => networkAtomJump net (e i)*relu (z-networkAtomOffset net U (x 1) (x 3) (e i)))
    (fun i : NetworkAtoms net => networkAtomJump net i*relu (z-networkAtomOffset net U (x 1) (x 3) i))
    (fun _ => rfl)
  rw [hr]
  exact Paired65.relu_identity_of_atomBalance _ _
    (network_effective_atomBalance net U hU hb hnet (x 1) (x 3)) z

/-- Every arbitrary-real exact paired `(6,5)` completion with four effective
atoms reaches the fully explicit signed-code offset family, up to one genuine
second-hidden-layer permutation. The conclusion records both actual paths. -/
theorem network_four_oriented_representation (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁=pairedRows U) (hcode : codeDet U≠0)
    (hb : net.HasZeroBiases) (hnet : ∀ x,net.eval x=Maximum 4 x)
    (hfour : (activeAtoms net.w₃ (fun i => net.W₂ i 0) (fun i => net.W₂ i 1)).card=4) :
    ∃ (c : Fin 5) (e : Fin 4 ≃ NetworkAtoms net) (q : Equiv.Perm (Fin 5)),
      q 0=c ∧ (∀ i : Fin 4,q i.succ=(e i).val) ∧
      JoinedIn (ExactSet 4 6 5) net (normalizeFourCarrier net c) ∧
      JoinedIn (ExactSet 4 6 5) (fourReindexedNetwork net c q)
        (orientedCompletionNet (pairedRows U) 0 (baselineRow U) (comparisonRow U)
          (fun i => codeOffsetRow net U (e i)) (fun i => networkAtomJump net (e i))
          (fourAtomFlip net e)) ∧
      (∀ x,0≤preact (pairedRows U) 0
        (carrierRow (fun i => networkAtomJump net (e i)) (fourAtomFlip net e)
          (baselineRow U) (comparisonRow U) (fun i => codeOffsetRow net U (e i))) 0 x) := by
  classical
  obtain ⟨c,hcs,hcd,hrest,hg⟩ := network_four_atoms_unique_carrier net U hU hb hnet hfour
  have hc : ∀ i : NetworkAtoms net,i.val≠c := by
    intro i he
    have hi := networkAtom_common_zero net i
    rw [he] at hi
    linarith only [hcs,hi]
  have hcard : Fintype.card (NetworkAtoms net)=4 :=
    (effectiveAtoms_card _ _ _).trans hfour
  let e : Fin 4 ≃ NetworkAtoms net := (Fintype.equivFinOfCardEq hcard).symm
  obtain ⟨q,hq₀,hq⟩ := four_atom_physical_permutation net c e hc
  let a := fourReindexedNetwork net c q
  let j := fun i : Fin 4 => networkAtomJump net (e i)
  let F := fun i : Fin 4 => codeOffsetRow net U (e i)
  let flip := fourAtomFlip net e
  have hs := fourCarrierScales_pos net c hcd (fun i hi => (hrest i hi).2.1)
  have ha : ∀ x,a.eval x=Maximum 4 x := by
    intro x
    exact (permuteHidden_eval _ (Equiv.refl _) q x).trans
      ((scaleSecond_eval net _ hs x).trans (hnet x))
  have hbn := normalizeFourCarrier_zeroBias net c hb
  have hafirst : a.W₁=pairedRows U := hU
  have hab : a.HasZeroBiases := by
    refine ⟨hbn.1,?_,hbn.2.2⟩
    funext i
    change (normalizeFourCarrier net c).b₂ (q i)=0
    rw [hbn.2.1]
    rfl
  have hout : a.w₃=Fin.cons 1 j := fourReindexed_output net c e hc hcd q hq₀ hq
  have hloc : ∀ i x,preact a.W₁ a.b₁ (a.W₂ i.succ) 0 x=
      if flip i then -(preact a.W₁ a.b₁ (comparisonRow U) 0 x-preact a.W₁ a.b₁ (F i) 0 x)
      else preact a.W₁ a.b₁ (comparisonRow U) 0 x-preact a.W₁ a.b₁ (F i) 0 x := by
    intro i x
    have hp := fourReindexed_local_preact net c e hc q hq U hcode hU hb i x
    have hf : preact (pairedRows U) 0 (atomOffsetRow net U (e i)) 0 x=
        preact (pairedRows U) 0 (F i) 0 x := by
      rw [paired_preact_eq_endpointForm,paired_preact_eq_endpointForm,
        atomOffsetRow_form net U hcode,codeOffsetRow_form net U hcode]
    rw [hf] at hp
    simpa only [a,flip,fourAtomFlip,decide_eq_true_eq,hafirst,hab.1] using hp
  have hbal : ∀ x,Paired65.AtomBalance j (fun i => preact a.W₁ a.b₁ (F i) 0 x) := by
    intro x
    rw [hafirst,hab.1]
    exact codeOffsetRow_balance net U hU hcode hb hnet e x
  have hag : ∀ x,0≤preact a.W₁ a.b₁ (a.W₂ 0) 0 x := by
    intro x
    have hcg := mul_nonneg (hs c).le (hg x)
    have hp := PairNormalization.scaleSecond_preact net (fourCarrierScales net c) c x
    change 0≤preact (normalizeFourCarrier net c).W₁ (normalizeFourCarrier net c).b₁
      ((normalizeFourCarrier net c).W₂ (q 0)) 0 x
    rw [hq₀]
    have hn : 0≤preact (normalizeFourCarrier net c).W₁ (normalizeFourCarrier net c).b₁
        ((normalizeFourCarrier net c).W₂ c) ((normalizeFourCarrier net c).b₂ c) x := by
      unfold normalizeFourCarrier
      rw [hp]
      exact hcg
    simpa only [hbn.2.1,Pi.zero_apply] using hn
  have hmax : ∀ x,preact a.W₁ a.b₁ (baselineRow U) 0 x+
      relu (preact a.W₁ a.b₁ (comparisonRow U) 0 x)=Maximum 4 x := by
    intro x
    rw [hafirst,hab.1]
    exact paired_max_decomposition U hcode x
  let af : ExactFiber 4 6 5 := ⟨a,ha⟩
  have hpath := orientedCompletion_rowReplacement af (baselineRow U) (comparisonRow U) F j flip
    hab.2.1 hab.2.2 hout hloc hbal hag hmax
  have heq : withSecondRows a
      (Fin.cons (carrierRow j flip (baselineRow U) (comparisonRow U) F)
        (fun i => if flip i then -(comparisonRow U-F i) else comparisonRow U-F i)) 0=
      orientedCompletionNet (pairedRows U) 0 (baselineRow U) (comparisonRow U) F j flip := by
    change Network.mk a.W₁ a.b₁ _ 0 a.w₃ a.b₃=Network.mk _ _ _ _ _ _
    rw [hafirst,hab.1,hout,hab.2.2]
  rw [heq] at hpath
  refine ⟨c,e,q,hq₀,hq,normalizeFourCarrier_joinedIn_exact net hnet c hcd
    (fun i hi => (hrest i hi).2.1),hpath,?_⟩
  intro x
  have he := orientedCompletion_carrier_forced af (baselineRow U) (comparisonRow U) F j flip
    hab.2.1 hab.2.2 hout hloc hbal hag hmax x
  rw [hafirst,hab.1] at he
  rw [← he]
  simpa only [hafirst,hab.1] using hag x

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
