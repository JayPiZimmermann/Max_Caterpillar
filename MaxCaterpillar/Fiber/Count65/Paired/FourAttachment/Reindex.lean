import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.Normalization
import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.PairedHalfline

/-! # A genuine physical ordering of the carrier and four effective atoms -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators Frontier Absorption

/-- All five physical slots are accounted for: the carrier is first, and the
four effective atoms retain any chosen ordering. This is an actual permutation. -/
theorem four_atom_physical_permutation (net : Network 4 6 5) (c : Fin 5)
    (e : Fin 4 ≃ NetworkAtoms net) (hc : ∀ i : NetworkAtoms net,i.val≠c) :
    ∃ q : Equiv.Perm (Fin 5),q 0=c ∧ ∀ i : Fin 4,q i.succ=(e i).val := by
  let f : Fin 5 → Fin 5 := Fin.cons c (fun i => (e i).val)
  have hinj : Function.Injective f := by
    intro a b
    refine Fin.cases ?_ (fun a => ?_) a
    · refine Fin.cases ?_ (fun b => ?_) b
      · intro _
        rfl
      · intro he
        exact False.elim (hc (e b) he.symm)
    · refine Fin.cases ?_ (fun b => ?_) b
      · intro he
        exact False.elim (hc (e a) he)
      · intro he
        have hab : a=b := e.injective (Subtype.ext he)
        exact congrArg Fin.succ hab
  let q : Equiv.Perm (Fin 5) := Equiv.ofBijective f ⟨hinj,Finite.surjective_of_injective hinj⟩
  exact ⟨q,rfl,fun _ => rfl⟩

noncomputable def fourReindexedNetwork (net : Network 4 6 5) (c : Fin 5)
    (q : Equiv.Perm (Fin 5)) : Network 4 6 5 :=
  permuteHidden (normalizeFourCarrier net c) (Equiv.refl _) q

lemma fourReindexed_output (net : Network 4 6 5) (c : Fin 5)
    (e : Fin 4 ≃ NetworkAtoms net) (hc : ∀ i : NetworkAtoms net,i.val≠c)
    (hcd : 0<net.w₃ c) (q : Equiv.Perm (Fin 5))
    (hq₀ : q 0=c) (hq : ∀ i : Fin 4,q i.succ=(e i).val) :
    (fourReindexedNetwork net c q).w₃=Fin.cons 1 (fun i => networkAtomJump net (e i)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · change (normalizeFourCarrier net c).w₃ (q 0)=1
    rw [hq₀,normalizeFourCarrier_output net c hcd]
  · change (normalizeFourCarrier net c).w₃ (q i.succ)=networkAtomJump net (e i)
    rw [hq,normalizeFourCarrier_atom_output net c (e i) (hc (e i))]

lemma fourReindexed_local_preact (net : Network 4 6 5) (c : Fin 5)
    (e : Fin 4 ≃ NetworkAtoms net) (hc : ∀ i : NetworkAtoms net,i.val≠c)
    (q : Equiv.Perm (Fin 5)) (hq : ∀ i : Fin 4,q i.succ=(e i).val)
    (U : Fin 2 → Fin 2 → ℝ) (hcode : codeDet U≠0)
    (hU : net.W₁=pairedRows U) (hb : net.HasZeroBiases) (i : Fin 4) (x : Point 4) :
    preact (fourReindexedNetwork net c q).W₁ (fourReindexedNetwork net c q).b₁
      ((fourReindexedNetwork net c q).W₂ i.succ) 0 x=
      if net.W₂ (e i).val 0<0 then
        -(preact (pairedRows U) 0 (comparisonRow U) 0 x-
          preact (pairedRows U) 0 (atomOffsetRow net U (e i)) 0 x)
      else preact (pairedRows U) 0 (comparisonRow U) 0 x-
        preact (pairedRows U) 0 (atomOffsetRow net U (e i)) 0 x := by
  have hrow : (fourReindexedNetwork net c q).W₂ i.succ=(normalizedAtomNetwork net).W₂ (e i).val := by
    change (fun j => (normalizeFourCarrier net c).W₂ (q i.succ) ((Equiv.refl _) j))=_
    rw [hq]
    exact normalizeFourCarrier_atom_row net c (e i) (hc (e i))
  have hfirst : (fourReindexedNetwork net c q).W₁=pairedRows U := hU
  have hbfirst : (fourReindexedNetwork net c q).b₁=0 := hb.1
  rw [hrow,hfirst,hbfirst]
  by_cases hn : net.W₂ (e i).val 0<0
  · rw [if_pos hn,normalizedAtomNetwork_row_neg net (e i) hn]
    have hneg : preact (pairedRows U) 0 (-unitAtomRow net (e i)) 0 x=
        -preact (pairedRows U) 0 (unitAtomRow net (e i)) 0 x := by
      simpa only [neg_zero] using preact_neg (pairedRows U) 0 (unitAtomRow net (e i)) 0 x
    rw [hneg]
    simp only [atomOffsetRow,preact_sub_zero]
    ring
  · have hp : 0<net.W₂ (e i).val 0 :=
      lt_of_le_of_ne (not_lt.mp hn) (Ne.symm (networkAtom_comparison_ne_zero net (e i)))
    rw [if_neg hn,normalizedAtomNetwork_row_pos net (e i) hp]
    simp only [atomOffsetRow,preact_sub_zero]
    ring

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
