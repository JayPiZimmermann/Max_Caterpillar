import MaxCaterpillar.Frontier.RandomRestriction.GoodEventCherriesDefs

/-! # Disjoint actual cherry slots and the deterministic deletion bound -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
variable {m : ℕ}

/-- All endpoints of all isolated selected gaps are distinct. -/
theorem isolatedGapEndpoint_injective (Γ : Finset (Fin m)) :
    Function.Injective (isolatedGapEndpoint Γ) := by
  rintro ⟨g,i⟩ ⟨h,j⟩ heq
  have hg := (mem_isolatedGaps g.val Γ).mp g.property
  have hh := (mem_isolatedGaps h.val Γ).mp h.property
  have hgs := isolatedGapPredecessor_succ g.val hg.2.1
  have hhs := isolatedGapPredecessor_succ h.val hh.2.1
  cases i <;> cases j
  · change isolatedGapPredecessor g.val = isolatedGapPredecessor h.val at heq
    have hv := congrArg Fin.val heq
    have gh : g = h := by
      apply Subtype.ext
      apply Fin.ext
      linarith only [hv,hgs,hhs]
    exact Prod.ext gh rfl
  · change isolatedGapPredecessor g.val = h.val at heq
    exfalso
    apply (hg.2.2 h.val hh.1).1
    have hv := congrArg Fin.val heq
    linarith only [hv,hgs]
  · change g.val = isolatedGapPredecessor h.val at heq
    exfalso
    apply (hh.2.2 g.val hg.1).1
    have hv := congrArg Fin.val heq
    linarith only [hv,hhs]
  · change g.val = h.val at heq
    exact Prod.ext (Subtype.ext heq) rfl

/-- The literal slot map can be supplied directly to the local-coin matching. -/
def isolatedGapSlots (Γ : Finset (Fin m)) : (↥(isolatedGaps Γ) × Bool) ↪ Fin m :=
  ⟨isolatedGapEndpoint Γ,isolatedGapEndpoint_injective Γ⟩

/-- Only the anchor gap and endpoints of selected adjacent gap pairs are deleted. -/
theorem card_le_isolated_add_one_add_two_adjacent (Γ : Finset (Fin m)) :
    Γ.card ≤ (isolatedGaps Γ).card + 1 + 2 * (selectedGapAdjacencies Γ).card := by
  classical
  let Z := Γ.filter (fun g => g.val = 0)
  let A := selectedGapAdjacencies Γ
  have hz : Z.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro g hg h hh
    apply Fin.ext
    exact (Finset.mem_filter.mp hg).2.trans (Finset.mem_filter.mp hh).2.symm
  have hcover : Γ ⊆ (isolatedGaps Γ ∪ Z) ∪ (A.image Prod.fst ∪ A.image Prod.snd) := by
    intro g hg
    by_cases hgi : g ∈ isolatedGaps Γ
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hgi)
    by_cases hg0 : g.val = 0
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hg,hg0⟩))
    have hgpos : 0 < g.val := Nat.pos_of_ne_zero hg0
    have hn : ¬ (∀ h ∈ Γ, h.val + 1 ≠ g.val ∧ g.val + 1 ≠ h.val) := by
      intro hn
      exact hgi ((mem_isolatedGaps g Γ).mpr ⟨hg,hgpos,hn⟩)
    push_neg at hn
    obtain ⟨h,hh,hrel⟩ := hn
    apply Finset.mem_union_right
    by_cases hleft : h.val + 1 = g.val
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(h,g),(mem_selectedGapAdjacencies h g Γ).mpr ⟨hleft,hh,hg⟩,rfl⟩
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨(g,h),(mem_selectedGapAdjacencies g h Γ).mpr ⟨hrel hleft,hg,hh⟩,rfl⟩
  have hc := Finset.card_le_of_subset hcover
  have hu := Finset.card_union_le (isolatedGaps Γ ∪ Z) (A.image Prod.fst ∪ A.image Prod.snd)
  have hi := Finset.card_union_le (isolatedGaps Γ) Z
  have ha := Finset.card_union_le (A.image Prod.fst) (A.image Prod.snd)
  have hf := Finset.card_image_le (s := A) (f := Prod.fst)
  have hs := Finset.card_image_le (s := A) (f := Prod.snd)
  change Γ.card ≤ (isolatedGaps Γ).card + 1 + 2 * A.card
  calc
    Γ.card ≤ ((isolatedGaps Γ ∪ Z) ∪ (A.image Prod.fst ∪ A.image Prod.snd)).card := hc
    _ ≤ ((isolatedGaps Γ).card + Z.card) +
        ((A.image Prod.fst).card + (A.image Prod.snd).card) :=
      le_trans hu (add_le_add hi ha)
    _ ≤ ((isolatedGaps Γ).card + 1) + (A.card + A.card) :=
      add_le_add (Nat.add_le_add_left hz _) (add_le_add hf hs)
    _ = (isolatedGaps Γ).card + 1 + 2 * A.card := by rw [two_mul]

theorem isolatedGaps_card_lower_bound (Γ : Finset (Fin m)) :
    Γ.card - 1 - 2 * (selectedGapAdjacencies Γ).card ≤ (isolatedGaps Γ).card := by
  apply tsub_le_iff_right.mpr
  apply tsub_le_iff_right.mpr
  have hc := card_le_isolated_add_one_add_two_adjacent Γ
  linarith only [hc]

#print axioms isolatedGapEndpoint_injective
#print axioms card_le_isolated_add_one_add_two_adjacent
end MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
