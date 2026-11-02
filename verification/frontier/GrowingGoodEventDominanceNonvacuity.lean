import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance

/-! Independent nonvacuity for every selected arity, including k=0 and k=1.
The original row is constructed on the actual Fin(4+k) label set. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominanceNonvacuity
open BigOperators Configurations Cartesian DominantGap GoodEventDominance
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
  (smallRankGaps mem_smallRankGaps isolatedGaps mem_isolatedGaps)

private def tailValues : Fin 4→ℝ := ![1,-1,1,-1]

/-- All selected labels have weight zero; the four genuine tail labels carry
1,-1,1,-1 in actual position order. -/
noncomputable def witnessRow (k : ℕ) : Point (4+k) := fun i =>
  match (fullPositionEquiv k 4).symm i with
  | Sum.inl _ => 0
  | Sum.inr t => tailValues t

lemma witnessRow_selected (k : ℕ) (s : Fin k) :
    witnessRow k (selectedPosition k 4 s)=0 := by
  rw [←fullPositionEquiv_selected k 4 s]
  simp only [witnessRow,Equiv.symm_apply_apply]

lemma witnessRow_tail (k : ℕ) (t : Fin 4) :
    witnessRow k (tailPosition k 4 t)=tailValues t := by
  rw [←fullPositionEquiv_tail k 4 t]
  simp only [witnessRow,Equiv.symm_apply_apply]

lemma witnessRow_sum (k : ℕ) : (∑ i,witnessRow k i)=0 := by
  rw [sum_full_positions (witnessRow k)]
  simp_rw [witnessRow_selected,witnessRow_tail]
  norm_num [Fin.sum_univ_succ,Fin.sum_univ_zero,tailValues]

lemma witnessRow_support (k : ℕ) : NormalizedNetwork.rowSupport (witnessRow k)=
    (Finset.univ : Finset (Fin 4)).image (tailPosition k 4) := by
  classical
  ext i
  constructor
  · intro hi
    have hw := (NormalizedNetwork.mem_rowSupport (witnessRow k) i).mp hi
    rcases full_position_cases (k:=k) (m:=4) i with ⟨s,he⟩ | ⟨t,he⟩
    · rw [he,witnessRow_selected] at hw
      exact (hw rfl).elim
    · exact Finset.mem_image.mpr ⟨t,Finset.mem_univ _,he.symm⟩
  · intro hi
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hi
    apply (NormalizedNetwork.mem_rowSupport (witnessRow k) _).mpr
    rw [witnessRow_tail]
    fin_cases t <;> norm_num [tailValues]

lemma witnessRow_support_card (k : ℕ) :
    (NormalizedNetwork.rowSupport (witnessRow k)).card=4 := by
  rw [witnessRow_support,Finset.card_image_of_injective _ (tailPosition k 4).injective,
    Finset.card_univ,Fintype.card_fin]

private def collapsedValues : Option (Fin 4)→ℝ
  | none => 0
  | some t => tailValues t

lemma witnessRow_collapse (k : ℕ) :
    collapsedRow k (Equiv.refl _) (witnessRow k)=collapsedValues := by
  funext x
  cases x with
  | none =>
    change (∑ s : Fin k,witnessRow k (selectedPosition k 4 s))=0
    simp_rw [witnessRow_selected]
    exact Finset.sum_const_zero
  | some t => exact witnessRow_tail k t

/-- The actual rank vector is [2,1,3,0], not an abstract cherry condition. -/
def witnessRank : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 2).trans (Equiv.swap 0 3)
lemma witnessRank_values (i : Fin 4) : witnessRank i=![2,1,3,0] i := by
  fin_cases i <;> decide

lemma witnessLowRanks : smallRankGaps witnessRank 2=({1,3} : Finset (Fin 4)) := by
  ext g
  rw [mem_smallRankGaps]
  fin_cases g <;> decide

lemma witness_isolated : (1 : Fin 4)∈isolatedGaps (smallRankGaps witnessRank 2) := by
  rw [witnessLowRanks]
  apply (mem_isolatedGaps 1 ({1,3} : Finset (Fin 4))).mpr
  decide

lemma witness_coefficients (g : Fin 4) :
    tailCoefficient (positionConfig witnessRank) collapsedValues g=![0,1,0,1] g := by
  fin_cases g <;>
    norm_num [tailCoefficient,positionConfig,collapsedValues,tailValues,
      Finset.sum_filter,Fin.sum_univ_succ,Fin.sum_univ_zero]

lemma witness_dominant : GapDominant (positionConfig witnessRank) collapsedValues 1 := by
  constructor
  · rw [witness_coefficients]
    norm_num
  · intro i hi hne
    rw [witness_coefficients] at hi
    fin_cases i
    · norm_num at hi
    · exact (hne rfl).elim
    · norm_num at hi
    · change (witnessRank 3).val<(witnessRank 1).val
      rw [witnessRank_values,witnessRank_values]
      decide

/-- Every selected arity has an actual zero-sum support-four original row,
full permutation and rank permutation with an isolated dominant nonzero gap. -/
theorem every_selected_arity_has_isolated_dominant (k : ℕ) :
    ∃ w : Point (4+k),∃ σ : Equiv.Perm (Fin (4+k)),∃ ρ : Equiv.Perm (Fin 4),
      ∃ K : ℕ,∃ g : Fin 4,
        (∑ i,w i)=0 ∧ 3≤(NormalizedNetwork.rowSupport w).card ∧
        GapDominant (positionConfig ρ) (collapsedRow k σ w) g ∧
        g∈isolatedGaps (smallRankGaps ρ K) := by
  refine ⟨witnessRow k,Equiv.refl _,witnessRank,2,1,witnessRow_sum k,?_,?_,witness_isolated⟩
  · rw [witnessRow_support_card]
    decide
  · rw [witnessRow_collapse]
    exact witness_dominant

/-- The zero-selected-arity boundary satisfies the same actual hypotheses. -/
example : ∃ w : Point (4+0),∃ σ : Equiv.Perm (Fin (4+0)),∃ ρ : Equiv.Perm (Fin 4),
    ∃ K : ℕ,∃ g : Fin 4,
      (∑ i,w i)=0 ∧ 3≤(NormalizedNetwork.rowSupport w).card ∧
      GapDominant (positionConfig ρ) (collapsedRow 0 σ w) g ∧
      g∈isolatedGaps (smallRankGaps ρ K) := every_selected_arity_has_isolated_dominant 0
example : ∃ w : Point (4+1),∃ σ : Equiv.Perm (Fin (4+1)),∃ ρ : Equiv.Perm (Fin 4),
    ∃ K : ℕ,∃ g : Fin 4,
      (∑ i,w i)=0 ∧ 3≤(NormalizedNetwork.rowSupport w).card ∧
      GapDominant (positionConfig ρ) (collapsedRow 1 σ w) g ∧
      g∈isolatedGaps (smallRankGaps ρ K) := every_selected_arity_has_isolated_dominant 1

#check @every_selected_arity_has_isolated_dominant
#print axioms witnessRow_sum
#print axioms witnessRow_support_card
#print axioms witnessRow_collapse
#print axioms witness_isolated
#print axioms witness_dominant
#print axioms every_selected_arity_has_isolated_dominant
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominanceNonvacuity
