import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Selected
import MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction.Deletion

/-! # Actual selected and tail labels for arbitrary selected arity

All labels belong to Fin(m+k). A genuine full permutation sends the selected
labels to the first k positions. Its inverse enumerates those labels and their
exact complement. No structural matching hypothesis or probability conclusion
is part of these definitions. Empty selected and tail blocks are allowed. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Configurations

abbrev FullPerm (k m : ℕ) := Equiv.Perm (Fin (m+k))
abbrev TailPerm (m : ℕ) := Equiv.Perm (Fin m)
abbrev RankPerm (m : ℕ) := Equiv.Perm (Fin m)
abbrev Configuration (k m : ℕ) := FullPerm k m × TailPerm m × RankPerm m
abbrev LiteralConfiguration (k m : ℕ) := FullPerm k m × RankPerm m

/-- The first k actual positions. -/
def selectedPosition (k m : ℕ) : Fin k ↪ Fin (m+k) :=
  GrowingMatching.prefixEmbedding (Nat.le_add_left k m)

/-- The remaining m actual positions, starting at offset k. -/
def tailPosition (k m : ℕ) : Fin m ↪ Fin (m+k) where
  toFun i := ⟨i.val+k,Nat.add_lt_add_right i.isLt k⟩
  inj' := by
    intro i j h
    exact Fin.ext (Nat.add_right_cancel (congrArg Fin.val h))

@[simp] lemma selectedPosition_val (k m : ℕ) (i : Fin k) :
    (selectedPosition k m i).val=i.val := rfl
@[simp] lemma tailPosition_val (k m : ℕ) (i : Fin m) :
    (tailPosition k m i).val=i.val+k := rfl

def fullPositionEquiv (k m : ℕ) : Fin k ⊕ Fin m ≃ Fin (m+k) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm k m))

@[simp] lemma fullPositionEquiv_selected (k m : ℕ) (i : Fin k) :
    fullPositionEquiv k m (Sum.inl i)=selectedPosition k m i := by
  apply Fin.ext
  rfl
@[simp] lemma fullPositionEquiv_tail (k m : ℕ) (i : Fin m) :
    fullPositionEquiv k m (Sum.inr i)=tailPosition k m i := by
  apply Fin.ext
  exact Nat.add_comm k i.val

lemma full_position_cases {k m : ℕ} (v : Fin (m+k)) :
    (∃ i : Fin k,v=selectedPosition k m i) ∨ (∃ j : Fin m,v=tailPosition k m j) := by
  obtain ⟨p,hp⟩ := (fullPositionEquiv k m).surjective v
  cases p with
  | inl i => exact Or.inl ⟨i,((fullPositionEquiv_selected k m i).symm.trans hp).symm⟩
  | inr j => exact Or.inr ⟨j,((fullPositionEquiv_tail k m j).symm.trans hp).symm⟩

variable {k m : ℕ}

/-- The literal frozen prefix-selection event set. -/
noncomputable def selectedLabels (σ : FullPerm k m) : Finset (Fin (m+k)) :=
  GoodEvent.smallRankGaps σ k

lemma selectedLabels_card (σ : FullPerm k m) : (selectedLabels σ).card=k :=
  GoodEvent.card_smallRankGaps (Nat.le_add_left k m) σ

def selectedEmbedding (σ : FullPerm k m) : Fin k ↪ Fin (m+k) where
  toFun i := σ.symm (selectedPosition k m i)
  inj' := σ.symm.injective.comp (selectedPosition k m).injective

def baseTail (σ : FullPerm k m) : Fin m ↪ Fin (m+k) where
  toFun j := σ.symm (tailPosition k m j)
  inj' := σ.symm.injective.comp (tailPosition k m).injective

lemma selectedEmbedding_range (σ : FullPerm k m) (v : Fin (m+k)) :
    (∃ i,selectedEmbedding σ i=v) ↔ v ∈ selectedLabels σ := by
  constructor
  · rintro ⟨i,rfl⟩
    apply (GoodEvent.mem_smallRankGaps σ _).mpr
    change (σ (σ.symm (selectedPosition k m i))).val<k
    rw [Equiv.apply_symm_apply]
    exact i.isLt
  · intro hv
    have h := (GoodEvent.mem_smallRankGaps σ v).mp hv
    let i : Fin k := ⟨(σ v).val,h⟩
    refine ⟨i,?_⟩
    change σ.symm (selectedPosition k m i)=v
    apply σ.injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    rfl

lemma baseTail_range (σ : FullPerm k m) (v : Fin (m+k)) :
    (∃ j,baseTail σ j=v) ↔ v ∉ selectedLabels σ := by
  constructor
  · rintro ⟨j,rfl⟩ hv
    have h := (GoodEvent.mem_smallRankGaps σ _).mp hv
    change (σ (σ.symm (tailPosition k m j))).val<k at h
    rw [Equiv.apply_symm_apply] at h
    exact (Nat.not_lt.mpr (Nat.le_add_left k j.val)) h
  · intro hv
    rcases full_position_cases (σ v) with ⟨i,hi⟩ | ⟨j,hj⟩
    · apply False.elim
      apply hv
      apply (GoodEvent.mem_smallRankGaps σ v).mpr
      rw [hi]
      exact i.isLt
    · refine ⟨j,?_⟩
      change σ.symm (tailPosition k m j)=v
      rw [←hj,Equiv.symm_apply_apply]

lemma selectedEmbedding_image (σ : FullPerm k m) :
    Finset.univ.image (selectedEmbedding σ)=selectedLabels σ := by
  classical
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and,selectedEmbedding_range]

lemma baseTail_image_complement_selectedLabels (σ : FullPerm k m) :
    Finset.univ.image (baseTail σ)=(Finset.univ : Finset (Fin (m+k))) \ selectedLabels σ := by
  classical
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_sdiff,baseTail_range]

lemma complement_selectedLabels_card (σ : FullPerm k m) :
    ((Finset.univ : Finset (Fin (m+k))) \ selectedLabels σ).card=m := by
  classical
  rw [←baseTail_image_complement_selectedLabels,
    Finset.card_image_of_injective _ (baseTail σ).injective,Finset.card_univ,Fintype.card_fin]

/-- Actual deletion of all k selected labels, retaining every other edge. -/
lemma edge_card_le_baseTail_add (G : SimpleGraph (Fin (m+k))) [DecidableRel G.Adj]
    (σ : FullPerm k m) :
    G.edgeFinset.card≤(G.comap (baseTail σ)).edgeFinset.card+k*((m+k)-1) := by
  simpa only [selectedLabels_card] using GraphRestriction.edge_card_le_comap_add
    G (selectedLabels σ) (baseTail σ) (baseTail_range σ)

lemma baseTail_edge_card_lower_bound_nat (G : SimpleGraph (Fin (m+k))) [DecidableRel G.Adj]
    (σ : FullPerm k m) :
    (G.edgeFinset.card:ℝ)-(k:ℝ)*(((m+k)-1:ℕ):ℝ)≤((G.comap (baseTail σ)).edgeFinset.card:ℝ) := by
  have h : (G.edgeFinset.card:ℝ)≤((G.comap (baseTail σ)).edgeFinset.card:ℝ)+
      (k:ℝ)*(((m+k)-1:ℕ):ℝ) := by
    exact_mod_cast edge_card_le_baseTail_add G σ
  linarith only [h]

/-- Real-subtraction form of the actual deletion loss, for a nonempty label set. -/
lemma baseTail_edge_card_lower_bound (G : SimpleGraph (Fin (m+k))) [DecidableRel G.Adj]
    (σ : FullPerm k m) (hn : 1≤m+k) :
    (G.edgeFinset.card:ℝ)-(k:ℝ)*((m:ℝ)+(k:ℝ)-1)≤
      ((G.comap (baseTail σ)).edgeFinset.card:ℝ) := by
  have hcast : (((m+k)-1:ℕ):ℝ)=(m:ℝ)+(k:ℝ)-1 := by
    rw [Nat.cast_sub hn,Nat.cast_add,Nat.cast_one]
  simpa only [hcast] using baseTail_edge_card_lower_bound_nat G σ

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Configurations
