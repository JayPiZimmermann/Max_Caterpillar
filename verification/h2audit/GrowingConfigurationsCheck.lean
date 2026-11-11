import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Configurations
import MaxCaterpillar.Frontier.RandomRestriction.UniformTuplesFiveTail

set_option autoImplicit false
noncomputable section
open BigOperators
open MaxCaterpillar.Frontier.RandomRestriction
open MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Configurations

example {k m : ℕ} (σ : FullPerm k m) : selectedLabels σ=GoodEvent.smallRankGaps σ k := rfl
example {k m : ℕ} (σ : FullPerm k m) : (selectedLabels σ).card=k := selectedLabels_card σ
example {k m : ℕ} (σ : FullPerm k m) (v : Fin (m+k)) :
    (∃ i,selectedEmbedding σ i=v) ↔ v∈selectedLabels σ := selectedEmbedding_range σ v
example {k m : ℕ} (σ : FullPerm k m) (v : Fin (m+k)) :
    (∃ j,baseTail σ j=v) ↔ v∉selectedLabels σ := baseTail_range σ v
example {k m : ℕ} (σ : FullPerm k m) :
    Finset.univ.image (baseTail σ)=(Finset.univ : Finset (Fin (m+k))) \ selectedLabels σ :=
  baseTail_image_complement_selectedLabels σ
example {k m : ℕ} (σ : FullPerm k m) :
    ((Finset.univ : Finset (Fin (m+k))) \ selectedLabels σ).card=m :=
  complement_selectedLabels_card σ
example {k m : ℕ} (G : SimpleGraph (Fin (m+k))) [DecidableRel G.Adj]
    (σ : FullPerm k m) :
    (G.edgeFinset.card:ℝ)-(k:ℝ)*(((m+k)-1:ℕ):ℝ)≤((G.comap (baseTail σ)).edgeFinset.card:ℝ) :=
  baseTail_edge_card_lower_bound_nat G σ
example {k m : ℕ} (G : SimpleGraph (Fin (m+k))) [DecidableRel G.Adj]
    (σ : FullPerm k m) (hn : 1≤m+k) :
    (G.edgeFinset.card:ℝ)-(k:ℝ)*((m:ℝ)+(k:ℝ)-1)≤((G.comap (baseTail σ)).edgeFinset.card:ℝ) :=
  baseTail_edge_card_lower_bound G σ hn
example {k m : ℕ} (f : Fin (m+k) → ℝ) :
    (∑ i,f i)=(∑ s : Fin k,f (selectedPosition k m s))+∑ t : Fin m,f (tailPosition k m t) :=
  sum_full_positions f
example {k m : ℕ} (σ : FullPerm k m) (τ : TailPerm m) :
    selectedLabels (effectivePermutation σ τ)=selectedLabels σ := selectedLabels_effective σ τ
example {k m : ℕ} (σ : FullPerm k m) (τ : TailPerm m) (j : Fin m) :
    (effectivePermutation σ τ).symm (tailPosition k m j)=σ.symm (tailPosition k m (τ j)) :=
  effectivePermutation_tail σ τ j
example {k m : ℕ} (B : Finset (LiteralConfiguration k m)) :
    (pullbackEvent B).card=Fintype.card (TailPerm m)*B.card := pullbackEvent_card B
example {k m : ℕ} (B : Finset (LiteralConfiguration k m)) :
    ((pullbackEvent B).card:ℝ)/(Fintype.card (Configuration k m):ℝ)=
      (B.card:ℝ)/(Fintype.card (LiteralConfiguration k m):ℝ) := pullbackEvent_fraction B
example {k m : ℕ} (σ : FullPerm k m) (ρ : RankPerm m) (f : TailPerm m → ℝ) :
    (∑ ω : FixedOuter σ ρ,f ω.val.2.1)/(Fintype.card (FixedOuter σ ρ):ℝ)=
      (∑ τ,f τ)/(Fintype.card (TailPerm m):ℝ) := average_fixedOuter σ ρ f

-- The arbitrary-arity coordinate convention agrees with the frozen five-arity one.
example (m : ℕ) : selectedPosition 5 m=GoodEvent.selectedPosition m := rfl
example (m : ℕ) : tailPosition 5 m=GoodEvent.tailPosition m := rfl
-- Empty selected and tail blocks are actual supported instances.
example (σ : FullPerm 0 3) : (selectedLabels σ).card=0 := selectedLabels_card σ
example (σ : FullPerm 3 0) :
    ((Finset.univ : Finset (Fin (0+3))) \ selectedLabels σ).card=0 :=
  complement_selectedLabels_card σ
example : Fintype.card (Configuration 0 0)=1 := by
  change Fintype.card (Equiv.Perm (Fin 0) × (Equiv.Perm (Fin 0) × Equiv.Perm (Fin 0)))=1
  rw [Fintype.card_prod,Fintype.card_prod]
  have h0 : Fintype.card (Equiv.Perm (Fin 0))=1 := by
    rw [Fintype.card_perm,Fintype.card_fin]
    rfl
  rw [h0]

#check @baseTail_edge_card_lower_bound
#check @pullbackEventEquiv
#check @fixedOuterEquiv
#print axioms selectedLabels_card
#print axioms selectedEmbedding_range
#print axioms baseTail_range
#print axioms selectedEmbedding_image
#print axioms baseTail_image_complement_selectedLabels
#print axioms complement_selectedLabels_card
#print axioms edge_card_le_baseTail_add
#print axioms baseTail_edge_card_lower_bound_nat
#print axioms baseTail_edge_card_lower_bound
#print axioms sum_full_positions
#print axioms tailLift_selected
#print axioms tailLift_tail
#print axioms effectiveFullEquiv
#print axioms selectedLabels_effective
#print axioms effectivePermutation_tail
#print axioms configurationEquiv
#print axioms pullbackEventEquiv
#print axioms pullbackEvent_card
#print axioms pullbackEvent_fraction
#print axioms fixedOuterEquiv
#print axioms average_fixedOuter
#print axioms sum_configuration_by_outer
