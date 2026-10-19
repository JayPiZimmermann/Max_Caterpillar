import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Canonical.Table

/-!
# Exact finite support minimization

Starting from the assumption-free canonical coefficients, enumerate all
subsets of the normalized active dictionary which still compute `MAX` with
those coefficients.  Select a least-cardinality subset and break ties by the
finite index order.  The selected network is data depending only on `r`; the
caterpillar identity is used only to prove that the finite candidate set is
nonempty and that the network computes `MAX`.
-/

open BigOperators MeasureTheory

namespace MaxNN.Caterpillar.Corrections.Canonical

open MaxNN.Width

noncomputable section

local instance sparsePropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

set_option maxHeartbeats 800000

variable (r : ℕ)

abbrev ActiveIndex := Fin (canonicalActiveKeys r).card

def activeKey (i : ActiveIndex r) : RealKey (r + 1) :=
  (canonicalActiveKeys r).equivFin.symm i

theorem activeKey_injective : Function.Injective (activeKey r) := by
  intro i j hij
  apply (canonicalActiveKeys r).equivFin.symm.injective
  exact Subtype.ext hij

theorem activeKey_mem (i : ActiveIndex r) : activeKey r i ∈ canonicalActiveKeys r :=
  (canonicalActiveKeys r).equivFin.symm i |>.2

/-- A finite rank used only to give supports a deterministic tie-breaking
order. -/
def supportRank (S : Finset (ActiveIndex r)) :
    Fin ((Finset.univ.powerset : Finset (Finset (ActiveIndex r))).card) :=
  (Finset.univ.powerset).equivFin ⟨S, Finset.mem_powerset.mpr (Finset.subset_univ _)⟩

theorem supportRank_injective : Function.Injective (supportRank r) := by
  intro S T h
  have hs := (Finset.univ.powerset).equivFin.injective h
  exact congrArg Subtype.val hs

local instance supportLinearOrder : LinearOrder (Finset (ActiveIndex r)) :=
  LinearOrder.lift' (supportRank r) (supportRank_injective r)

def supportComputes (S : Finset (ActiveIndex r)) : Prop :=
  ∀ y : Fin (r + 1 + 1) → ℝ,
    MAX (r + 1 + 1) y =
      ∑ i in S, canonicalNormalizedCoeff r (activeKey r i) *
        realUnitY (activeKey r i) y +
      ∑ j, canonicalRemainderCoeff r j * feat (r + 1 + 1) y j

def supportCandidates : Finset (Finset (ActiveIndex r)) :=
  Finset.univ.powerset.filter (supportComputes r)

def supportSizes : Finset ℕ :=
  (supportCandidates r).image Finset.card

def minimumSupportSize : ℕ :=
  if h : (supportSizes r).Nonempty then (supportSizes r).min' h else 0

def optimalSupports : Finset (Finset (ActiveIndex r)) :=
  (supportCandidates r).filter fun S ↦ S.card = minimumSupportSize r

/-- A deterministic least-cardinality exact support, with the `Finset`
linear order used only to break ties.  It defaults to the empty set if the
correctness identity is unavailable. -/
def chosenSupport : Finset (ActiveIndex r) :=
  if h : (optimalSupports r).Nonempty then (optimalSupports r).min' h else ∅

def sparseKeys : Finset (RealKey (r + 1)) :=
  (chosenSupport r).image (activeKey r)

/-- The support-minimized network data, defined without proof parameters. -/
def sparseNetworkCandidate : ReLUNet (r + 1 + 1) 1 2 :=
  dictionaryNetwork (sparseKeys r) (canonicalNormalizedCoeff r)
    (canonicalRemainderCoeff r)

theorem univ_mem_supportCandidates (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) :
    (Finset.univ : Finset (ActiveIndex r)) ∈ supportCandidates r := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
  intro y
  have h := (canonicalCorrectionTable r hr hclass).computes_normalizedActive y
  rw [canonicalCorrectionTable_normalizedActiveKeys r hr hclass,
    canonicalCorrectionTable_normalizedCoeff r hr hclass,
    canonicalCorrectionTable_remainder r hr hclass] at h
  rw [← ParamidGeom.CoordAux.sum_equivFin_symm (canonicalActiveKeys r)
    (fun k ↦ canonicalNormalizedCoeff r k * realUnitY k y)] at h
  exact h

theorem supportCandidates_nonempty (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) : (supportCandidates r).Nonempty :=
  ⟨Finset.univ, univ_mem_supportCandidates r hr hclass⟩

theorem supportSizes_nonempty (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) : (supportSizes r).Nonempty := by
  obtain ⟨S, hS⟩ := supportCandidates_nonempty r hr hclass
  exact ⟨S.card, Finset.mem_image.mpr ⟨S, hS, rfl⟩⟩

theorem optimalSupports_nonempty (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) : (optimalSupports r).Nonempty := by
  have hsizes := supportSizes_nonempty r hr hclass
  have hmin : (supportSizes r).min' hsizes ∈ supportSizes r :=
    Finset.min'_mem _ _
  obtain ⟨S, hSc, hcard⟩ := Finset.mem_image.mp hmin
  refine ⟨S, Finset.mem_filter.mpr ⟨hSc, ?_⟩⟩
  unfold minimumSupportSize
  rw [dif_pos hsizes]
  exact hcard

theorem chosenSupport_mem_optimal (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) : chosenSupport r ∈ optimalSupports r := by
  unfold chosenSupport
  rw [dif_pos (optimalSupports_nonempty r hr hclass)]
  exact Finset.min'_mem _ _

theorem chosenSupport_mem_candidates (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) : chosenSupport r ∈ supportCandidates r :=
  (Finset.mem_filter.mp (chosenSupport_mem_optimal r hr hclass)).1

theorem chosenSupport_computes (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) : supportComputes r (chosenSupport r) :=
  (Finset.mem_filter.mp (chosenSupport_mem_candidates r hr hclass)).2

theorem chosenSupport_card_eq_minimum (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) :
    (chosenSupport r).card = minimumSupportSize r :=
  (Finset.mem_filter.mp (chosenSupport_mem_optimal r hr hclass)).2

/-- Minimality is only among supports using the fixed canonical coefficients
and fixed canonical feature remainder. -/
theorem chosenSupport_card_le_of_supportComputes (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) (S : Finset (ActiveIndex r))
    (hS : supportComputes r S) : (chosenSupport r).card ≤ S.card := by
  rw [chosenSupport_card_eq_minimum r hr hclass]
  have hcand : S ∈ supportCandidates r :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hS⟩
  have hsize : S.card ∈ supportSizes r := Finset.mem_image.mpr ⟨S, hcand, rfl⟩
  have hsizes := supportSizes_nonempty r hr hclass
  unfold minimumSupportSize
  rw [dif_pos hsizes]
  exact Finset.min'_le _ _ hsize

theorem sparseKeys_card : (sparseKeys r).card = (chosenSupport r).card := by
  apply Finset.card_image_iff.mpr
  intro i _ j _ hij
  exact activeKey_injective r hij

theorem chosenSupport_card_le :
    (chosenSupport r).card ≤ (canonicalActiveKeys r).card := by
  have hs : chosenSupport r ⊆ (Finset.univ : Finset (ActiveIndex r)) := by
    by_cases h : (optimalSupports r).Nonempty
    · rw [chosenSupport, dif_pos h]
      have hm := Finset.min'_mem (optimalSupports r) h
      have hc := (Finset.mem_filter.mp hm).1
      exact Finset.mem_powerset.mp (Finset.mem_filter.mp hc).1
    · rw [chosenSupport, dif_neg h]
      exact Finset.empty_subset _
  calc
    (chosenSupport r).card ≤ (Finset.univ : Finset (ActiveIndex r)).card :=
      Finset.card_le_of_subset hs
    _ = (canonicalActiveKeys r).card := by simp only [Finset.card_univ, Fintype.card_fin]

theorem sparseKeys_card_le :
    (sparseKeys r).card ≤ (canonicalActiveKeys r).card := by
  rw [sparseKeys_card]
  exact chosenSupport_card_le r

theorem sparseKeys_simplexDifference :
    ∀ k ∈ sparseKeys r, ∀ v ∈ k.2, IsSimplexDifference v := by
  intro k hk v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
  apply normalizedKeys_simplexDifference
  exact (Finset.mem_filter.mp (activeKey_mem r i)).1
  exact hv

theorem sum_sparseKeys (y : Fin (r + 1 + 1) → ℝ) :
    ∑ k in sparseKeys r, canonicalNormalizedCoeff r k * realUnitY k y =
      ∑ i in chosenSupport r, canonicalNormalizedCoeff r (activeKey r i) *
        realUnitY (activeKey r i) y := by
  unfold sparseKeys
  apply Finset.sum_image
  intro i _ j _ hij
  exact activeKey_injective r hij

theorem sparseNetworkCandidate_computes (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) :
    (sparseNetworkCandidate r).Computes (MAX (r + 1 + 1)) := by
  apply dictionaryNetwork_computes
  · exact sparseKeys_simplexDifference r
  · intro y
    have h := chosenSupport_computes r hr hclass y
    rw [sum_sparseKeys r y]
    exact h

theorem sparse_twoLayerWidth (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) :
    TwoLayerWidth (r + 1 + 1) (W (r + 1 + 1)) ((sparseKeys r).card + 2)
      (MAX (r + 1 + 1)) := by
  apply twoLayerWidth_of_mem_realUnitSpan (sparseKeys_simplexDifference r)
  refine ⟨canonicalNormalizedCoeff r,
    fun y ↦ ∑ j, canonicalRemainderCoeff r j * feat (r + 1 + 1) y j,
    ⟨canonicalRemainderCoeff r, fun _ ↦ rfl⟩, ?_⟩
  intro y
  have h := chosenSupport_computes r hr hclass y
  rw [sum_sparseKeys r y]
  exact h

end

end MaxNN.Caterpillar.Corrections.Canonical
