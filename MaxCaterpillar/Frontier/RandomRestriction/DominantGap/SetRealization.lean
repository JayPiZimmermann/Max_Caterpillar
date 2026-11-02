import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.NetworkRealization
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.SetRestriction
import Mathlib.Data.Fintype.Powerset

/-! # Actual dominant-gap survival on a selected coordinate set

The tail is the actual complement of S. A common scale can be chosen for every
selected set, every raw permutation and every possible activation pattern.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.DominantGap
open BigOperators Cartesian

noncomputable def complementEmbedding {N : ℕ} (S : Finset (Fin N)) :
    Fin ((Finset.univ : Finset (Fin N)) \ S).card ↪ Fin N :=
  NormalizedNetwork.selectedEmbedding (Finset.univ \ S)

lemma complementEmbedding_image {N : ℕ} (S : Finset (Fin N)) :
    Finset.univ.image (complementEmbedding S)=Finset.univ \ S :=
  NormalizedNetwork.selectedEmbedding_image _

lemma complement_card {N : ℕ} (S : Finset (Fin N)) :
    ((Finset.univ : Finset (Fin N)) \ S).card=N-S.card := by
  rw [Finset.card_sdiff (Finset.subset_univ _)]
  simp only [Finset.card_univ,Fintype.card_fin]

lemma restrict_complement_eq_zero_iff {N : ℕ} (S : Finset (Fin N)) (w : Point N) :
    NormalizedNetwork.restrict (complementEmbedding S) w=0 ↔
      NormalizedNetwork.rowSupport w⊆S := by
  classical
  constructor
  · intro h i hi
    by_contra hnot
    have himage : i∈Finset.univ.image (complementEmbedding S) := by
      rw [complementEmbedding_image]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hnot⟩
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp himage
    have hw := congrFun h a
    change w (complementEmbedding S a)=0 at hw
    rw [ha] at hw
    exact (NormalizedNetwork.mem_rowSupport w i).mp hi hw
  · intro h
    funext a
    change w (complementEmbedding S a)=0
    by_contra hw
    have hS := h ((NormalizedNetwork.mem_rowSupport w _).mpr hw)
    have himage : complementEmbedding S a∈Finset.univ.image (complementEmbedding S) :=
      Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
    rw [complementEmbedding_image] at himage
    exact (Finset.mem_sdiff.mp himage).2 hS

noncomputable def setGapPoint {N : ℕ} (S : Finset (Fin N))
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ) : Point N :=
  actualGapPoint (complementEmbedding S) p T

/-- Explicit actual-coordinate version of the generic survival conclusion. -/
structure GenericSetNetworkPoint {N h₁ h₂ : ℕ} (net : NormalizedNetwork N h₁ h₂)
    (S : Finset (Fin N)) (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card)
    (T : ℝ) : Prop where
  selected_zero : ∀ i∈S,setGapPoint S p T i=0
  outside_negative : ∀ i∉S,setGapPoint S p T i<0
  first_zero_iff_support : ∀ j,lin (net.A j) (setGapPoint S p T)=0 ↔
    NormalizedNetwork.rowSupport (net.A j)⊆S
  second_zero_iff_support : ∀ k,net.inner k (setGapPoint S p T)=0 ↔
    NormalizedNetwork.rowSupport (actualEffectiveRow net k (setGapPoint S p T))⊆S
  underlying_generic : GenericNetworkPoint net (complementEmbedding S) p T

lemma genericSetNetworkPoint_of_generic {N h₁ h₂ : ℕ}
    (net : NormalizedNetwork N h₁ h₂) (S : Finset (Fin N))
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericNetworkPoint net (complementEmbedding S) p T) :
    GenericSetNetworkPoint net S p T := by
  classical
  refine ⟨?_,?_,?_,?_,h⟩
  · intro i hi
    apply h.tied_block i
    rw [complementEmbedding_image]
    exact fun hmem => (Finset.mem_sdiff.mp hmem).2 hi
  · intro i hi
    have himage : i∈Finset.univ.image (complementEmbedding S) := by
      rw [complementEmbedding_image]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi⟩
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp himage
    have hn := h.negative_tail a
    rwa [ha] at hn
  · intro j
    exact (h.first_zero_iff j).trans (restrict_complement_eq_zero_iff S (net.A j))
  · intro k
    exact (h.second_zero_iff k).trans
      (restrict_complement_eq_zero_iff S (actualEffectiveRow net k (setGapPoint S p T)))

/-- No generic-point or survival-equivalence assumption is required: the scale
is produced from the arbitrary original finite real coefficient arrays. -/
theorem exists_set_network_gap_threshold {N h₁ h₂ : ℕ}
    (net : NormalizedNetwork N h₁ h₂) (S : Finset (Fin N)) :
    ∃ B : ℝ,2≤B ∧ ∀ T : ℝ,B≤T→
      ∀ p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card,
        GenericSetNetworkPoint net S p T := by
  obtain ⟨B,hB,h⟩ := exists_network_gap_threshold net (complementEmbedding S)
  exact ⟨B,hB,fun T hT p => genericSetNetworkPoint_of_generic net S p T (h T hT p)⟩

/-- One scale works for the complete finite experiment: every coordinate set,
every tau/rho, every original neuron and every possible active first pattern. -/
theorem exists_uniform_set_network_gap_threshold {N h₁ h₂ : ℕ}
    (net : NormalizedNetwork N h₁ h₂) :
    ∃ B : ℝ,2≤B ∧ ∀ S : Finset (Fin N),∀ T : ℝ,B≤T→
      ∀ p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card,
        GenericSetNetworkPoint net S p T := by
  classical
  choose bound hbound hstable using fun S : Finset (Fin N) => exists_set_network_gap_threshold net S
  let B : ℝ := 2+∑ S : Finset (Fin N),bound S
  have hnonneg : ∀ S,0≤bound S := fun S => le_trans (by norm_num) (hbound S)
  have hsum : 0≤∑ S : Finset (Fin N),bound S := Finset.sum_nonneg (fun S _ => hnonneg S)
  refine ⟨B,by dsimp only [B]; linarith only [hsum],?_⟩
  intro S T hT p
  apply hstable S T
  have hS : bound S≤∑ S : Finset (Fin N),bound S :=
    Finset.single_le_sum (fun R _ => hnonneg R) (Finset.mem_univ S)
  dsimp only [B] at hT
  linarith only [hS,hT]
end MaxCaterpillar.Frontier.RandomRestriction.DominantGap
