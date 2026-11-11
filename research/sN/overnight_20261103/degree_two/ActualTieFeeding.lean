import research.sN.overnight_20261103.degree_two.ActualTie
import research.sN.overnight_20261103.degree_two.FeedingComponents

/-! Selected-set coverage with unrestricted output-only first rows.
Only rows with a nonzero coefficient into a second neuron must be braid rows.
The graph remains the literal signed aggregate of the original network. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.DegreeTwo
open Frontier Frontier.RandomRestriction NormalizedNetwork DominantGap Cartesian
attribute [local instance] Classical.propDecidable
variable {N m h₁ h₂ : ℕ}

theorem original_weight_ne_zero_of_localized (net : NormalizedNetwork N h₁ h₂)
    (point : Point N) (f : Fin m ↪ Fin N) (k : Fin h₂) (j : Fin h₁)
    (hw : (net.localize point f).W k j≠0) : net.W k j≠0 := by
  intro hz
  apply hw
  simp [localize,freezeOuter,localFirst,hz]

theorem exists_active_second_on_embedding_feeding [NeZero N] [NeZero m]
    (hm : 3≤m) (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized)
    (hbraid : ∀ k j,net.W k j≠0 → (rowSupport (net.A j)).card≤2)
    (hmax : ∀ x,net.eval x=Maximum N x) (f : Fin m ↪ Fin N) :
    ∃ r : Fin h₂,net.d r≠0 ∧
      Nat.card ((braidInteractionGraph net hn r).comap f).ConnectedComponent≤2 := by
  classical
  let S : Finset (Fin N) := Finset.univ.image f
  let e := complementEmbedding S
  have hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N))\Finset.univ.image f :=
    complementEmbedding_image S
  obtain ⟨B,_hB,hgeneric⟩ := exists_network_gap_threshold net e
  let p : RawConfig ((Finset.univ : Finset (Fin N))\S).card :=
    (Equiv.refl _,Equiv.refl _)
  have h := hgeneric B (le_refl B) p
  let point := actualGapPoint e p B
  have hfirst := embedded_first_zero_iff_support net f e p B hcomp h
  have hloc := embeddedLocalizedModel_translation_normalized net hn hmax f e p B hcomp h
  have hlocmax := embeddedLocalizedModel_computes_max net hmax f e p B hcomp h
  have hs : ∀ k j,(net.localize point f).W k j≠0 →
      (rowSupport ((net.localize point f).A j)).card≤2 := by
    intro k j hw
    have ho := original_weight_ne_zero_of_localized net point f k j hw
    rw [localize_first_row]
    by_cases hz : lin (net.A j) point=0
    · rw [if_pos hz,card_rowSupport_restrict f (net.A j) ((hfirst j).mp hz)]
      exact hbraid k j ho
    · rw [if_neg hz,rowSupport_zero,Finset.card_empty]
      exact Nat.zero_le _
  obtain ⟨r,hd,hc⟩ := Overnight.DegreeTwo.exists_active_second_two_components_feeding hm
    (net.localize point f) hloc hs hlocmax
  obtain ⟨hr,hdo⟩ := original_active_of_localized_active net point f r hd
  refine ⟨r,hdo,?_⟩
  have hg := GrowingMatching.localized_braidGraph_eq_comap net hn point f hfirst hloc r hr
  rwa [←hg]

/-- Any number of arbitrary output-only first neurons is permitted. Only
the original nonzero first-to-second coefficients impose the braid condition. -/
theorem exists_active_second_on_set_feeding [NeZero N]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hbraid : ∀ k j,net.W k j≠0 → (rowSupport (net.A j)).card≤2)
    (hmax : ∀ x,net.eval x=Maximum N x)
    (S : Finset (Fin N)) (hS : 3≤S.card) :
    ∃ r : Fin h₂,net.d r≠0 ∧
      Nat.card ((braidInteractionGraph net hn r).induce (S : Set (Fin N))).ConnectedComponent≤2 := by
  letI : NeZero S.card := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hS)⟩
  obtain ⟨r,hd,hc⟩ := exists_active_second_on_embedding_feeding hS net hn hbraid hmax
    (selectedEmbedding S)
  exact ⟨r,hd,by rwa [selected_component_card] at hc⟩

#check @exists_active_second_on_set_feeding
#print axioms original_weight_ne_zero_of_localized
#print axioms exists_active_second_on_embedding_feeding
#print axioms exists_active_second_on_set_feeding
end MaxCaterpillar.ExponentialPush.DegreeTwo
