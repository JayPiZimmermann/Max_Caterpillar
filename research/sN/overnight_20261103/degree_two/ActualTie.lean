import research.sN.overnight_20261103.degree_two.GlobalComponents
import research.sN.overnight_20261103.degree_two.GraphRelabel
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Structural

/-! Every actual top tie needs an original second neuron whose induced signed
interaction graph has at most two components. The generic point, local model,
and signed edge correspondence are all derived from the original network. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.DegreeTwo
open Frontier Frontier.RandomRestriction NormalizedNetwork DominantGap Cartesian
attribute [local instance] Classical.propDecidable

variable {N m h₁ h₂ : ℕ}

/-- A nonzero localized output coefficient belongs to a surviving original
slot and equals its original coefficient. -/
theorem original_active_of_localized_active (net : NormalizedNetwork N h₁ h₂)
    (point : Point N) (f : Fin m ↪ Fin N) (r : Fin h₂)
    (hd : (net.localize point f).d r≠0) :
    net.inner r point=0 ∧ net.d r≠0 := by
  classical
  have hr : net.inner r point=0 := by
    by_contra hr
    apply hd
    change (if net.inner r point=0 then net.d r else 0)=0
    exact if_neg hr
  refine ⟨hr,?_⟩
  change (if net.inner r point=0 then net.d r else 0)≠0 at hd
  simpa only [hr,ite_true] using hd

/-- The conclusion concerns the graph induced by the given embedding on the
original signed aggregates. No matching obstruction or genericity premise is
required. The complement may be empty. -/
theorem exists_active_second_on_embedding [NeZero N] [NeZero m]
    (hm : 3≤m) (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized)
    (hbraid : ∀ j,(rowSupport (net.A j)).card≤2)
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
  have hs : ∀ j,(rowSupport ((net.localize point f).A j)).card≤2 := by
    apply GrowingMatching.localized_support_le_two net point f hfirst
    intro j hlarge _
    exact (Nat.not_succ_le_self 2) (le_trans hlarge (hbraid j))
  obtain ⟨r,hd,hc⟩ := exists_active_second_le_two_components hm
    (net.localize point f) hloc hs hlocmax
  obtain ⟨hr,hdo⟩ := original_active_of_localized_active net point f r hd
  refine ⟨r,hdo,?_⟩
  have hg := GrowingMatching.localized_braidGraph_eq_comap net hn point f hfirst hloc r hr
  rwa [←hg]

/-- Every selected set of at least three real input coordinates is covered by
an original active second neuron with at most two induced components,
including isolated selected vertices. No restriction on h₁ is imposed. -/
theorem exists_active_second_on_set [NeZero N]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hbraid : ∀ j,(rowSupport (net.A j)).card≤2)
    (hmax : ∀ x,net.eval x=Maximum N x)
    (S : Finset (Fin N)) (hS : 3≤S.card) :
    ∃ r : Fin h₂,net.d r≠0 ∧
      Nat.card ((braidInteractionGraph net hn r).induce (S : Set (Fin N))).ConnectedComponent≤2 := by
  letI : NeZero S.card := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hS)⟩
  obtain ⟨r,hd,hc⟩ := exists_active_second_on_embedding hS net hn hbraid hmax
    (selectedEmbedding S)
  exact ⟨r,hd,by rwa [selected_component_card] at hc⟩

#check @exists_active_second_on_embedding
#check @exists_active_second_on_set
#print axioms original_active_of_localized_active
#print axioms exists_active_second_on_embedding
#print axioms exists_active_second_on_set
end MaxCaterpillar.ExponentialPush.DegreeTwo
