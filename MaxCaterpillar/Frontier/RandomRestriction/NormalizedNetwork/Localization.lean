import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.LocalFirst
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Outer
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.TiedMaximum
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Support
import MaxCaterpillar.Frontier.RandomRestriction.TiedPoint

/-! # Faithful localization at a generic tied coordinate set

The point is constructed, not assumed. Every original first and second index
is preserved, and a first row survives only with its exact original restricted
coefficients. A final outer normalization restores translation invariance.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
open BigOperators
variable {N m h₁ h₂ : ℕ}

noncomputable def localize (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) : NormalizedNetwork m h₁ h₂ :=
  freezeOuter (net.localFirst q e) (fun k => net.inner k q)

lemma localize_eval (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (x : Point m) :
    (net.localize q e).eval x = net.directionalEval q e x := by
  rw [localize,freezeOuter_eval,localFirst_output]
  simp only [localFirst_inner]
  rfl

@[simp] theorem localize_first_row (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (j : Fin h₁) :
    (net.localize q e).A j =
      if lin (net.A j) q = 0 then restrict e (net.A j) else 0 := rfl

theorem localize_feeding_original (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (j : Fin h₁)
    (hj : (net.localize q e).Feeding j) : net.Feeding j :=
  localFirst_feeding net q e j (freezeOuter_feeding_original _ _ j hj)

theorem localize_computes_max_of_tied [NeZero N] [NeZero m]
    (net : NormalizedNetwork N h₁ h₂) (hnet : ∀ x, net.eval x = Maximum N x)
    (e : Fin m ↪ Fin N) (q : Point N) (hq : ∀ a, q (e a) = 0)
    (hneg : ∀ i, i ∉ Finset.univ.image e → q i < 0) :
    ∀ x, (net.localize q e).eval x = Maximum m x := by
  intro x
  rw [localize_eval]
  exact directional_computes_max_of_tied net hnet e q hq hneg x

lemma rowSupport_subset_iff (a : Point N) (S : Finset (Fin N)) :
    rowSupport a ⊆ S ↔ ∀ i, i ∉ S → a i = 0 := by
  classical
  constructor
  · intro h i hi
    by_contra ha
    exact hi (h ((mem_rowSupport a i).mpr ha))
  · intro h i hi
    by_contra hn
    exact (mem_rowSupport a i).mp hi (h i hn)

/-- An actual generic tied point, with the exact zero-gate characterization. -/
theorem exists_generic_tied_point (net : NormalizedNetwork N h₁ h₂)
    (e : Fin m ↪ Fin N) :
    ∃ q : Point N, (∀ a, q (e a) = 0) ∧
      (∀ i, i ∉ Finset.univ.image e → q i < 0) ∧
      (∀ j, lin (net.A j) q = 0 ↔ rowSupport (net.A j) ⊆ Finset.univ.image e) := by
  classical
  obtain ⟨q,hq,hneg,hzero⟩ := exists_tied_point net.A (Finset.univ.image e)
  refine ⟨q,fun a => hq (e a) (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩),hneg,?_⟩
  intro j
  exact (hzero j).trans (rowSupport_subset_iff _ _).symm

/-- Coordinate-sum preservation is proved only for the retained full-support
rows, precisely the rows kept by a generic tied point. -/
lemma localize_first_zero_sum (net : NormalizedNetwork N h₁ h₂)
    (hfirst : ∀ j, ∑ i, net.A j i = 0) (e : Fin m ↪ Fin N) (q : Point N)
    (hzero : ∀ j, lin (net.A j) q = 0 ↔ rowSupport (net.A j) ⊆ Finset.univ.image e) :
    ∀ j, ∑ i, (net.localize q e).A j i = 0 := by
  classical
  intro j
  rw [localize_first_row]
  by_cases hj : lin (net.A j) q = 0
  · rw [if_pos hj,sum_restrict_of_subset e (net.A j) ((hzero j).mp hj)]
    exact hfirst j
  · rw [if_neg hj]
    simp

/-- The selected model has the same two finite index types as its source.
There is no normal-form hypothesis on second linear skips. -/
theorem exists_localized_normalized [NeZero N] [NeZero m]
    (net : NormalizedNetwork N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) (hfirst : ∀ j, ∑ i, net.A j i = 0)
    (e : Fin m ↪ Fin N) :
    ∃ model : NormalizedNetwork m h₁ h₂,
      (∀ x, model.eval x = Maximum m x) ∧ model.TranslationNormalized ∧
      (∀ j, model.A j = if rowSupport (net.A j) ⊆ Finset.univ.image e
        then restrict e (net.A j) else 0) ∧
      (∀ j, model.Feeding j → net.Feeding j) := by
  classical
  obtain ⟨q,hq,hneg,hzero⟩ := net.exists_generic_tied_point e
  let loc := net.localize q e
  have hloc : ∀ x, loc.eval x = Maximum m x :=
    net.localize_computes_max_of_tied hnet e q hq hneg
  have hsum : ∀ j, ∑ i, loc.A j i = 0 :=
    net.localize_first_zero_sum hfirst e q hzero
  refine ⟨normalizeOuter loc,normalizeOuter_computes_max loc hsum hloc,
    normalizeOuter_translation_normalized loc hsum hloc,?_,?_⟩
  · intro j
    rw [normalizeOuter_first_row]
    change (net.localize q e).A j = _
    rw [localize_first_row]
    by_cases hj : lin (net.A j) q = 0
    · rw [if_pos hj,if_pos ((hzero j).mp hj)]
    · rw [if_neg hj,if_neg (fun h => hj ((hzero j).mpr h))]
  · intro j hj
    exact net.localize_feeding_original q e j (normalizeOuter_feeding_original loc j hj)

#print axioms exists_localized_normalized
end MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
