import MaxCaterpillar.CountCubic.Word

/-!
# Caterpillar structure of the normalized correction keys

Every key of `normalizedKeys r` is `wordFaceKey w τ` for a decorated word
`w` and a face state `τ` (`exists_word_of_mem_normalizedKeys`).  In full
coordinates `y_0, …, y_{r+1}` (`N = r + 2`):

* `keyHead_wordFaceKey`: the head is
  `h = e_last - e_apex + Σ_{linear edges} (e_par - e_child)
     + Σ_{hinge edges, child < par} (e_par - e_child)`;
* `hasPair_wordFaceKey_iff`: `σ(y_a - y_b)` is a label iff some hinge edge has
  lower end `a` and upper end `b`;
* `kappa_wordFaceKey` (the κ formula):
  `κ_o = #{active edges with parent o} + [o = last] - [o = apex]
         - #{linear edges with child o}`, the last count being `≤ 1`
  (`card_linear_child_le_one`), i.e. `[parent edge of o is linear]`.

Consequences: `κ ≥ -1`, `κ_apex = -1`, the apex lies in no pair, pendant
leaves have `κ ∈ {0, -1}` (`-1` iff the parent edge is linear), `|M|` is the
number of hinge edges and `|M| ≤ N - 2`, `Σ κ = |M|`, and every label has at
most two hinge neighbours among the spine labels.
-/

open BigOperators

namespace MaxCaterpillar.CountCubic

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections MaxNN.ParamidGeom
  MaxNN.ParamidChain

variable {r : ℕ}

theorem wordGamma_eq (w : WordIndex r) :
    wordGamma w = toR (vtx (lastV w)) - toR (vtx (apexV w)) := rfl

/-- Sums over filtered word labels are sums over tree edges. -/
theorem sum_wordLabels_filter (w : WordIndex r) (P : (Fin (r + 1) → ℝ) → Prop)
    [DecidablePred P] (F : (Fin (r + 1) → ℝ) → ℝ) :
    ∑ v in (wordLabels w).filter P, F v =
      ∑ j, if P (edgeVecs (wordBase w) w.2.1 j) then F (edgeVecs (wordBase w) w.2.1 j) else 0 := by
  classical
  unfold wordLabels
  rw [Finset.image_filter, Finset.sum_image (fun x _ y _ h => edgeVecs_word_injective w h),
    Finset.sum_filter]

theorem edgeState_eq (w : WordIndex r) (τ : wordLabels w → Fin 3) (j : Fin r) :
    keyExt (wordLabels w) τ (edgeVecs (wordBase w) w.2.1 j) = edgeState w τ j := rfl

/-- The head of a normalized word face key, coordinate by coordinate. -/
theorem keyHead_wordFaceKey (w : WordIndex r) (τ : wordLabels w → Fin 3) (o : Fin (r + 1 + 1)) :
    keyHead (wordFaceKey w τ) o =
      (if lastV w = o then 1 else 0) - (if apexV w = o then 1 else 0) +
      (∑ j, if edgeState w τ j = 1 then
          (if parV w j = o then 1 else 0) - (if childV w j = o then 1 else 0) else 0) +
      (∑ j, if edgeState w τ j = 2 ∧ childV w j < parV w j then
          (if parV w j = o then 1 else 0) - (if childV w j = o then 1 else 0) else 0) := by
  classical
  unfold keyHead wordFaceKey normalizedKey faceKey
  simp only [fullVec_add, fullVec_sum, Pi.add_apply, Finset.sum_apply]
  rw [Finset.filter_filter, sum_wordLabels_filter, sum_wordLabels_filter, wordGamma_eq,
    fullVec_vtx_sub_apply]
  have e1 : (∑ j, if keyExt (wordLabels w) τ (edgeVecs (wordBase w) w.2.1 j) = 1 then
        fullVec (edgeVecs (wordBase w) w.2.1 j) o else 0) =
      ∑ j, if edgeState w τ j = 1 then
        (if parV w j = o then 1 else 0) - (if childV w j = o then 1 else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [edgeState_eq, edgeVecs_eq, fullVec_vtx_sub_apply]
  have e2 : (∑ j, if keyExt (wordLabels w) τ (edgeVecs (wordBase w) w.2.1 j) = 2 ∧
          reverseLabel (edgeVecs (wordBase w) w.2.1 j) then
        fullVec (edgeVecs (wordBase w) w.2.1 j) o else 0) =
      ∑ j, if edgeState w τ j = 2 ∧ childV w j < parV w j then
        (if parV w j = o then 1 else 0) - (if childV w j = o then 1 else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [edgeState_eq, edgeVecs_eq, fullVec_vtx_sub_apply]
    by_cases h : edgeState w τ j = 2 ∧ childV w j < parV w j
    · rw [if_pos h, if_pos ⟨h.1, (reverseLabel_edge_iff w j).mpr h.2⟩]
    · rw [if_neg h, if_neg]
      rintro ⟨h1, h2⟩
      exact h ⟨h1, (reverseLabel_edge_iff w j).mp h2⟩
  rw [e1, e2]

/-- The pairs of a normalized word face key are exactly the hinge edges,
written with their lower end first. -/
theorem hasPair_wordFaceKey_iff (w : WordIndex r) (τ : wordLabels w → Fin 3)
    (a b : Fin (r + 1 + 1)) :
    HasPair (wordFaceKey w τ) a b ↔
      ∃ j, edgeState w τ j = 2 ∧ lowV w j = a ∧ highV w j = b := by
  classical
  unfold HasPair wordFaceKey normalizedKey faceKey
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨v, ⟨hv, hst⟩, he⟩
    unfold wordLabels at hv
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
    rw [orientedLabel_edge] at he
    obtain ⟨h1, h2⟩ := simplex_difference_endpoints (ne_of_lt (lowV_lt_highV w j)) he
    exact ⟨j, hst, h1, h2⟩
  · rintro ⟨j, hst, rfl, rfl⟩
    refine ⟨edgeVecs (wordBase w) w.2.1 j,
      ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, hst⟩, ?_⟩
    rw [orientedLabel_edge]

/-- `N⁺(o)` is in bijection with the hinge edges whose lower end is `o`. -/
theorem card_upNbrs_wordFaceKey (w : WordIndex r) (τ : wordLabels w → Fin 3)
    (o : Fin (r + 1 + 1)) :
    (upNbrs (wordFaceKey w τ) o).card =
      (Finset.univ.filter fun j => edgeState w τ j = 2 ∧ lowV w j = o).card := by
  classical
  have he : upNbrs (wordFaceKey w τ) o =
      (Finset.univ.filter fun j => edgeState w τ j = 2 ∧ lowV w j = o).image (highV w) := by
    ext x
    rw [mem_upNbrs, hasPair_wordFaceKey_iff, Finset.mem_image]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, j, hst, hl, hh⟩
      exact ⟨j, ⟨hst, hl⟩, hh⟩
    · rintro ⟨j, ⟨hst, hl⟩, hh⟩
      refine ⟨?_, j, hst, hl, hh⟩
      rw [← hl, ← hh]
      exact lowV_lt_highV w j
  rw [he, Finset.card_image_of_injOn]
  intro j hj j' hj' hh
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj hj'
  exact edge_eq_of_low_high w (hj.2.trans hj'.2.symm) hh

/-- A label is the child of at most one tree edge. -/
theorem card_linear_child_le_one (w : WordIndex r) (τ : wordLabels w → Fin 3)
    (o : Fin (r + 1 + 1)) :
    (Finset.univ.filter fun j => edgeState w τ j = 1 ∧ childV w j = o).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro j hj j' hj'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
  exact childV_injective w (hj.2.trans hj'.2.symm)

/-- The per-edge bookkeeping behind the κ formula: an edge with parent `p`,
child `c` and state `s` contributes the same to `h_o + |N⁺(o)|` as to
`[s active, p = o] - [s linear, c = o]`. -/
theorem kappa_local {n : ℕ} (s : Fin 3) (p c o : Fin n) (hpc : p ≠ c) :
    ((if s = 1 then (if p = o then (1 : ℝ) else 0) - (if c = o then 1 else 0) else 0) +
        (if s = 2 ∧ c < p then (if p = o then (1 : ℝ) else 0) - (if c = o then 1 else 0) else 0) +
        (if s = 2 ∧ (if c < p then c else p) = o then (1 : ℝ) else 0)) =
      (if s ≠ 0 ∧ p = o then (1 : ℝ) else 0) - (if s = 1 ∧ c = o then (1 : ℝ) else 0) := by
  have hs : s = 0 ∨ s = 1 ∨ s = 2 := by fin_cases s <;> decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  rcases hs with rfl | rfl | rfl <;> by_cases hcp : c < p <;>
    (try simp only [hcp, if_true, if_false, h01, h02, h12, h01.symm, h02.symm, h12.symm,
      Ne.def, not_false_eq_true, true_and, false_and, and_true, and_false, not_true,
      eq_self_iff_true]) <;>
    by_cases hp : p = o <;> by_cases hc : c = o <;>
    (try simp only [hp, hc, if_true, if_false, eq_self_iff_true]) <;>
    first | (exfalso; exact hpc (hp.trans hc.symm)) | norm_num

/-- **The κ formula.** For the normalized key of `w` with face state `τ`,
`κ_o = #active children + [o = last] - [o = apex] - [parent edge linear]`. -/
theorem kappa_wordFaceKey (w : WordIndex r) (τ : wordLabels w → Fin 3) (o : Fin (r + 1 + 1)) :
    kappa (wordFaceKey w τ) o =
      ((Finset.univ.filter fun j => edgeState w τ j ≠ 0 ∧ parV w j = o).card : ℝ) +
      (if lastV w = o then 1 else 0) - (if apexV w = o then 1 else 0) -
      ((Finset.univ.filter fun j => edgeState w τ j = 1 ∧ childV w j = o).card : ℝ) := by
  classical
  unfold kappa
  rw [keyHead_wordFaceKey, card_upNbrs_wordFaceKey]
  simp only [← Finset.sum_boole]
  have hj : ∀ j : Fin r,
      ((if edgeState w τ j = 1 then
          (if parV w j = o then (1 : ℝ) else 0) - (if childV w j = o then 1 else 0) else 0) +
        (if edgeState w τ j = 2 ∧ childV w j < parV w j then
          (if parV w j = o then (1 : ℝ) else 0) - (if childV w j = o then 1 else 0) else 0) +
        (if edgeState w τ j = 2 ∧ lowV w j = o then (1 : ℝ) else 0)) =
      (if edgeState w τ j ≠ 0 ∧ parV w j = o then (1 : ℝ) else 0) -
        (if edgeState w τ j = 1 ∧ childV w j = o then (1 : ℝ) else 0) := by
    intro j
    have hpc := parV_ne_childV w j
    have hlow : lowV w j = if childV w j < parV w j then childV w j else parV w j := by
      unfold lowV
      split_ifs with h
      · exact min_eq_right h.le
      · exact min_eq_left (not_lt.mp h)
    rw [hlow]
    exact kappa_local _ _ _ o hpc
  have hsum := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hj j)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  linarith

/-- The parent edge of a label is linear for at most one edge, so the last
count in the κ formula is the indicator of a linear parent edge. -/
theorem card_linear_child_eq (w : WordIndex r) (τ : wordLabels w → Fin 3) (j : Fin r) :
    (Finset.univ.filter fun j' => edgeState w τ j' = 1 ∧ childV w j' = childV w j).card =
      if edgeState w τ j = 1 then 1 else 0 := by
  classical
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨j, ?_⟩
    ext j'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, he⟩
      exact childV_injective w he
    · rintro rfl
      exact ⟨h, rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro j' - ⟨h1, he⟩
    rw [childV_injective w he] at h1
    exact h h1

/-- `κ ≥ -1` everywhere. -/
theorem neg_one_le_kappa_wordFaceKey (w : WordIndex r) (τ : wordLabels w → Fin 3)
    (o : Fin (r + 1 + 1)) : -1 ≤ kappa (wordFaceKey w τ) o := by
  classical
  rw [kappa_wordFaceKey]
  have h0 : (0 : ℝ) ≤ ((Finset.univ.filter fun j => edgeState w τ j ≠ 0 ∧ parV w j = o).card : ℝ) :=
    Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ if lastV w = o then 1 else 0 := by split_ifs <;> norm_num
  have h2 : ((Finset.univ.filter fun j => edgeState w τ j = 1 ∧ childV w j = o).card : ℝ) ≤ 1 := by
    exact_mod_cast card_linear_child_le_one w τ o
  by_cases ha : apexV w = o
  · rw [if_pos ha]
    have hz : (Finset.univ.filter fun j => edgeState w τ j = 1 ∧ childV w j = o) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro j - ⟨-, he⟩
      exact apexV_ne_childV w j (ha.trans he.symm)
    rw [hz, Finset.card_empty, Nat.cast_zero]
    linarith
  · rw [if_neg ha]
    linarith

/-- `κ_apex = -1`. -/
theorem kappa_apex_wordFaceKey (w : WordIndex r) (τ : wordLabels w → Fin 3) :
    kappa (wordFaceKey w τ) (apexV w) = -1 := by
  classical
  rw [kappa_wordFaceKey, if_neg (apexV_ne_lastV w).symm, if_pos rfl]
  have hz1 : (Finset.univ.filter fun j => edgeState w τ j ≠ 0 ∧ parV w j = apexV w) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro j - ⟨-, he⟩
    exact apexV_ne_parV w j he.symm
  have hz2 : (Finset.univ.filter fun j => edgeState w τ j = 1 ∧ childV w j = apexV w) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro j - ⟨-, he⟩
    exact apexV_ne_childV w j he.symm
  rw [hz1, hz2]
  norm_num

/-- The apex lies in no pair of `M`. -/
theorem not_hasPair_apex_wordFaceKey (w : WordIndex r) (τ : wordLabels w → Fin 3)
    (x : Fin (r + 1 + 1)) :
    ¬ HasPair (wordFaceKey w τ) (apexV w) x ∧ ¬ HasPair (wordFaceKey w τ) x (apexV w) := by
  have hend : ∀ j, lowV w j ≠ apexV w ∧ highV w j ≠ apexV w := by
    intro j
    unfold lowV highV
    constructor
    · rcases min_choice (parV w j) (childV w j) with h | h <;> rw [h]
      · exact (apexV_ne_parV w j).symm
      · exact (apexV_ne_childV w j).symm
    · rcases max_choice (parV w j) (childV w j) with h | h <;> rw [h]
      · exact (apexV_ne_parV w j).symm
      · exact (apexV_ne_childV w j).symm
  constructor
  · rw [hasPair_wordFaceKey_iff]
    rintro ⟨j, -, h, -⟩
    exact (hend j).1 h
  · rw [hasPair_wordFaceKey_iff]
    rintro ⟨j, -, -, h⟩
    exact (hend j).2 h

/-- A pendant (non-spine) position has no children and is not the last spine
vertex, so its κ is `0`, or `-1` exactly when its parent edge is linear. -/
theorem kappa_pendant_wordFaceKey (w : WordIndex r) (τ : wordLabels w → Fin 3) (j : Fin r)
    (hj : j.succ ∉ w.2.1) :
    kappa (wordFaceKey w τ) (childV w j) = if edgeState w τ j = 1 then -1 else 0 := by
  classical
  rw [kappa_wordFaceKey, card_linear_child_eq]
  have hz : (Finset.univ.filter fun j' => edgeState w τ j' ≠ 0 ∧ parV w j' = childV w j) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro j' - ⟨-, he⟩
    exact parent_ne_pendant w.2.1 j hj j'.succ (baseV_injective w he)
  have hl : lastV w ≠ childV w j := fun he =>
    lastHead_ne_pendant w.2.1 j hj (baseV_injective w he)
  rw [hz, if_neg hl, if_neg (apexV_ne_childV w j)]
  split_ifs <;> norm_num

theorem kappa_pendant_mem (w : WordIndex r) (τ : wordLabels w → Fin 3) (j : Fin r)
    (hj : j.succ ∉ w.2.1) :
    kappa (wordFaceKey w τ) (childV w j) = 0 ∨ kappa (wordFaceKey w τ) (childV w j) = -1 := by
  rw [kappa_pendant_wordFaceKey w τ j hj]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- `M` is in bijection with the hinge edges. -/
theorem card_pairSet_wordFaceKey (w : WordIndex r) (τ : wordLabels w → Fin 3) :
    (pairSet (wordFaceKey w τ)).card =
      (Finset.univ.filter fun j => edgeState w τ j = 2).card := by
  classical
  have he : pairSet (wordFaceKey w τ) =
      (Finset.univ.filter fun j => edgeState w τ j = 2).image (fun j => (lowV w j, highV w j)) := by
    ext ⟨a, b⟩
    rw [mem_pairSet, Finset.mem_image]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    rw [hasPair_wordFaceKey_iff]
    constructor
    · rintro ⟨-, j, hst, hl, hh⟩
      exact ⟨j, hst, hl, hh⟩
    · rintro ⟨j, hst, hl, hh⟩
      refine ⟨?_, j, hst, hl, hh⟩
      change a < b
      rw [← hl, ← hh]
      exact lowV_lt_highV w j
  rw [he, Finset.card_image_of_injOn]
  intro j _ j' _ h
  simp only [Prod.mk.injEq] at h
  exact edge_eq_of_low_high w h.1 h.2

/-- `|M| ≤ N - 2`. -/
theorem card_pairSet_wordFaceKey_le (w : WordIndex r) (τ : wordLabels w → Fin 3) :
    (pairSet (wordFaceKey w τ)).card ≤ r := by
  rw [card_pairSet_wordFaceKey]
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])

/-- `Σ_o κ_o` is the number of hinge edges. -/
theorem sum_kappa_wordFaceKey (w : WordIndex r) (τ : wordLabels w → Fin 3) :
    ∑ o, kappa (wordFaceKey w τ) o =
      ((Finset.univ.filter fun j => edgeState w τ j = 2).card : ℝ) := by
  rw [sum_kappa, card_pairSet_wordFaceKey]

/-- Hinge neighbours: `x` is joined to `o` by a pair of `M`. -/
def HingeNbr (k : RealKey (r + 1)) (o x : Fin (r + 1 + 1)) : Prop :=
  HasPair k o x ∨ HasPair k x o

theorem hingeNbr_wordFaceKey (w : WordIndex r) (τ : wordLabels w → Fin 3)
    {o x : Fin (r + 1 + 1)} (h : HingeNbr (wordFaceKey w τ) o x) :
    ∃ j, edgeState w τ j = 2 ∧
      ((parV w j = o ∧ childV w j = x) ∨ (childV w j = o ∧ parV w j = x)) := by
  have hcase : ∀ j, (lowV w j = parV w j ∧ highV w j = childV w j) ∨
      (lowV w j = childV w j ∧ highV w j = parV w j) := by
    intro j
    unfold lowV highV
    rcases le_total (parV w j) (childV w j) with h | h
    · exact Or.inl ⟨min_eq_left h, max_eq_right h⟩
    · exact Or.inr ⟨min_eq_right h, max_eq_left h⟩
  rcases h with h | h <;> rw [hasPair_wordFaceKey_iff] at h <;>
    obtain ⟨j, hst, hl, hh⟩ := h <;> refine ⟨j, hst, ?_⟩ <;>
    rcases hcase j with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1 ▸ hl, h2 ▸ hh⟩
  · exact Or.inr ⟨h1 ▸ hl, h2 ▸ hh⟩
  · exact Or.inr ⟨h2 ▸ hh, h1 ▸ hl⟩
  · exact Or.inl ⟨h2 ▸ hh, h1 ▸ hl⟩

open Classical in
/-- Every label has at most two hinge neighbours that are spine labels:
its parent, and the next spine vertex when it is itself a spine vertex. -/
theorem card_spine_hingeNbr_le_two (w : WordIndex r) (τ : wordLabels w → Fin 3)
    (o : Fin (r + 1 + 1)) :
    ((spineV w).filter fun x => HingeNbr (wordFaceKey w τ) o x).card ≤ 2 := by
  classical
  let A := (Finset.univ.filter fun j => childV w j = o).image (parV w)
  let B := (Finset.univ.filter fun j => j.succ ∈ w.2.1 ∧ parV w j = o).image (childV w)
  have hA : A.card ≤ 1 := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_le_one]
    intro j hj j' hj'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
    exact childV_injective w (hj.trans hj'.symm)
  have hB : B.card ≤ 1 := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_le_one]
    intro j hj j' hj'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
    exact spine_child_unique w hj.1 hj'.1 (hj.2.trans hj'.2.symm)
  have hsub : (spineV w).filter (fun x => HingeNbr (wordFaceKey w τ) o x) ⊆ A ∪ B := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxs, hn⟩ := hx
    obtain ⟨j, -, hj⟩ := hingeNbr_wordFaceKey w τ hn
    rcases hj with ⟨hp, hc⟩ | ⟨hc, hp⟩
    · apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨j, ?_, hc⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, hp⟩
      unfold spineV at hxs
      obtain ⟨s, hs, hsx⟩ := Finset.mem_image.mp hxs
      have hsj : s = j.succ := baseV_injective w (hsx.trans hc.symm)
      rw [hsj] at hs
      rcases Finset.mem_insert.mp hs with h0 | h
      · exact absurd h0 (Fin.succ_ne_zero j)
      · exact h
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨j, ?_, hp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hc
  calc ((spineV w).filter fun x => HingeNbr (wordFaceKey w τ) o x).card
      ≤ (A ∪ B).card := Finset.card_le_of_subset hsub
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ ≤ 2 := by omega

/-! ## The tree shape -/

/-- Parents are spine labels. -/
theorem parV_mem_spineV (w : WordIndex r) (j : Fin r) : parV w j ∈ spineV w :=
  Finset.mem_image.mpr ⟨_, parent_mem_insert w.2.1 j.succ, rfl⟩

/-- The last spine label is a spine label. -/
theorem lastV_mem_spineV (w : WordIndex r) : lastV w ∈ spineV w :=
  Finset.mem_image.mpr ⟨_, Finset.max'_mem (insert 0 w.2.1) (Finset.insert_nonempty _ _), rfl⟩

/-- The apex is not a vertex of the tree. -/
theorem apexV_not_mem_spineV (w : WordIndex r) : apexV w ∉ spineV w := by
  intro h
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
  exact apexV_ne_baseV w i hi.symm

/-- A pendant label (non-spine child) is the parent of no edge. -/
theorem parV_ne_pendant (w : WordIndex r) {j : Fin r} (hj : j.succ ∉ w.2.1) (j' : Fin r) :
    parV w j' ≠ childV w j := fun he =>
  parent_ne_pendant w.2.1 j hj j'.succ (baseV_injective w he)

/-- Pendant labels are exactly the non-spine labels other than the apex. -/
theorem childV_not_mem_spineV (w : WordIndex r) {j : Fin r} (hj : j.succ ∉ w.2.1) :
    childV w j ∉ spineV w := by
  intro h
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
  have hij := baseV_injective w he
  rw [hij] at hi
  rcases Finset.mem_insert.mp hi with h0 | h0
  · exact Fin.succ_ne_zero j h0
  · exact hj h0

/-- Any label other than the last spine label without active children (in
particular every tree leaf other than `last`, and the apex) has `κ ∈ {0, -1}`. -/
theorem kappa_mem_of_no_active_child (w : WordIndex r) (τ : wordLabels w → Fin 3)
    (o : Fin (r + 1 + 1)) (hno : ∀ j, edgeState w τ j ≠ 0 → parV w j ≠ o)
    (hlast : lastV w ≠ o) :
    kappa (wordFaceKey w τ) o = 0 ∨ kappa (wordFaceKey w τ) o = -1 := by
  classical
  have hz : (Finset.univ.filter fun j => edgeState w τ j ≠ 0 ∧ parV w j = o) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro j - ⟨h1, h2⟩
    exact hno j h1 h2
  have hle := card_linear_child_le_one w τ o
  have hlo := neg_one_le_kappa_wordFaceKey w τ o
  rw [kappa_wordFaceKey, hz, if_neg hlast, Finset.card_empty, Nat.cast_zero] at hlo ⊢
  have hup : (0 : ℝ) - (if apexV w = o then 1 else 0) -
      ((Finset.univ.filter fun j => edgeState w τ j = 1 ∧ childV w j = o).card : ℝ) ≤ 0 := by
    have : (0 : ℝ) ≤ if apexV w = o then 1 else 0 := by split_ifs <;> norm_num
    have : (0 : ℝ) ≤ ((Finset.univ.filter fun j => edgeState w τ j = 1 ∧ childV w j = o).card : ℝ) :=
      Nat.cast_nonneg _
    linarith
  -- the value is an integer in `[-1, 0]`
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h <;>
    simp only [h, Nat.cast_zero, Nat.cast_one] at hlo hup ⊢ <;>
    split_ifs at hlo hup ⊢ <;> norm_num at hlo hup ⊢

/-- Every label of a normalized word face key is `u_i - u_j` for a pair
`(i, j)` of `M` (so `i < j` and the unit is `σ(y_i - y_j)`): the pair set
records all labels. -/
theorem label_wordFaceKey (w : WordIndex r) (τ : wordLabels w → Fin 3)
    {v : Fin (r + 1) → ℝ} (hv : v ∈ (wordFaceKey w τ).2) :
    ∃ p ∈ pairSet (wordFaceKey w τ), v = toR (vtx p.1) - toR (vtx p.2) := by
  classical
  have hv' := hv
  unfold wordFaceKey normalizedKey faceKey at hv'
  simp only [Finset.mem_image, Finset.mem_filter] at hv'
  obtain ⟨u, ⟨hu, hst⟩, rfl⟩ := hv'
  unfold wordLabels at hu
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hu
  refine ⟨(lowV w j, highV w j), ?_, orientedLabel_edge w j⟩
  rw [mem_pairSet, hasPair_wordFaceKey_iff]
  exact ⟨lowV_lt_highV w j, j, hst, rfl, rfl⟩

theorem normalizedKey_label {k : RealKey (r + 1)} (hk : k ∈ normalizedKeys r)
    {v : Fin (r + 1) → ℝ} (hv : v ∈ k.2) :
    ∃ p ∈ pairSet k, v = toR (vtx p.1) - toR (vtx p.2) := by
  obtain ⟨w, τ, rfl⟩ := exists_word_of_mem_normalizedKeys hk
  exact label_wordFaceKey w τ hv

/-! ## Statements for every normalized key -/

/-- Every normalized key has the caterpillar κ formula for some word and face
state. -/
theorem normalizedKey_kappa_formula {k : RealKey (r + 1)} (hk : k ∈ normalizedKeys r) :
    ∃ (w : WordIndex r) (τ : wordLabels w → Fin 3), k = wordFaceKey w τ ∧
      ∀ o, kappa k o =
        ((Finset.univ.filter fun j => edgeState w τ j ≠ 0 ∧ parV w j = o).card : ℝ) +
        (if lastV w = o then 1 else 0) - (if apexV w = o then 1 else 0) -
        ((Finset.univ.filter fun j => edgeState w τ j = 1 ∧ childV w j = o).card : ℝ) := by
  obtain ⟨w, τ, rfl⟩ := exists_word_of_mem_normalizedKeys hk
  exact ⟨w, τ, rfl, kappa_wordFaceKey w τ⟩

theorem normalizedKey_neg_one_le_kappa {k : RealKey (r + 1)} (hk : k ∈ normalizedKeys r)
    (o : Fin (r + 1 + 1)) : -1 ≤ kappa k o := by
  obtain ⟨w, τ, rfl⟩ := exists_word_of_mem_normalizedKeys hk
  exact neg_one_le_kappa_wordFaceKey w τ o

/-- Every normalized key has an apex: `κ = -1` and no pair contains it. -/
theorem normalizedKey_exists_apex {k : RealKey (r + 1)} (hk : k ∈ normalizedKeys r) :
    ∃ a, kappa k a = -1 ∧ ∀ x, ¬ HasPair k a x ∧ ¬ HasPair k x a := by
  obtain ⟨w, τ, rfl⟩ := exists_word_of_mem_normalizedKeys hk
  exact ⟨apexV w, kappa_apex_wordFaceKey w τ, not_hasPair_apex_wordFaceKey w τ⟩

theorem normalizedKey_card_pairSet_le {k : RealKey (r + 1)} (hk : k ∈ normalizedKeys r) :
    (pairSet k).card ≤ r := by
  obtain ⟨w, τ, rfl⟩ := exists_word_of_mem_normalizedKeys hk
  exact card_pairSet_wordFaceKey_le w τ

theorem normalizedKey_sum_kappa {k : RealKey (r + 1)} (_hk : k ∈ normalizedKeys r) :
    ∑ o, kappa k o = (pairSet k).card :=
  sum_kappa k

end MaxCaterpillar.CountCubic
