import MaxNN.Constructions.Paramid.Caterpillar.Words.RootStar
import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Structured
import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.LinearCombination
import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.FibreSplit
import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.EndpointCanonical
import MaxNN.Constructions.Paramid.Caterpillar.Block.Pairing
import MaxNN.Constructions.Paramid.Geom.Doubling

/-! # The empty-cut star sum

The empty-cut terms missing from the lower caterpillar formula form a lower-dimensional
support-function combination.  The proof first isolates a generic rooted star by the Boolean
alternating identity, then averages over swaps of the apex position while keeping the root fixed.
-/

open BigOperators

namespace MaxNN.Caterpillar

open ParamidGeom

variable {m q s : ℕ}

/-- The cone attached to a subset of a finite vector family. -/
noncomputable def rootStarTerm (D : Fin q → Fin m → ℝ) (S : Finset (Fin q)) :
    (Fin m → ℝ) → ℝ :=
  fun y => relu ((∑ i in S, dot (D i) y) +
    ∑ i in (Finset.univ : Finset (Fin q)) \ S, relu (dot (D i) y))

theorem rootStarTerm_eq_paramidOn (D : Fin q → Fin m → ℝ)
    (hD : Function.Injective D) (S : Finset (Fin q)) :
    rootStarTerm D S = paramidOn (∑ i in S, D i)
      (((Finset.univ : Finset (Fin q)) \ S).image D) := by
  funext y
  unfold rootStarTerm paramidOn
  rw [ParamidGeom.DoublingAux.dot_sum_left]
  rw [Finset.sum_image (fun a _ b _ hab => hD hab)]

/-- Terms indexed by subsets of size at least two already have at most `q-1` frame vectors. -/
theorem rootStarTerm_mem_LSpan_of_two_le_card (D : Fin q → Fin m → ℝ)
    (hD : Function.Injective D) (S : Finset (Fin q)) (hS : S ⊆ Finset.univ)
    (hcard : 2 ≤ S.card) : rootStarTerm D S ∈ LSpan m (q - 1) := by
  rw [rootStarTerm_eq_paramidOn D hD S]
  have hm := paramidOn_mem_LSpan (∑ i in S, D i)
    (((Finset.univ : Finset (Fin q)) \ S).image D)
  have hc : (((Finset.univ : Finset (Fin q)) \ S).image D).card + 1 ≤ q - 1 := by
    have hle : S.card ≤ q := by
      simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_of_subset hS
    have hq : 2 ≤ q := hcard.trans hle
    rw [Finset.card_image_of_injective _ hD, Finset.card_sdiff hS,
      Finset.card_univ, Fintype.card_fin]
    calc
      q - S.card + 1 ≤ (q - 2) + 1 :=
        Nat.add_le_add_right (Nat.sub_le_sub_left hcard q) 1
      _ = q - 1 := by omega
  exact DoublingAux.LSpan_mono hc hm

/-- The empty subset is a zonotope support function, hence belongs to `LSpan 1`. -/
theorem rootStarTerm_empty_mem_LSpan (D : Fin q → Fin m → ℝ)
    (hD : Function.Injective D) : rootStarTerm D ∅ ∈ LSpan m 1 := by
  rw [rootStarTerm_eq_paramidOn D hD ∅]
  simp only [Finset.sum_empty, Finset.sdiff_empty]
  have he : paramidOn (0 : Fin m → ℝ) (Finset.univ.image D) =
      fun y => ∑ v in Finset.univ.image D, relu (dot v y) := by
    funext y
    unfold paramidOn
    simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
    rw [relu_of_nonneg (Finset.sum_nonneg fun _ _ => relu_nonneg _)]
  rw [he]
  have hz := hS_powerset_image_add_sum_mem_LSpan (0 : Fin m → ℝ)
    (Finset.univ.image D)
  rw [hS_powerset_image_add_sum] at hz
  simpa only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] using hz

private def largeSubsets (q : ℕ) : Finset (Finset (Fin q)) :=
  (Finset.univ : Finset (Finset (Fin q))).filter fun S => 2 ≤ S.card

private def singletonSubsets (q : ℕ) : Finset (Finset (Fin q)) :=
  (Finset.univ : Finset (Finset (Fin q))).filter fun S => S.card = 1

private theorem powerset_partition (q : ℕ) :
    (Finset.univ : Finset (Fin q)).powerset =
      insert ∅ (singletonSubsets q ∪ largeSubsets q) := by
  ext S
  simp only [Finset.mem_powerset, Finset.subset_univ, Finset.mem_insert,
    Finset.mem_union, singletonSubsets, largeSubsets, Finset.mem_filter,
    Finset.mem_univ, true_and, true_iff]
  by_cases h0 : S = ∅
  · exact Or.inl h0
  · right
    have hc : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
    by_cases h1 : S.card = 1
    · exact Or.inl h1
    · exact Or.inr (by omega)

private theorem singletonSubsets_eq_image (q : ℕ) :
    singletonSubsets q =
      (Finset.univ : Finset (Fin q)).image (fun i => ({i} : Finset (Fin q))) := by
  ext S
  simp only [singletonSubsets, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · intro hS
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hS
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact Finset.card_singleton i

/-- Inclusion-exclusion expresses the sum of all singleton root-star cones using only an
empty-set zonotope term and cones with at most `q-1` frame vectors. -/
theorem rootStar_singleton_sum_mem_LSpan (hq : 2 ≤ q) (D : Fin q → Fin m → ℝ)
    (hD : Function.Injective D) :
    (∑ i : Fin q, rootStarTerm D {i}) ∈ LSpan m (q - 1) := by
  have hempty : rootStarTerm D ∅ ∈ LSpan m (q - 1) :=
    DoublingAux.LSpan_mono (by omega) (rootStarTerm_empty_mem_LSpan D hD)
  have hlarge :
      (∑ S in largeSubsets q, (-1 : ℝ) ^ S.card • rootStarTerm D S) ∈
        LSpan m (q - 1) := by
    apply Submodule.sum_mem
    intro S hS
    apply Submodule.smul_mem
    apply rootStarTerm_mem_LSpan_of_two_le_card D hD S (Finset.subset_univ S)
    simpa only [largeSubsets, Finset.mem_filter, Finset.mem_univ, true_and] using hS
  have hfun :
      (∑ i : Fin q, rootStarTerm D {i}) = rootStarTerm D ∅ +
        ∑ S in largeSubsets q, (-1 : ℝ) ^ S.card • rootStarTerm D S := by
    funext y
    have hdisj : Disjoint (singletonSubsets q) (largeSubsets q) := by
      rw [Finset.disjoint_left]
      intro S hs hl
      simp only [singletonSubsets, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      simp only [largeSubsets, Finset.mem_filter, Finset.mem_univ, true_and] at hl
      omega
    have hnot : ∅ ∉ singletonSubsets q ∪ largeSubsets q := by
      simp only [Finset.mem_union, singletonSubsets, largeSubsets, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.not_mem_empty, false_or, not_or,
        Finset.card_empty]
      omega
    have hsingle :
        (∑ S in singletonSubsets q,
          (-1 : ℝ) ^ S.card * rootStarTerm D S y) =
          -(∑ i : Fin q, rootStarTerm D {i} y) := by
      rw [singletonSubsets_eq_image q, Finset.sum_image]
      · simp only [Finset.card_singleton, pow_one, neg_one_mul,
          Finset.sum_neg_distrib]
      · intro a _ha b _hb hab
        exact Finset.singleton_injective hab
    have halt := rootStar_alternating_sum (fun i => dot (D i) y)
    change (∑ S in (Finset.univ : Finset (Fin q)).powerset,
      (-1 : ℝ) ^ S.card * rootStarTerm D S y) = 0 at halt
    rw [powerset_partition q, Finset.sum_insert hnot, Finset.sum_union hdisj,
      hsingle] at halt
    simp only [Finset.card_empty, pow_zero, one_mul] at halt
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  rw [hfun]
  exact Submodule.add_mem _ hempty hlarge

private def starPosition (p : Fin (s + 1)) : Fin (s + 2) :=
  (1 : Fin (s + 2)).succAbove p

@[simp] private theorem starPosition_zero :
    starPosition (s := s) 0 = 0 := by
  simp [starPosition]

private theorem starPosition_ne_one (p : Fin (s + 1)) :
    starPosition p ≠ (1 : Fin (s + 2)) :=
  Fin.succAbove_ne _ _

private theorem starPosition_injective :
    Function.Injective (starPosition (s := s)) :=
  Fin.succAbove_right_injective

private def starSwap (p : Fin (s + 1)) : Equiv.Perm (Fin (s + 2)) :=
  Equiv.swap 0 (starPosition p)

private def starSwapWord (p : Fin (s + 1)) (π : Equiv.Perm (Fin (s + 2))) :
    Equiv.Perm (Fin (s + 2)) :=
  (starSwap p).trans π

@[simp] private theorem starSwap_apply_one (p : Fin (s + 1)) :
    starSwap p (1 : Fin (s + 2)) = 1 := by
  apply Equiv.swap_apply_of_ne_of_ne
  · simp
  · exact Ne.symm (starPosition_ne_one p)

private theorem starSwap_starPosition (p q : Fin (s + 1)) :
    starSwap p (starPosition q) = starPosition ((Equiv.swap 0 p) q) := by
  by_cases hq0 : q = 0
  · subst q
    simp only [starSwap, starPosition_zero, Equiv.swap_apply_left]
  · by_cases hqp : q = p
    · subst q
      simp only [starSwap, Equiv.swap_apply_right, starPosition_zero]
    · rw [starSwap, Equiv.swap_apply_of_ne_of_ne]
      · rw [Equiv.swap_apply_of_ne_of_ne hq0 hqp]
      · exact fun h => hq0 (starPosition_injective h)
      · exact fun h => hqp (starPosition_injective h)

private def rootDifference (π : Equiv.Perm (Fin (s + 2))) (p : Fin (s + 1)) :
    Fin (s + 2) → ℝ :=
  coordinateVertex (π 1) - coordinateVertex (π (starPosition p))

private theorem coordinateVertex_injective :
    Function.Injective (@coordinateVertex s) := by
  intro a b hab
  by_contra hne
  have h := congrFun hab a
  simpa [coordinateVertex, Pi.single_apply, hne] using h

private theorem rootDifference_injective (π : Equiv.Perm (Fin (s + 2))) :
    Function.Injective (rootDifference π) := by
  intro p q hpq
  unfold rootDifference at hpq
  apply starPosition_injective
  apply π.injective
  apply coordinateVertex_injective
  exact sub_right_injective hpq

@[simp] private theorem starPosition_succ (j : Fin s) :
    starPosition j.succ = j.succ.succ := by
  rfl

private theorem sum_starSwap_succ (p : Fin (s + 1)) (f : Fin (s + 1) → ℝ) :
    (∑ j : Fin s, f ((Equiv.swap 0 p) j.succ)) =
      ∑ q in (Finset.univ : Finset (Fin (s + 1))) \ {p}, f q := by
  apply Finset.sum_bij (fun j _ => (Equiv.swap 0 p) j.succ)
  · intro j _hj
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton]
    intro h
    have he := (Equiv.swap 0 p).injective
      (h.trans (Equiv.swap_apply_left 0 p).symm)
    exact Fin.succ_ne_zero j he
  · intro j _hj
    rfl
  · intro a b _ha _hb h
    exact Fin.succ_injective _ ((Equiv.swap 0 p).injective h)
  · intro q hq
    have hqp : q ≠ p := by
      simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_singleton] using hq
    have hz : (Equiv.swap 0 p) q ≠ 0 := by
      intro h
      have hh := congrArg (Equiv.swap 0 p) h
      rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at hh
      exact hqp hh
    let j : Fin s := Fin.pred ((Equiv.swap 0 p) q) hz
    refine ⟨j, Finset.mem_univ j, ?_⟩
    dsimp only [j]
    rw [Fin.succ_pred, Equiv.swap_apply_self]

private theorem lastHead_empty :
    lastHead (∅ : Finset (Fin (s + 1))) = 0 := by
  unfold lastHead
  simp

private theorem parent_empty (j : Fin (s + 1)) :
    parent (∅ : Finset (Fin (s + 1))) j = 0 := by
  unfold parent
  simp

private theorem emptyGamma_eq (π : Equiv.Perm (Fin (s + 2))) (p : Fin (s + 1)) :
    coordinateA (starSwapWord p π) (lastHead (∅ : Finset (Fin (s + 1)))) -
      coordinateVertex ((starSwapWord p π) 0) = rootDifference π p := by
  rw [lastHead_empty]
  unfold coordinateA starSwapWord rootDifference
  simp only [Equiv.trans_apply, Fin.succ_zero_eq_one, starSwap_apply_one]
  rw [show starSwap p 0 = starPosition p by
    exact Equiv.swap_apply_left 0 (starPosition p)]

private theorem emptyEdgeVec_eq (π : Equiv.Perm (Fin (s + 2))) (p : Fin (s + 1))
    (j : Fin s) :
    edgeVecs (coordinateA (starSwapWord p π)) ∅ j =
      rootDifference π ((Equiv.swap 0 p) j.succ) := by
  unfold edgeVecs coordinateA starSwapWord rootDifference
  rw [parent_empty]
  simp only [Equiv.trans_apply, Fin.succ_zero_eq_one, starSwap_apply_one]
  rw [← starPosition_succ j, starSwap_starPosition]

private theorem starSwapWord_empty_unit (π : Equiv.Perm (Fin (s + 2)))
    (p : Fin (s + 1)) :
    coordinateLowerUnit (starSwapWord p π) ∅ =
      dot (coordinateVertex (π (starPosition p))) + rootStarTerm (rootDifference π) {p} := by
  change caterpillarUnit (coordinateVertex ((starSwapWord p π) 0))
      (coordinateA (starSwapWord p π)) ∅ = _
  rw [caterpillarUnit_eq_dot_add_paramidUnit]
  rw [emptyGamma_eq]
  have hedge : edgeVecs (coordinateA (starSwapWord p π)) ∅ =
      fun j => rootDifference π ((Equiv.swap 0 p) j.succ) := by
    funext j
    exact emptyEdgeVec_eq π p j
  rw [hedge]
  unfold starSwapWord
  simp only [Equiv.trans_apply, starSwap, Equiv.swap_apply_left]
  funext y
  unfold paramidUnit rootStarTerm
  simp only [Pi.add_apply]
  rw [sum_starSwap_succ (s := s) p
    (fun q => relu (dot (rootDifference π q) y))]
  simp

private def starSwapWords (p : Fin (s + 1)) :
    Equiv.Perm (Fin (s + 2)) ≃ Equiv.Perm (Fin (s + 2)) where
  toFun := starSwapWord p
  invFun := starSwapWord p
  left_inv π := by
    ext i
    simp only [starSwapWord, Equiv.trans_apply, starSwap, Equiv.swap_apply_self]
  right_inv π := by
    ext i
    simp only [starSwapWord, Equiv.trans_apply, starSwap, Equiv.swap_apply_self]

/-- The sum of all empty-cut lower words is lower-dimensional.  The proof averages the
fixed-root star identity over apex swaps; no factorial or coefficient normalization enters. -/
theorem emptyCut_coordinateLowerUnit_sum_mem_LSpan (hs : 1 ≤ s) :
    (∑ π : Equiv.Perm (Fin (s + 2)), coordinateLowerUnit π ∅) ∈ LSpan (s + 2) s := by
  apply sum_mem_of_equiv_average (LSpan (s + 2) s)
    (fun π : Equiv.Perm (Fin (s + 2)) => coordinateLowerUnit π ∅) starSwapWords
  intro π
  have hroot :
      (∑ p : Fin (s + 1), rootStarTerm (rootDifference π) {p}) ∈
        LSpan (s + 2) s := by
    have h := rootStar_singleton_sum_mem_LSpan (m := s + 2)
      (q := s + 1) (by omega) (rootDifference π) (rootDifference_injective π)
    simpa using h
  have hlinear :
      (∑ p : Fin (s + 1), dot (coordinateVertex (π (starPosition p)))) ∈
        LSpan (s + 2) s := by
    apply Submodule.sum_mem
    intro p _hp
    exact DoublingAux.LSpan_mono (Nat.zero_le s)
      (FlagAux.dot_mem_LSpan (coordinateVertex (π (starPosition p))) 0)
  rw [show (∑ p : Fin (s + 1), coordinateLowerUnit (starSwapWords p π) ∅) =
      (∑ p : Fin (s + 1), dot (coordinateVertex (π (starPosition p)))) +
        ∑ p : Fin (s + 1), rootStarTerm (rootDifference π) {p} by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    change coordinateLowerUnit (starSwapWord p π) ∅ = _
    exact starSwapWord_empty_unit π p]
  exact Submodule.add_mem _ hlinear hroot

/-- The two empty-cut endpoint fibres left by the coordinate reindexing belong to the
target lower-dimensional span. -/
theorem coordinateEndpointStarSum_mem_LSpan (hs : 1 ≤ s) :
    coordinateEndpointStarSum s ∈ LSpan (s + 2) s := by
  let c : ℝ := (s + 3 : ℝ)⁻¹ * wordWeight s ∅
  have hfirst (π : Equiv.Perm (Fin (s + 2))) :
      coordinateUpperTerm 1 π (firstInsertCuts (∅ : Finset (Fin (s + 1)))) -
        c • coordinateLowerUnit π ∅ ∈ LSpan (s + 2) 1 := by
    have hg := germDiff_firstEndpoint_sub_lower_mem_LSpan_one
      (coordinateVertex (π 0)) 0 (coordinateA π) ∅ (coordinateOne s)
      (dot_coordinateVertex_one _) dot_zero_coordinateOne
      (fun i => dot_coordinateVertex_one _)
    unfold coordinateUpperTerm
    rw [coordinateUpperUnit_first]
    have hw : wordWeight (s + 1) (firstInsertCuts (∅ : Finset (Fin (s + 1)))) = c := by
      have hc : (firstInsertCuts (∅ : Finset (Fin (s + 1)))).card =
          (∅ : Finset (Fin (s + 1))).card + 1 := by
        simp [firstInsertCuts]
      simpa only [c] using wordWeight_succ_of_card_eq_add_one
        (∅ : Finset (Fin (s + 1))) (firstInsertCuts ∅) hc
    exact smul_sub_smul_mem_of_eq hw hg
  have hlast (π : Equiv.Perm (Fin (s + 2))) :
      coordinateUpperTerm (Fin.last (s + 2)) π
          (joinCuts (s := 0) (∅ : Finset (Fin (s + 1))) (∅ : Finset (Fin 1))) -
        c • coordinateLowerUnit π ∅ ∈ LSpan (s + 2) 1 := by
    have hg := germDiff_lastEndpoint_sub_lower_mem_LSpan_one
      (coordinateVertex (π 0)) (coordinateA π) 0 ∅ (coordinateOne s)
      (dot_coordinateVertex_one _) (fun i => dot_coordinateVertex_one _)
      dot_zero_coordinateOne
    unfold coordinateUpperTerm
    rw [coordinateUpperUnit_last]
    apply smul_sub_smul_mem_of_eq _ hg
    rw [wordWeight_lastEndpointCuts]
  have herr :
      (∑ π : Equiv.Perm (Fin (s + 2)),
        ((coordinateUpperTerm 1 π (firstInsertCuts (∅ : Finset (Fin (s + 1)))) +
          coordinateUpperTerm (Fin.last (s + 2)) π
            (joinCuts (s := 0) (∅ : Finset (Fin (s + 1)))
              (∅ : Finset (Fin 1)))) -
          (2 * c) • coordinateLowerUnit π ∅)) ∈ LSpan (s + 2) 1 := by
    apply Submodule.sum_mem
    intro π _hπ
    have h := Submodule.add_mem (LSpan (s + 2) 1) (hfirst π) (hlast π)
    convert h using 1
    funext y
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have herr' := DoublingAux.LSpan_mono hs herr
  have hstar := Submodule.smul_mem (LSpan (s + 2) s) (2 * c)
    (emptyCut_coordinateLowerUnit_sum_mem_LSpan hs)
  have htotal := Submodule.add_mem (LSpan (s + 2) s) herr' hstar
  unfold coordinateEndpointStarSum
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.smul_sum, sub_add_cancel] using htotal

end MaxNN.Caterpillar
