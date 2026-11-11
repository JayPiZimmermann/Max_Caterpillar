import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Model
import MaxCaterpillar.Frontier.StarCertificate.MobiusQuadratic

/-! # Actual zero-sum rows of support at most two are signed braid rows

Zero rows are included. The Boolean expansion allows arbitrary signed scale
and records its sole quadratic edge in a directed matrix.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.BraidModel
open BigOperators StarCertificate

structure BraidPair (a : Point 5) where
  left : Fin 5
  right : Fin 5
  distinct : left ≠ right
  scale : ℝ
  row_eq : a = scale • (unitVec left - unitVec right)

theorem exists_braidPair (a : Point 5) (hsum : ∑ i, a i = 0)
    (hcard : (NormalizedNetwork.rowSupport a).card ≤ 2) : Nonempty (BraidPair a) := by
  classical
  by_cases hz : a = 0
  · exact ⟨⟨0, 1, by decide, 0, by simp [hz]⟩⟩
  have hsupport : ∑ i in NormalizedNetwork.rowSupport a, a i = 0 := by
    rw [← hsum]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    exact not_not.mp (by simpa only [NormalizedNetwork.mem_rowSupport] using hi)
  have hnonempty : (NormalizedNetwork.rowSupport a).Nonempty := by
    by_contra he
    apply hz
    funext i
    have hi : i ∉ NormalizedNetwork.rowSupport a := by
      intro hi
      exact he ⟨i, hi⟩
    simpa only [NormalizedNetwork.mem_rowSupport, not_not] using hi
  have htwo : (NormalizedNetwork.rowSupport a).card = 2 := by
    apply Nat.le_antisymm hcard
    by_contra hlt
    have hone : (NormalizedNetwork.rowSupport a).card ≤ 1 := by
      exact Nat.le_of_lt_succ (not_le.mp hlt)
    obtain ⟨i, hi⟩ := hnonempty
    have hs : (∑ j in NormalizedNetwork.rowSupport a, a j) = a i := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        exact False.elim (hji ((Finset.card_le_one.mp hone) j hj i hi))
      · intro hn
        exact False.elim (hn hi)
    rw [hs] at hsupport
    exact ((NormalizedNetwork.mem_rowSupport a i).mp hi) hsupport
  obtain ⟨i, j, hij, heq⟩ := Finset.card_eq_two.mp htwo
  have hop : a i + a j = 0 := by
    rw [heq, Finset.sum_pair hij] at hsupport
    exact hsupport
  refine ⟨⟨i, j, hij, a i, ?_⟩⟩
  funext k
  by_cases hki : k = i
  · subst k
    simp [unitVec, hij]
  · by_cases hkj : k = j
    · subst k
      simp [Pi.smul_apply, unitVec, hij.symm]
      linarith only [hop]
    · have hk : a k = 0 := by
        have hn : k ∉ NormalizedNetwork.rowSupport a := by simp [heq, hki, hkj]
        simpa only [NormalizedNetwork.mem_rowSupport, not_not] using hn
      simp [Pi.smul_apply, unitVec, hki, hkj, hk]

namespace BraidPair
variable {a : Point 5}

theorem lin_eq (p : BraidPair a) (x : Point 5) :
    lin a x = p.scale * (x p.left - x p.right) := by
  calc
    lin a x = lin (p.scale • (unitVec p.left - unitVec p.right)) x :=
      congrArg (fun c : Point 5 => lin c x) p.row_eq
    _ = p.scale * (x p.left - x p.right) := by
      rw [lin_smul_left]
      congr 1
      simp [lin, unitVec, sub_mul, Finset.sum_sub_distrib]

noncomputable def linearCoeff (p : BraidPair a) (i : Fin 5) : ℝ :=
  (if i = p.left then relu p.scale else 0) +
    (if i = p.right then relu (-p.scale) else 0)

noncomputable def quadraticCoeff (p : BraidPair a) (i j : Fin 5) : ℝ :=
  if i = p.left ∧ j = p.right then -|p.scale| else 0

theorem quadraticCoeff_nonzero (p : BraidPair a) (i j : Fin 5)
    (h : p.quadraticCoeff i j ≠ 0) : i = p.left ∧ j = p.right := by
  by_contra hn
  exact h (by simp [quadraticCoeff, hn])

theorem quadraticCoeff_ne_zero_support (p : BraidPair a) (i j : Fin 5)
    (h : p.quadraticCoeff i j ≠ 0) : a i ≠ 0 ∧ a j ≠ 0 := by
  obtain ⟨rfl, rfl⟩ := p.quadraticCoeff_nonzero i j h
  have ht : p.scale ≠ 0 := by
    intro ht
    exact h (by simp [quadraticCoeff, ht])
  have hl := congrArg (fun c : Point 5 => c p.left) p.row_eq
  have hr := congrArg (fun c : Point 5 => c p.right) p.row_eq
  simp [Pi.smul_apply, unitVec, p.distinct, p.distinct.symm] at hl hr
  rw [hl, hr]
  exact ⟨ht, neg_ne_zero.mpr ht⟩

theorem quadraticCoeff_ne_zero_distinct (p : BraidPair a) (i j : Fin 5)
    (h : p.quadraticCoeff i j ≠ 0) : i ≠ j := by
  obtain ⟨rfl, rfl⟩ := p.quadraticCoeff_nonzero i j h
  exact p.distinct

theorem relu_boolean (p : BraidPair a) (B : Finset (Fin 5)) :
    relu (lin a (fun i => booleanCoordinate i B)) =
      booleanQuadratic 0 p.linearCoeff p.quadraticCoeff B := by
  classical
  rw [p.lin_eq]
  have hlin : (∑ i, p.linearCoeff i * booleanCoordinate i B) =
      relu p.scale * booleanCoordinate p.left B +
        relu (-p.scale) * booleanCoordinate p.right B := by
    simp [linearCoeff, add_mul, Finset.sum_add_distrib]
  have hquad : (∑ i, ∑ j, p.quadraticCoeff i j *
        (booleanCoordinate i B * booleanCoordinate j B)) =
      -|p.scale| * (booleanCoordinate p.left B * booleanCoordinate p.right B) := by
    simp [quadraticCoeff, ite_and, ite_mul]
  unfold booleanQuadratic
  rw [hlin, hquad]
  have habs : relu p.scale + relu (-p.scale) = |p.scale| := by
    rcases le_total 0 p.scale with hs | hs
    · rw [relu_of_nonneg hs, relu_of_nonpos (neg_nonpos.mpr hs), abs_of_nonneg hs]
      ring
    · rw [relu_of_nonpos hs, relu_of_nonneg (neg_nonneg.mpr hs), abs_of_nonpos hs]
      ring
  by_cases hl : p.left ∈ B <;> by_cases hr : p.right ∈ B <;>
    simp [booleanCoordinate, hl, hr, habs, relu] at *
  linarith only [habs]

end BraidPair
end MaxCaterpillar.Frontier.RandomRestriction.BraidModel
