import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.FiniteDimensional

/-!
# Chain simplices: the vertices `g, g + u₀, g + u₀ + u₁, …`

Helper for `Geom/Kuhn.lean` (namespace `MaxNN.ParamidGeom.Kuhn`).  For `g ∈ V` and
`u : Fin n → V`, `chainPt g u r = g + ∑_{p < r} u p` (`r = 0, …, n`) are the vertices of a
monotone lattice path.

* `chain_mem_convexHull`: if `1 ≥ c₀ ≥ c₁ ≥ … ≥ c_{n−1} ≥ 0` then
  `g + ∑ c_p u_p ∈ conv {chainPt g u r}` (induction on `n`: peel off the first step).
* `cone_chain_mem_convexHull`: if moreover `s ∈ [0, 1]` and `c_p ≤ s`, then
  `s g + ∑ c_p u_p ∈ conv ({0} ∪ {chainPt g u r})` (scale the previous statement).
* `linearIndependent_of_span`, `chainPt_succ_sub_castSucc`: the chain points are linearly
  independent as soon as a linearly independent family of the same size lies in their span.
* `affineIndependent_cons_zero`: prepending `0` to a linearly independent family gives an
  affinely independent family.
-/

namespace MaxNN.ParamidGeom.Kuhn

open BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The vertex `g + ∑_{p < r} u p` of the monotone path with start `g` and steps `u`. -/
def chainPt {n : ℕ} (g : V) (u : Fin n → V) (r : Fin (n + 1)) : V :=
  g + ∑ p : Fin n, if (p : ℕ) < (r : ℕ) then u p else 0

theorem chainPt_zero {n : ℕ} (g : V) (u : Fin n → V) : chainPt g u 0 = g := by
  simp [chainPt]

theorem chainPt_succ {n : ℕ} (g : V) (u : Fin (n + 1) → V) (r : Fin (n + 1)) :
    chainPt g u r.succ = chainPt (g + u 0) (fun p => u p.succ) r := by
  simp [chainPt, Fin.sum_univ_succ, add_assoc]

theorem chainPt_succ_sub_castSucc {n : ℕ} (g : V) (u : Fin n → V) (p : Fin n) :
    chainPt g u p.succ - chainPt g u (Fin.castSucc p) = u p := by
  simp only [chainPt, Fin.val_succ, Fin.coe_castSucc]
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.sum_eq_single p]
  · simp
  · intro q _ hqp
    have hiff : ((q : ℕ) < (p : ℕ) + 1 ↔ (q : ℕ) < (p : ℕ)) := by
      constructor
      · intro h
        exact lt_of_le_of_ne (Nat.lt_succ_iff.mp h) (fun e => hqp (Fin.ext e))
      · intro h
        exact Nat.lt_succ_of_lt h
    by_cases h : (q : ℕ) < (p : ℕ)
    · rw [if_pos (hiff.mpr h), if_pos h, sub_self]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, sub_self]
  · intro h
    exact absurd (Finset.mem_univ p) h

/-- **A monotone combination of the steps lies in the chain simplex.** -/
theorem chain_mem_convexHull :
    ∀ (n : ℕ) (g : V) (u : Fin n → V) (c : Fin n → ℝ), (∀ p, 0 ≤ c p) → (∀ p, c p ≤ 1) →
      (∀ p q, p ≤ q → c q ≤ c p) →
      g + ∑ p, c p • u p ∈ convexHull ℝ (Set.range (chainPt g u))
  | 0, g, u, c, _, _, _ => by
      rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      exact subset_convexHull ℝ _ ⟨0, chainPt_zero g u⟩
  | n + 1, g, u, c, h0, h1, hanti => by
      by_cases hc : c 0 = 0
      · have hall : ∀ p, c p = 0 := fun p =>
          le_antisymm ((hanti 0 p (Fin.zero_le p)).trans hc.le) (h0 p)
        have e : g + ∑ p, c p • u p = g := by simp [hall]
        rw [e]
        exact subset_convexHull ℝ _ ⟨0, chainPt_zero g u⟩
      · have hcpos : 0 < c 0 := lt_of_le_of_ne (h0 0) (Ne.symm hc)
        let d : Fin n → ℝ := fun p => c p.succ / c 0
        have hd0 : ∀ p, 0 ≤ d p := fun p => div_nonneg (h0 _) hcpos.le
        have hd1 : ∀ p, d p ≤ 1 := fun p =>
          (div_le_one hcpos).mpr (hanti 0 p.succ (Fin.zero_le _))
        have hdanti : ∀ p q, p ≤ q → d q ≤ d p := fun p q hpq =>
          div_le_div_of_le hcpos.le (hanti _ _ (Fin.succ_le_succ_iff.mpr hpq))
        have IH := chain_mem_convexHull n (g + u 0) (fun p => u p.succ) d hd0 hd1 hdanti
        have hsub : Set.range (chainPt (g + u 0) (fun p => u p.succ)) ⊆
            Set.range (chainPt g u) := by
          rintro _ ⟨r, rfl⟩
          exact ⟨r.succ, chainPt_succ g u r⟩
        have hy := convexHull_mono hsub IH
        have hg : g ∈ convexHull ℝ (Set.range (chainPt g u)) :=
          subset_convexHull ℝ _ ⟨0, chainPt_zero g u⟩
        have hd : ∀ p : Fin n, c 0 • (d p • u p.succ) = c p.succ • u p.succ := fun p => by
          rw [smul_smul]
          show (c 0 * (c p.succ / c 0)) • u p.succ = c p.succ • u p.succ
          rw [mul_div_cancel' _ hc]
        have key : g + ∑ p, c p • u p =
            (1 - c 0) • g + c 0 • (g + u 0 + ∑ p, d p • u p.succ) := by
          rw [Fin.sum_univ_succ, smul_add, smul_add, Finset.smul_sum]
          simp only [hd]
          rw [sub_smul, one_smul]
          abel
        rw [key]
        exact convex_convexHull ℝ _ hg hy (sub_nonneg.mpr (h1 0)) hcpos.le (by ring)

/-- **The cone version**: `s g + ∑ c_p u_p ∈ conv ({0} ∪ chain)` for `0 ≤ c_p ≤ s ≤ 1` with `c`
antitone. -/
theorem cone_chain_mem_convexHull {n : ℕ} (g : V) (u : Fin n → V) (s : ℝ) (c : Fin n → ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (h0 : ∀ p, 0 ≤ c p) (hcs : ∀ p, c p ≤ s)
    (hanti : ∀ p q, p ≤ q → c q ≤ c p) :
    s • g + ∑ p, c p • u p ∈ convexHull ℝ (insert 0 (Set.range (chainPt g u))) := by
  by_cases hs : s = 0
  · have hall : ∀ p, c p = 0 := fun p => le_antisymm ((hcs p).trans hs.le) (h0 p)
    have e : s • g + ∑ p, c p • u p = 0 := by simp [hall, hs]
    rw [e]
    exact subset_convexHull ℝ _ (Set.mem_insert 0 _)
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hin := chain_mem_convexHull n g u (fun p => c p / s)
      (fun p => div_nonneg (h0 p) hspos.le) (fun p => (div_le_one hspos).mpr (hcs p))
      (fun p q hpq => div_le_div_of_le hspos.le (hanti p q hpq))
    have hy := convexHull_mono (Set.subset_insert 0 _) hin
    have h0m : (0 : V) ∈ convexHull ℝ (insert 0 (Set.range (chainPt g u))) :=
      subset_convexHull ℝ _ (Set.mem_insert 0 _)
    have key : s • g + ∑ p, c p • u p =
        (1 - s) • (0 : V) + s • (g + ∑ p, (c p / s) • u p) := by
      rw [smul_zero, zero_add, smul_add, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [smul_smul, mul_div_cancel' _ hs]
    rw [key]
    exact convex_convexHull ℝ _ h0m hy (sub_nonneg.mpr hs1) hspos.le (by ring)

/-- A family `w` of `n + 1` vectors whose span contains a linearly independent family of
`n + 1` vectors is linearly independent. -/
theorem linearIndependent_of_span [FiniteDimensional ℝ V] {n : ℕ} (w B : Fin (n + 1) → V)
    (hB : LinearIndependent ℝ B) (hsub : ∀ j, B j ∈ Submodule.span ℝ (Set.range w)) :
    LinearIndependent ℝ w := by
  have hle : Submodule.span ℝ (Set.range B) ≤ Submodule.span ℝ (Set.range w) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hsub j
  have h1 : Fintype.card (Fin (n + 1)) = (Set.range B).finrank ℝ :=
    linearIndependent_iff_card_eq_finrank_span.mp hB
  have h2 : FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range B)) ≤
      FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range w)) :=
    Submodule.finrank_mono hle
  have h3 : (Set.range w).finrank ℝ ≤ Fintype.card (Fin (n + 1)) := finrank_range_le_card
  refine linearIndependent_iff_card_eq_finrank_span.mpr (le_antisymm ?_ h3)
  exact (le_of_eq h1).trans h2

/-- Prepending the origin to a linearly independent family gives an affinely independent
family. -/
theorem affineIndependent_cons_zero {n : ℕ} (w : Fin n → V) (hw : LinearIndependent ℝ w) :
    AffineIndependent ℝ (Fin.cons 0 w : Fin (n + 1) → V) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin (n + 1))]
  let e : Fin n ≃ {x : Fin (n + 1) // x ≠ 0} :=
    { toFun := fun r => ⟨r.succ, Fin.succ_ne_zero r⟩
      invFun := fun x => x.1.pred x.2
      left_inv := fun r => by simp
      right_inv := fun x => by simp }
  refine (linearIndependent_equiv' e ?_).mp hw
  funext r
  simp

end MaxNN.ParamidGeom.Kuhn
