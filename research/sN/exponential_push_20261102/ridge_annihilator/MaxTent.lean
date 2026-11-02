import MaxCaterpillar.Frontier.Basic
import MaxCaterpillar.Frontier.StarCertificate.Anova

/-! An exact finite coordinate difference of the maximum is a compact tent
modulo the common diagonal. Research leaf; no regularity assumptions. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.Ridge
open BigOperators Frontier Frontier.StarCertificate

variable {N : ℕ} [NeZero N]

/-- Add one in precisely the selected coordinates. -/
def shiftCoordinates (T : Finset (Fin N)) (x : Point N) : Point N :=
  fun i => x i + if i ∈ T then 1 else 0

@[simp] lemma shiftCoordinates_empty (x : Point N) : shiftCoordinates ∅ x = x := by
  funext i
  simp [shiftCoordinates]

lemma shiftCoordinates_eq_add (T : Finset (Fin N)) (x : Point N) :
    shiftCoordinates T x = x + shiftCoordinates T 0 := by
  funext i
  simp [shiftCoordinates]

/-- The mixed difference in all the coordinate directions. -/
def maxCoordinateDifference (x : Point N) : ℝ :=
  anchoredDifference Finset.univ (fun T => Maximum N (shiftCoordinates T x))

lemma maximum_shift_mono (S T : Finset (Fin N)) (hST : S ⊆ T) (x : Point N) :
    Maximum N (shiftCoordinates S x) ≤ Maximum N (shiftCoordinates T x) := by
  apply (Maximum_le_iff _ _).mpr
  intro i
  have hi := le_Maximum (shiftCoordinates T x) i
  by_cases his : i ∈ S
  · have hit := hST his
    simpa [shiftCoordinates,his,hit] using hi
  · by_cases hit : i ∈ T
    · simp only [shiftCoordinates,his,hit,if_false,if_true,add_zero] at *
      linarith
    · simpa [shiftCoordinates,his,hit] using hi

lemma maximum_shift_insert_min (x : Point N) (k : Fin N)
    (hk : ∀ i, x k ≤ x i) (T : Finset (Fin N)) (hT : T.Nonempty) :
    Maximum N (shiftCoordinates (insert k T) x) =
      Maximum N (shiftCoordinates T x) := by
  apply le_antisymm
  · apply (Maximum_le_iff _ _).mpr
    intro i
    by_cases hik : i = k
    · subst i
      obtain ⟨j,hj⟩ := hT
      have hjm := le_Maximum (shiftCoordinates T x) j
      have hkj := hk j
      simp only [shiftCoordinates,Finset.mem_insert_self,if_true] 
      simp only [shiftCoordinates,hj,if_true] at hjm
      linarith
    · simpa [shiftCoordinates,Finset.mem_insert,hik] using
        le_Maximum (shiftCoordinates T x) i
  · exact maximum_shift_mono T (insert k T) (Finset.subset_insert _ _) x

lemma maximum_shift_singleton (x : Point N) (k : Fin N) :
    Maximum N (shiftCoordinates {k} x) = max (Maximum N x) (x k + 1) := by
  apply le_antisymm
  · apply (Maximum_le_iff _ _).mpr
    intro i
    by_cases hik : i = k
    · subst i
      simpa [shiftCoordinates] using le_max_right (Maximum N x) (x k + 1)
    · simp only [shiftCoordinates,Finset.mem_singleton,hik,if_false,add_zero]
      exact (le_Maximum x i).trans (le_max_left _ _)
  · apply max_le
    · simpa only [shiftCoordinates_empty] using
        maximum_shift_mono ∅ {k} (Finset.empty_subset _) x
    · simpa [shiftCoordinates] using le_Maximum (shiftCoordinates {k} x) k

theorem maxCoordinateDifference_at_min (x : Point N) (k : Fin N)
    (hk : ∀ i, x k ≤ x i) :
    maxCoordinateDifference x =
      (-1 : ℝ) ^ (N - 1) * max 0 (1 + x k - Maximum N x) := by
  unfold maxCoordinateDifference
  rw [← Finset.insert_erase (Finset.mem_univ k)]
  rw [anchoredDifference_insert _ k (Finset.not_mem_erase k Finset.univ)]
  unfold anchoredDifference
  rw [Finset.sum_eq_single ∅]
  · dsimp only
    simp only [Finset.sdiff_empty,Finset.card_erase_of_mem (Finset.mem_univ k),
      Finset.card_univ,Fintype.card_fin]
    have hins : insert k (∅ : Finset (Fin N)) = {k} := by ext i; simp
    rw [hins,maximum_shift_singleton]
    have he : shiftCoordinates (∅ : Finset (Fin N)) x = x := by
      funext i
      simp [shiftCoordinates]
    rw [he]
    congr 1
    rcases le_total (Maximum N x) (x k + 1) with h | h
    · rw [max_eq_right h,max_eq_right (by linarith)]
      ring
    · rw [max_eq_left h,sub_self,max_eq_left (by linarith)]
  · intro T _ hT
    have hne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
    dsimp only
    rw [maximum_shift_insert_min x k hk T hne,sub_self,mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_powerset.mpr (Finset.empty_subset _)))

/-- The exact all-input identity. The range of `x` is `Maximum x + Maximum (-x)`. -/
theorem maxCoordinateDifference_eq_tent (x : Point N) :
    maxCoordinateDifference x =
      (-1 : ℝ) ^ (N - 1) * max 0 (1 - Maximum N x - Maximum N (-x)) := by
  obtain ⟨k,hk⟩ := exists_eq_Maximum (-x)
  have hkmin : ∀ i, x k ≤ x i := by
    intro i
    have hi := le_Maximum (-x) i
    rw [hk] at hi
    simp only [Pi.neg_apply] at hi
    linarith
  rw [maxCoordinateDifference_at_min x k hkmin,hk]
  simp only [Pi.neg_apply]
  congr 2
  ring

theorem maxCoordinateDifference_zero :
    maxCoordinateDifference (0 : Point N) = (-1 : ℝ) ^ (N - 1) := by
  rw [maxCoordinateDifference_eq_tent]
  have hz : Maximum N (0 : Point N) = 0 := by
    apply le_antisymm
    · apply (Maximum_le_iff _ _).mpr
      intro i
      exact le_rfl
    · simpa only [Pi.zero_apply] using le_Maximum (0 : Point N) (0 : Fin N)
  simp [hz]

/-- The mixed difference vanishes once any coordinate contrast exceeds one. -/
theorem maxCoordinateDifference_eq_zero_of_contrast (x : Point N)
    (i j : Fin N) (hij : 1 ≤ x i - x j) :
    maxCoordinateDifference x = 0 := by
  rw [maxCoordinateDifference_eq_tent]
  have hi := le_Maximum x i
  have hj := le_Maximum (-x) j
  simp only [Pi.neg_apply] at hj
  rw [max_eq_left (by linarith),mul_zero]

theorem maxCoordinateDifference_eq_zero_of_abs_contrast (x : Point N)
    (i j : Fin N) (hij : 1 ≤ |x i - x j|) :
    maxCoordinateDifference x = 0 := by
  rcases le_or_gt 0 (x i - x j) with h | h
  · rw [abs_of_nonneg h] at hij
    exact maxCoordinateDifference_eq_zero_of_contrast x i j hij
  · rw [abs_of_neg h] at hij
    exact maxCoordinateDifference_eq_zero_of_contrast x j i (by linarith)

theorem maxCoordinateDifference_ne_zero :
    maxCoordinateDifference (0 : Point N) ≠ 0 := by
  rw [maxCoordinateDifference_zero]
  exact pow_ne_zero _ (by norm_num)

#print axioms maxCoordinateDifference_at_min
#print axioms maxCoordinateDifference_eq_tent
#print axioms maxCoordinateDifference_zero
#print axioms maxCoordinateDifference_eq_zero_of_contrast
#print axioms maxCoordinateDifference_eq_zero_of_abs_contrast
#print axioms maxCoordinateDifference_ne_zero
end MaxCaterpillar.ExponentialPush.Ridge
