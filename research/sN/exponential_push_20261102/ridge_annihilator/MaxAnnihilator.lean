import research.sN.exponential_push_20261102.ridge_annihilator.MaxTent
import research.sN.exponential_push_20261102.ridge_annihilator.DifferenceAlgebra

/-! The explicit maximum tent commutes with every translation difference. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.Ridge
open BigOperators Frontier.StarCertificate

variable {N : ℕ} [NeZero N]

theorem iterDiff_maxCoordinateDifference (vs : List (Point N)) :
    iterDiff vs maxCoordinateDifference = fun x =>
      anchoredDifference Finset.univ
        (fun T => iterDiff vs (Maximum N) (shiftCoordinates T x)) := by
  have he : maxCoordinateDifference = fun x : Point N =>
      ∑ T in (Finset.univ : Finset (Fin N)).powerset,
        (-1 : ℝ) ^ ((Finset.univ : Finset (Fin N)) \ T).card *
          Maximum N (x + shiftCoordinates T 0) := by
    funext x
    unfold maxCoordinateDifference anchoredDifference
    apply Finset.sum_congr rfl
    intro T _
    dsimp only
    rw [shiftCoordinates_eq_add T x]
  rw [he,iterDiff_weighted_translate]
  funext x
  unfold anchoredDifference
  apply Finset.sum_congr rfl
  intro T _
  dsimp only
  rw [shiftCoordinates_eq_add T x]

theorem iterDiff_maxCoordinateDifference_eq_zero_of_maximum (vs : List (Point N))
    (h : iterDiff vs (Maximum N) = 0) :
    iterDiff vs maxCoordinateDifference = 0 := by
  rw [iterDiff_maxCoordinateDifference,h]
  funext x
  simp [anchoredDifference]

theorem iterDiff_maxCoordinateDifference_eq_zero (vs : List (Point N))
    (h : iterDiff vs (Maximum N) = 0) :
    iterDiff vs maxCoordinateDifference = 0 :=
  iterDiff_maxCoordinateDifference_eq_zero_of_maximum vs h

#print axioms iterDiff_maxCoordinateDifference
#print axioms iterDiff_maxCoordinateDifference_eq_zero_of_maximum
#print axioms iterDiff_maxCoordinateDifference_eq_zero
end MaxCaterpillar.ExponentialPush.Ridge
