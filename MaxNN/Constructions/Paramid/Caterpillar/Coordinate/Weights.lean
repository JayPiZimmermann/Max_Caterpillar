import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Insertion

/-! # Coefficients under coordinate-vertex insertion -/

namespace MaxNN.Caterpillar

variable {s : ℕ}

theorem wordWeight_succ_of_card_eq (S : Finset (Fin (s + 1)))
    (U : Finset (Fin (s + 1 + 1))) (hcard : U.card = S.card) :
    wordWeight (s + 1) U = -((s + 3 : ℝ)⁻¹) * wordWeight s S := by
  unfold wordWeight
  rw [hcard]
  rw [show s + 1 + 1 + 1 = (s + 2) + 1 by omega, Nat.factorial_succ]
  rw [show s + 2 + 1 + S.card = (s + 1 + 1 + S.card) + 1 by omega, pow_succ]
  rw [show s + 1 + 1 = s + 2 by omega]
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [Nat.factorial_ne_zero]
  ring

theorem wordWeight_succ_of_card_eq_add_one (S : Finset (Fin (s + 1)))
    (U : Finset (Fin (s + 1 + 1))) (hcard : U.card = S.card + 1) :
    wordWeight (s + 1) U = ((s + 3 : ℝ)⁻¹) * wordWeight s S := by
  unfold wordWeight
  rw [hcard]
  rw [show s + 1 + 1 + 1 = (s + 2) + 1 by omega, Nat.factorial_succ]
  rw [show s + 2 + 1 + (S.card + 1) = (s + 1 + 1 + S.card) + 2 by omega,
    pow_add, pow_two]
  rw [show s + 1 + 1 = s + 2 by omega]
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [Nat.factorial_ne_zero]
  ring

theorem wordWeight_insertPendantCuts (i : Fin (s + 1)) (S : Finset (Fin (s + 1))) :
    wordWeight (s + 1) (insertPendantCuts i S) =
      -((s + 3 : ℝ)⁻¹) * wordWeight s S :=
  wordWeight_succ_of_card_eq S _ (card_insertPendantCuts i S)

theorem card_lastEndpointCuts (S : Finset (Fin (s + 1))) :
    (joinCuts S (∅ : Finset (Fin 1))).card = S.card + 1 := by
  simpa using card_joinCuts S (∅ : Finset (Fin 1)) (by simp)

theorem wordWeight_lastEndpointCuts (S : Finset (Fin (s + 1))) :
    wordWeight (s + 1) (joinCuts S (∅ : Finset (Fin 1))) =
      ((s + 3 : ℝ)⁻¹) * wordWeight s S :=
  wordWeight_succ_of_card_eq_add_one S _ (card_lastEndpointCuts S)

theorem card_firstEndpointCuts (S : Finset (Fin (s + 1))) (h0 : (0 : Fin (s + 1)) ∉ S) :
    (joinCuts (∅ : Finset (Fin 1)) S).card = S.card + 1 := by
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    card_joinCuts (∅ : Finset (Fin 1)) S h0

theorem wordWeight_firstEndpointCuts (S : Finset (Fin (s + 1)))
    (h0 : (0 : Fin (s + 1)) ∉ S) :
    wordWeight (1 + s) (joinCuts (∅ : Finset (Fin 1)) S) =
      ((s + 3 : ℝ)⁻¹) * wordWeight s S := by
  unfold wordWeight
  rw [card_firstEndpointCuts S h0]
  rw [show 1 + s + 1 + 1 = (s + 2) + 1 by omega, Nat.factorial_succ]
  rw [show s + 2 + 1 + (S.card + 1) = (s + 1 + 1 + S.card) + 2 by omega,
    pow_add, pow_two]
  rw [show s + 1 + 1 = s + 2 by omega]
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [Nat.factorial_ne_zero]
  ring

end MaxNN.Caterpillar
